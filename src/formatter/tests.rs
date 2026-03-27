use crate::ast::*;
use crate::formatter;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::token::Span;

/// Parse source, format at given width, return the formatted string.
fn fmt(source: &str, width: usize) -> String {
    let tokens = Lexer::new(source).lex().unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program_annotated().unwrap();
    formatter::format(&program, width)
}

/// Try to parse and format; returns None if parsing fails.
fn try_fmt(source: &str, width: usize) -> Option<String> {
    let tokens = Lexer::new(source).lex().ok()?;
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program_annotated().ok()?;
    Some(formatter::format(&program, width))
}

/// Parse source and return a normalized AST suitable for structural comparison.
/// Normalization zeroes out all NodeIds, Spans, dangling trivia, and other
/// metadata that is expected to differ between parses of semantically identical code.
fn try_parse_normalized(source: &str) -> Option<Vec<Decl>> {
    let tokens = Lexer::new(source).lex().ok()?;
    let mut parser = Parser::new(tokens);
    let mut decls = parser.parse_program().ok()?;
    normalize_decls(&mut decls);
    Some(decls)
}

// ---------------------------------------------------------------------------
// AST normalization: replace all NodeId, Span, dangling trivia, and layout
// hints with dummy values so structural comparison ignores metadata.
// ---------------------------------------------------------------------------

const S: Span = Span { start: 0, end: 0 };
const NID: NodeId = NodeId(0);

fn normalize_decls(decls: &mut Vec<Decl>) {
    // Sort imports the same way the formatter does (Std.* first, then rest, each sorted)
    // so that import reordering doesn't cause false AST diffs.
    let import_end = decls
        .iter()
        .position(|d| !matches!(d, Decl::Import { .. } | Decl::ModuleDecl { .. }))
        .unwrap_or(decls.len());
    decls[..import_end].sort_by(|a, b| {
        let key = |d: &Decl| match d {
            Decl::ModuleDecl { .. } => (0, String::new()),
            Decl::Import { module_path, .. } => {
                let path = module_path.join(".");
                let is_std = path.starts_with("Std");
                (if is_std { 1 } else { 2 }, path)
            }
            _ => (3, String::new()),
        };
        key(a).cmp(&key(b))
    });
    for d in decls.iter_mut() {
        normalize_decl(d);
    }
}

fn normalize_decl(d: &mut Decl) {
    match d {
        Decl::FunSignature {
            id,
            name_span,
            params,
            return_type,
            effects,
            effect_row_var,
            where_clause,
            annotations,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            for (_, te) in params.iter_mut() {
                normalize_type_expr(te);
            }
            normalize_type_expr(return_type);
            for er in effects.iter_mut() {
                normalize_effect_ref(er);
            }
            if let Some((_, s)) = effect_row_var {
                *s = S;
            }
            for tb in where_clause.iter_mut() {
                normalize_trait_bound(tb);
            }
            for ann in annotations.iter_mut() {
                normalize_annotation(ann);
            }
        }
        Decl::FunBinding {
            id,
            name_span,
            params,
            guard,
            body,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            for p in params.iter_mut() {
                normalize_pat(p);
            }
            if let Some(g) = guard {
                normalize_expr(g);
            }
            normalize_expr(body);
        }
        Decl::Let {
            id,
            name_span,
            annotation,
            value,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            if let Some(te) = annotation {
                normalize_type_expr(te);
            }
            normalize_expr(value);
        }
        Decl::TypeDef {
            id,
            name_span,
            variants,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            for v in variants.iter_mut() {
                normalize_annotated(v, normalize_type_constructor);
            }
        }
        Decl::RecordDef {
            id,
            name_span,
            fields,
            dangling_trivia,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            dangling_trivia.clear();
            for f in fields.iter_mut() {
                normalize_annotated(f, |(_name, te)| normalize_type_expr(te));
            }
        }
        Decl::EffectDef {
            id,
            name_span,
            operations,
            dangling_trivia,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            dangling_trivia.clear();
            for op in operations.iter_mut() {
                normalize_annotated(op, normalize_effect_op);
            }
        }
        Decl::HandlerDef {
            id,
            name_span,
            effects,
            needs,
            where_clause,
            arms,
            recovered_arms,
            return_clause,
            dangling_trivia,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            dangling_trivia.clear();
            for er in effects.iter_mut().chain(needs.iter_mut()) {
                normalize_effect_ref(er);
            }
            for tb in where_clause.iter_mut() {
                normalize_trait_bound(tb);
            }
            for arm in arms.iter_mut().chain(recovered_arms.iter_mut()) {
                normalize_annotated(arm, normalize_handler_arm);
            }
            if let Some(rc) = return_clause {
                normalize_handler_arm(rc);
            }
        }
        Decl::TraitDef {
            id,
            name_span,
            supertraits,
            methods,
            dangling_trivia,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            dangling_trivia.clear();
            for (_, s) in supertraits.iter_mut() {
                *s = S;
            }
            for m in methods.iter_mut() {
                normalize_annotated(m, normalize_trait_method);
            }
        }
        Decl::ImplDef {
            id,
            trait_name_span,
            target_type_span,
            where_clause,
            needs,
            methods,
            dangling_trivia,
            span,
            ..
        } => {
            *id = NID;
            *trait_name_span = S;
            *target_type_span = S;
            *span = S;
            dangling_trivia.clear();
            for tb in where_clause.iter_mut() {
                normalize_trait_bound(tb);
            }
            for er in needs.iter_mut() {
                normalize_effect_ref(er);
            }
            for m in methods.iter_mut() {
                normalize_annotated(m, normalize_impl_method);
            }
        }
        Decl::Import { id, span, .. } => {
            *id = NID;
            *span = S;
        }
        Decl::ModuleDecl { id, span, .. } => {
            *id = NID;
            *span = S;
        }
        Decl::DictConstructor {
            id,
            methods,
            span,
            ..
        } => {
            *id = NID;
            *span = S;
            for m in methods.iter_mut() {
                normalize_expr(m);
            }
        }
    }
}

fn normalize_expr(e: &mut Expr) {
    e.id = NID;
    e.span = S;
    normalize_expr_kind(&mut e.kind);
}

fn normalize_expr_kind(ek: &mut ExprKind) {
    match ek {
        ExprKind::Lit { .. } | ExprKind::Var { .. } | ExprKind::Constructor { .. } => {}
        ExprKind::App { func, arg } => {
            normalize_expr(func);
            normalize_expr(arg);
        }
        ExprKind::BinOp { left, right, .. } => {
            normalize_expr(left);
            normalize_expr(right);
        }
        ExprKind::UnaryMinus { expr } => normalize_expr(expr),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            normalize_expr(cond);
            normalize_expr(then_branch);
            normalize_expr(else_branch);
        }
        ExprKind::Case {
            scrutinee,
            arms,
            dangling_trivia,
        } => {
            normalize_expr(scrutinee);
            for arm in arms.iter_mut() {
                normalize_annotated(arm, normalize_case_arm);
            }
            dangling_trivia.clear();
        }
        ExprKind::Block {
            stmts,
            dangling_trivia,
        } => {
            for stmt in stmts.iter_mut() {
                normalize_annotated(stmt, normalize_stmt);
            }
            dangling_trivia.clear();
        }
        ExprKind::Lambda { params, body } => {
            for p in params.iter_mut() {
                normalize_pat(p);
            }
            normalize_expr(body);
        }
        ExprKind::FieldAccess { expr, .. } => normalize_expr(expr),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            for (_, s, e) in fields.iter_mut() {
                *s = S;
                normalize_expr(e);
            }
        }
        ExprKind::RecordUpdate {
            record, fields, ..
        } => {
            normalize_expr(record);
            for (_, s, e) in fields.iter_mut() {
                *s = S;
                normalize_expr(e);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for a in args.iter_mut() {
                normalize_expr(a);
            }
        }
        ExprKind::With { expr, handler } => {
            normalize_expr(expr);
            normalize_handler(handler);
        }
        ExprKind::Resume { value } => normalize_expr(value),
        ExprKind::Tuple { elements } => {
            for e in elements.iter_mut() {
                normalize_expr(e);
            }
        }
        ExprKind::QualifiedName { .. } | ExprKind::DictRef { .. } => {}
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            dangling_trivia,
        } => {
            for (p, e) in bindings.iter_mut() {
                normalize_pat(p);
                normalize_expr(e);
            }
            normalize_expr(success);
            for arm in else_arms.iter_mut() {
                normalize_annotated(arm, normalize_case_arm);
            }
            dangling_trivia.clear();
        }
        ExprKind::Receive {
            arms,
            after_clause,
            dangling_trivia,
        } => {
            for arm in arms.iter_mut() {
                normalize_annotated(arm, normalize_case_arm);
            }
            if let Some((timeout, body)) = after_clause {
                normalize_expr(timeout);
                normalize_expr(body);
            }
            dangling_trivia.clear();
        }
        ExprKind::Ascription { expr, type_expr } => {
            normalize_expr(expr);
            normalize_type_expr(type_expr);
        }
        ExprKind::Pipe {
            segments,
            multiline,
        } => {
            *multiline = false;
            for seg in segments.iter_mut() {
                normalize_annotated(seg, normalize_expr);
            }
        }
        ExprKind::PipeBack { segments }
        | ExprKind::ComposeForward { segments }
        | ExprKind::ComposeBack { segments } => {
            for seg in segments.iter_mut() {
                normalize_annotated(seg, normalize_expr);
            }
        }
        ExprKind::Cons { head, tail } => {
            normalize_expr(head);
            normalize_expr(tail);
        }
        ExprKind::ListLit { elements } => {
            for e in elements.iter_mut() {
                normalize_expr(e);
            }
        }
        ExprKind::StringInterp { parts } => {
            for part in parts.iter_mut() {
                if let StringPart::Expr(e) = part {
                    normalize_expr(e);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            normalize_expr(body);
            for q in qualifiers.iter_mut() {
                match q {
                    ComprehensionQualifier::Generator(p, e)
                    | ComprehensionQualifier::Let(p, e) => {
                        normalize_pat(p);
                        normalize_expr(e);
                    }
                    ComprehensionQualifier::Guard(e) => normalize_expr(e),
                }
            }
        }
        ExprKind::DictMethodAccess { dict, .. } => normalize_expr(dict),
        ExprKind::ForeignCall { args, .. } => {
            for a in args.iter_mut() {
                normalize_expr(a);
            }
        }
    }
}

fn normalize_pat(p: &mut Pat) {
    match p {
        Pat::Wildcard { id, span } => {
            *id = NID;
            *span = S;
        }
        Pat::Var { id, span, .. } => {
            *id = NID;
            *span = S;
        }
        Pat::Lit { id, span, .. } => {
            *id = NID;
            *span = S;
        }
        Pat::Constructor {
            id, args, span, ..
        } => {
            *id = NID;
            *span = S;
            for a in args.iter_mut() {
                normalize_pat(a);
            }
        }
        Pat::Record {
            id, fields, span, ..
        } => {
            *id = NID;
            *span = S;
            for (_, alias) in fields.iter_mut() {
                if let Some(p) = alias {
                    normalize_pat(p);
                }
            }
        }
        Pat::AnonRecord {
            id, fields, span, ..
        } => {
            *id = NID;
            *span = S;
            for (_, alias) in fields.iter_mut() {
                if let Some(p) = alias {
                    normalize_pat(p);
                }
            }
        }
        Pat::Tuple {
            id,
            elements,
            span,
        } => {
            *id = NID;
            *span = S;
            for e in elements.iter_mut() {
                normalize_pat(e);
            }
        }
        Pat::StringPrefix {
            id, rest, span, ..
        } => {
            *id = NID;
            *span = S;
            normalize_pat(rest);
        }
    }
}

fn normalize_stmt(s: &mut Stmt) {
    match s {
        Stmt::Let {
            pattern,
            annotation,
            value,
            span,
            ..
        } => {
            *span = S;
            normalize_pat(pattern);
            if let Some(te) = annotation {
                normalize_type_expr(te);
            }
            normalize_expr(value);
        }
        Stmt::LetFun {
            id,
            name_span,
            params,
            guard,
            body,
            span,
            ..
        } => {
            *id = NID;
            *name_span = S;
            *span = S;
            for p in params.iter_mut() {
                normalize_pat(p);
            }
            if let Some(g) = guard {
                normalize_expr(g);
            }
            normalize_expr(body);
        }
        Stmt::Expr(e) => normalize_expr(e),
    }
}

fn normalize_type_expr(te: &mut TypeExpr) {
    match te {
        TypeExpr::Named { span, .. } | TypeExpr::Var { span, .. } => *span = S,
        TypeExpr::App { func, arg, span } => {
            *span = S;
            normalize_type_expr(func);
            normalize_type_expr(arg);
        }
        TypeExpr::Arrow {
            from,
            to,
            effects,
            effect_row_var,
            span,
        } => {
            *span = S;
            normalize_type_expr(from);
            normalize_type_expr(to);
            for er in effects.iter_mut() {
                normalize_effect_ref(er);
            }
            if let Some((_, s)) = effect_row_var {
                *s = S;
            }
        }
        TypeExpr::Record { fields, span } => {
            *span = S;
            for (_, te) in fields.iter_mut() {
                normalize_type_expr(te);
            }
        }
    }
}

fn normalize_case_arm(arm: &mut CaseArm) {
    arm.span = S;
    normalize_pat(&mut arm.pattern);
    if let Some(g) = &mut arm.guard {
        normalize_expr(g);
    }
    normalize_expr(&mut arm.body);
}

fn normalize_handler_arm(arm: &mut HandlerArm) {
    arm.span = S;
    for (_, s) in arm.params.iter_mut() {
        *s = S;
    }
    normalize_expr(&mut arm.body);
}

fn normalize_effect_op(op: &mut EffectOp) {
    op.span = S;
    for (_, te) in op.params.iter_mut() {
        normalize_type_expr(te);
    }
    normalize_type_expr(&mut op.return_type);
}

fn normalize_handler(h: &mut Handler) {
    match h {
        Handler::Named(_, span) => *span = S,
        Handler::Inline {
            arms,
            return_clause,
            dangling_trivia,
            ..
        } => {
            for arm in arms.iter_mut() {
                normalize_annotated(arm, normalize_handler_arm);
            }
            if let Some(rc) = return_clause {
                normalize_handler_arm(rc);
            }
            dangling_trivia.clear();
        }
    }
}

fn normalize_effect_ref(er: &mut EffectRef) {
    er.span = S;
    for te in er.type_args.iter_mut() {
        normalize_type_expr(te);
    }
}

fn normalize_trait_bound(tb: &mut TraitBound) {
    for (_, s) in tb.traits.iter_mut() {
        *s = S;
    }
}

fn normalize_annotation(ann: &mut Annotation) {
    ann.name_span = S;
    ann.span = S;
}

fn normalize_trait_method(m: &mut TraitMethod) {
    m.span = S;
    for (_, te) in m.params.iter_mut() {
        normalize_type_expr(te);
    }
    normalize_type_expr(&mut m.return_type);
}

fn normalize_impl_method(m: &mut ImplMethod) {
    m.name_span = S;
    for p in m.params.iter_mut() {
        normalize_pat(p);
    }
    normalize_expr(&mut m.body);
}

fn normalize_type_constructor(tc: &mut TypeConstructor) {
    tc.id = NID;
    tc.span = S;
    for (_, te) in tc.fields.iter_mut() {
        normalize_type_expr(te);
    }
}

fn normalize_annotated<T>(a: &mut Annotated<T>, f: impl FnOnce(&mut T)) {
    f(&mut a.node);
    // Annotated::PartialEq already ignores trivia, but clear for consistency
    a.leading_trivia.clear();
    a.trailing_comment = None;
    a.trailing_trivia.clear();
}

/// Format at default width (80).
fn fmt80(source: &str) -> String {
    fmt(source, 80)
}

// --- Fun bindings ---

#[test]
fn fun_binding_short_stays_on_one_line() {
    assert_eq!(fmt80("add x y = x + y"), "add x y = x + y\n");
}

#[test]
fn fun_binding_long_breaks_after_eq() {
    let src = "process_all_the_things x y z = some_very_long_function_name x y z";
    let result = fmt(src, 40);
    assert_eq!(
        result,
        "process_all_the_things x y z =\n  some_very_long_function_name x y z\n"
    );
}

#[test]
fn fun_binding_block_body_stays_on_eq_line() {
    let src = "process path = {\n  log! path\n}";
    assert_eq!(fmt80(src), "process path = {\n  log! path\n}\n");
}

#[test]
fn fun_binding_case_body_stays_on_eq_line() {
    let src = "dispatch shape = case shape {\n  Circle(r) -> r\n  Point -> 0.0\n}";
    assert_eq!(
        fmt80(src),
        "dispatch shape = case shape {\n  Circle(r) -> r\n  Point -> 0.0\n}\n"
    );
}

// --- Let bindings (declarations) ---

#[test]
fn let_decl_short_stays_on_one_line() {
    assert_eq!(fmt80("let x = 42"), "let x = 42\n");
}

#[test]
fn let_decl_long_breaks_after_eq() {
    let src = "let some_very_long_name = some_very_long_expression_that_is_way_too_wide";
    let result = fmt(src, 50);
    assert_eq!(
        result,
        "let some_very_long_name =\n  some_very_long_expression_that_is_way_too_wide\n"
    );
}

// --- Let statements (inside blocks) ---

#[test]
fn let_stmt_short_stays_on_one_line() {
    let src = "main () = {\n  let x = 42\n}";
    assert_eq!(fmt80(src), "main () = {\n  let x = 42\n}\n");
}

#[test]
fn let_stmt_long_breaks_after_eq() {
    let src = "main () = {\n  let result = some_very_long_function applied_to arguments\n}";
    let result = fmt(src, 40);
    // Both let binding and application break
    assert_eq!(
        result,
        "main () = {\n  let result =\n    some_very_long_function\n      applied_to\n      arguments\n}\n"
    );
}

// --- Pipes ---

#[test]
fn pipe_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = x |> add 1"), "f x = x |> add 1\n");
}

#[test]
fn pipe_long_breaks_per_segment() {
    let src = "f x = x |> add 1 |> multiply 2 |> subtract 3 |> divide 4 |> negate";
    let result = fmt(src, 40);
    assert!(result.contains("|> add 1\n"));
    assert!(result.contains("|> multiply 2\n"));
}

#[test]
fn pipe_multiline_preserved() {
    // User explicitly put |> on new lines — should stay multi-line
    let src = "f x = x\n  |> add 1\n  |> double";
    let result = fmt80(src);
    assert!(result.contains("|> add 1\n"));
    assert!(result.contains("|> double\n"));
}

#[test]
fn pipe_with_comments_stays_multiline() {
    let src = "f x = x\n  # before pipe\n  |> add 1\n  |> double";
    let result = fmt80(src);
    assert!(result.contains("# before pipe\n"));
    assert!(result.contains("|> add 1\n"));
}

// --- If-then-else ---

#[test]
fn if_short_stays_on_one_line() {
    assert_eq!(
        fmt80("pick x = if x > 0 then x else -x"),
        "pick x = if x > 0 then x else -x\n"
    );
}

#[test]
fn if_long_breaks_before_else() {
    let src = "pick x = if some_long_condition x then some_long_result x else other_long_result x";
    let result = fmt(src, 50);
    assert!(result.contains("then"), "result: {}", result);
    assert!(
        result.contains("\n  else") || result.contains("\nelse"),
        "result: {}",
        result
    );
}

// --- Blocks ---

#[test]
fn block_preserves_braces() {
    let src = "main () = {\n  println \"hello\"\n}";
    assert_eq!(fmt80(src), "main () = {\n  println \"hello\"\n}\n");
}

#[test]
fn block_with_multiple_stmts() {
    let src = "main () = {\n  let x = 1\n  println x\n}";
    assert_eq!(fmt80(src), "main () = {\n  let x = 1\n  println x\n}\n");
}

// --- Comments ---

#[test]
fn trailing_comment_preserved() {
    assert_eq!(
        fmt80("let x = 42 # the answer"),
        "let x = 42 # the answer\n"
    );
}

#[test]
fn leading_comment_preserved() {
    assert_eq!(
        fmt80("# a comment\nlet x = 42"),
        "# a comment\nlet x = 42\n"
    );
}

// --- Fun signatures ---

#[test]
fn fun_sig_short_stays_on_one_line() {
    assert_eq!(
        fmt80("fun add : Int -> Int -> Int"),
        "fun add : Int -> Int -> Int\n"
    );
}

#[test]
fn fun_sig_with_needs_stays_on_one_line() {
    assert_eq!(
        fmt80("fun process : String -> Unit needs {Log}"),
        "fun process : String -> Unit needs {Log}\n"
    );
}

#[test]
fn fun_sig_long_breaks_needs() {
    let src =
        "fun process_everything : String -> Int -> Result String Error needs {Log, Actor, Process}";
    let result = fmt(src, 60);
    // needs clause should break to next line
    assert!(result.contains("\n  needs {"), "result: {}", result);
}

// --- Application ---

#[test]
fn app_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = call a b c"), "f x = call a b c\n");
}

#[test]
fn app_long_breaks_all_args() {
    let src = "f x = some_long_function first_argument second_argument third_argument";
    let result = fmt(src, 40);
    assert!(result.contains("some_long_function\n"), "result: {}", result);
    assert!(result.contains("  first_argument\n"), "result: {}", result);
    assert!(result.contains("  second_argument\n"), "result: {}", result);
}

#[test]
fn app_nested_calls_parenthesized() {
    assert_eq!(
        fmt80("f x = call a (call b) (call c)"),
        "f x = call a (call b) (call c)\n"
    );
}

// --- Records ---

#[test]
fn record_create_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f x = User { name: x, age: 30 }"),
        "f x = User { name: x, age: 30 }\n"
    );
}

#[test]
fn record_create_long_breaks_fields() {
    let src = "f x = SomeRecord { first_field: some_long_value, second_field: another_long_value }";
    let result = fmt(src, 50);
    assert!(result.contains("SomeRecord {\n"), "result: {}", result);
    assert!(result.contains("  first_field:"), "result: {}", result);
}

#[test]
fn record_update_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f u = { u | age: 31 }"),
        "f u = { u | age: 31 }\n"
    );
}

#[test]
fn record_update_long_breaks_fields() {
    let src = "f u = { u | age: some_very_long_expression, name: another_very_long_expression }";
    let result = fmt(src, 40);
    assert!(result.contains("{ u |"), "result: {}", result);
    assert!(result.contains("  age:"), "result: {}", result);
}

// --- Lists ---

#[test]
fn list_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = [1, 2, 3]"), "f x = [1, 2, 3]\n");
}

#[test]
fn list_long_breaks_elements() {
    let src = "f x = [some_long_name, another_long_name, yet_another_long_name, final_name]";
    let result = fmt(src, 40);
    assert!(result.contains("[\n"), "result: {}", result);
    assert!(result.contains("  some_long_name,\n"), "result: {}", result);
}

#[test]
fn list_empty() {
    assert_eq!(fmt80("f x = []"), "f x = []\n");
}

// --- Tuples ---

#[test]
fn tuple_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = (1, 2, 3)"), "f x = (1, 2, 3)\n");
}

#[test]
fn tuple_long_breaks_elements() {
    let src = "f x = (some_long_name, another_long_name, yet_another_long_name)";
    let result = fmt(src, 40);
    assert!(result.contains("(\n"), "result: {}", result);
    assert!(result.contains("  some_long_name,\n"), "result: {}", result);
}

// --- Binary operators ---

#[test]
fn binop_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = a + b + c"), "f x = a + b + c\n");
}

#[test]
fn binop_long_breaks_before_operator() {
    let src = "f x = some_long_name + another_long_name + yet_another_long_name + final_name";
    let result = fmt(src, 40);
    assert!(result.contains("\n+ another_long_name") || result.contains("\n  + another_long_name"), "result: {}", result);
}

#[test]
fn binop_mixed_operators_not_flattened() {
    // a + b * c should NOT flatten — different operators
    assert_eq!(fmt80("f x = a + b * c"), "f x = a + b * c\n");
}

// --- With expressions ---

#[test]
fn with_named_handler_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f x = do_thing x with console"),
        "f x = do_thing x with console\n"
    );
}

#[test]
fn with_named_handler_long_breaks_before_with() {
    let src = "f x = some_very_long_function_call x y z with some_long_handler_name";
    let result = fmt(src, 50);
    assert!(result.contains("with some_long_handler_name"), "result: {}", result);
    // with breaks to its own line (indented under the expression)
    assert!(result.contains("\n"), "should be multi-line: {}", result);
}

#[test]
fn with_inline_handler_braces_on_same_line() {
    let src = "f x = do_thing x with {\n  log msg = { println msg; resume () },\n}";
    let result = fmt80(src);
    assert!(result.contains("with {"), "result: {}", result);
}

// --- Lambda ---

#[test]
fn lambda_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f x = fun y -> y + 1"),
        "f x = fun y -> y + 1\n"
    );
}

#[test]
fn lambda_long_breaks_after_arrow() {
    let src = "f x = fun some_long_param -> some_very_long_expression some_long_param other_arg";
    let result = fmt(src, 50);
    assert!(result.contains(" ->\n"), "result: {}", result);
}

// --- Imports ---

#[test]
fn import_simple() {
    assert_eq!(fmt80("import Std.List"), "import Std.List\n");
}

#[test]
fn import_exposing_short() {
    assert_eq!(
        fmt80("import Std.Test (describe, test)"),
        "import Std.Test (describe, test)\n"
    );
}

#[test]
fn import_exposing_long_breaks() {
    let src = "import Some.Very.Long.Module (first_thing, second_thing, third_thing, fourth_thing)";
    let result = fmt(src, 50);
    assert!(result.contains("\n"), "should break: {}", result);
    assert!(result.contains("first_thing"), "result: {}", result);
}

// --- Import sorting ---

#[test]
fn imports_sorted_std_first() {
    let src = "import MyModule\nimport Std.List\nimport Std.Array\nimport Another";
    let result = fmt80(src);
    let lines: Vec<&str> = result.lines().collect();
    assert_eq!(lines[0], "import Std.Array");
    assert_eq!(lines[1], "import Std.List");
    assert_eq!(lines[2], "import Another");
    assert_eq!(lines[3], "import MyModule");
}

#[test]
fn imports_already_sorted_unchanged() {
    let src = "import Std.List\nimport Std.Test (describe, test)\nimport MyModule";
    let result = fmt80(src);
    assert!(result.starts_with("import Std.List\nimport Std.Test"), "result: {}", result);
}

// --- Blank line normalization ---

#[test]
fn multiple_blank_lines_collapsed_to_one() {
    let src = "let x = 1\n\n\n\n\nlet y = 2";
    assert_eq!(fmt80(src), "let x = 1\n\nlet y = 2\n");
}

#[test]
fn single_blank_line_preserved() {
    let src = "let x = 1\n\nlet y = 2";
    assert_eq!(fmt80(src), "let x = 1\n\nlet y = 2\n");
}

// --- Idempotency ---

#[test]
fn idempotent_scratch_file() {
    let source = std::fs::read_to_string("examples/scratch.dy").unwrap();
    let first = fmt80(&source);
    let second = fmt80(&first);
    assert_eq!(first, second, "Formatter is not idempotent");
}

// --- Round-trip: all .dy files format cleanly, idempotently, and preserve AST ---

fn collect_dy_files() -> Vec<std::path::PathBuf> {
    let mut files = Vec::new();
    for dir in &["examples", "src/stdlib"] {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "dy") {
                    files.push(path);
                }
            }
        }
    }
    files.sort();
    files
}

/// Files with known formatter bugs that prevent clean round-tripping.
/// Each entry documents why so we can remove it when fixed.
///
/// - Triple-quoted strings (`"""`) not preserved (13-strings, String.dy)
/// - `()` printed as `Unit` in type exprs (14-fail-to-result, 25-state-effect, Async.dy)
/// - `(a, b)` printed as `Tuple a b` in return types (25-state-effect)
/// - `pub opaque` loses `pub` keyword (Async.dy)
/// - Deriving clause placement on multi-line type defs (28-deriving)
/// - Comment indentation stripped (36-sync-actor)
/// - Escaped quotes in strings `"\""` become `"""` (String.dy)
/// - Handler arm zero-arg ops lose `()` params (25-state-effect)
/// - Formatted output doesn't re-parse (20-validation-applicative, 29-actors,
///   32-monitor, 33-timer, 34-link, Dict.dy, Test.dy)
const KNOWN_FAILING: &[&str] = &[
    "13-strings.dy",
    "14-fail-to-result.dy",
    "20-validation-applicative.dy",
    "25-state-effect.dy",
    "28-deriving.dy",
    "29-actors.dy",
    "32-monitor.dy",
    "33-timer.dy",
    "34-link.dy",
    "36-sync-actor.dy",
    "Async.dy",
    "Dict.dy",
    "String.dy",
    "Test.dy",
];

fn is_known_failing(path: &std::path::Path) -> bool {
    let name = path.file_name().unwrap().to_str().unwrap();
    KNOWN_FAILING.contains(&name)
}

#[test]
fn round_trip_all_dy_files() {
    let mut failures = Vec::new();

    for path in collect_dy_files() {
        if is_known_failing(&path) {
            continue;
        }
        let source = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();

        // 1. Format (skip files that don't parse — e.g. error examples)
        let first = match try_fmt(&source, 80) {
            Some(f) => f,
            None => continue,
        };

        // 2. Idempotency: format again, should be identical
        let second = match try_fmt(&first, 80) {
            Some(f) => f,
            None => {
                failures.push(format!("{}: re-format failed", name));
                continue;
            }
        };
        if first != second {
            failures.push(format!("{}: not idempotent", name));
        }

        // 3. Round-trip: normalized AST should be unchanged after formatting
        let original_ast = match try_parse_normalized(&source) {
            Some(a) => a,
            None => continue,
        };
        let formatted_ast = match try_parse_normalized(&first) {
            Some(a) => a,
            None => {
                failures.push(format!("{}: re-parse failed", name));
                continue;
            }
        };
        if original_ast != formatted_ast {
            failures.push(format!("{}: AST changed", name));
        }
    }

    assert!(failures.is_empty(), "Round-trip failures:\n{}", failures.join("\n"));
}

/// Verify that known-failing files still fail (so we remove them from the list when fixed).
#[test]
fn known_failing_files_still_fail() {
    let mut unexpectedly_passing = Vec::new();

    for path in collect_dy_files() {
        if !is_known_failing(&path) {
            continue;
        }
        let source = std::fs::read_to_string(&path).unwrap();

        let first = match try_fmt(&source, 80) {
            Some(f) => f,
            None => continue,
        };
        let second = match try_fmt(&first, 80) {
            Some(f) => f,
            None => continue,
        };
        if first != second {
            continue; // still broken (not idempotent)
        }
        let original = match try_parse_normalized(&source) {
            Some(a) => a,
            None => continue,
        };
        let formatted = match try_parse_normalized(&first) {
            Some(a) => a,
            None => continue,
        };
        if original == formatted {
            unexpectedly_passing.push(path.display().to_string());
        }
    }

    assert!(
        unexpectedly_passing.is_empty(),
        "These files now pass round-trip — remove from KNOWN_FAILING:\n{}",
        unexpectedly_passing.join("\n")
    );
}

