use super::Doc;
use super::decl::is_block_like;
use super::helpers::{
    docs_from_vec, format_binop, format_trailing, format_trivia, format_trivia_dangling,
};
use super::pat::format_pat;
use super::type_expr::format_type_expr;
use crate::ast::*;
use crate::docs;
use crate::token::Span;
use crate::token::StringKind;

/// Flatten a left-nested BinOp chain of the same operator.
/// `(a + b) + c` with op=Add -> ([a, b, c], Add)
/// Stops flattening when the operator changes (respects precedence).
fn flatten_binop<'a>(expr: &'a Expr, op: &'a BinOp) -> (Vec<&'a Expr>, &'a BinOp) {
    let mut operands = Vec::new();
    let mut current = expr;
    while let ExprKind::BinOp {
        op: ref curr_op,
        ref left,
        ref right,
    } = current.kind
    {
        if curr_op == op {
            operands.push(right.as_ref());
            current = left.as_ref();
        } else {
            break;
        }
    }
    operands.push(current);
    operands.reverse();
    (operands, op)
}

/// Flatten a left-nested App chain into (func, [arg1, arg2, ...]).
fn flatten_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}

fn format_binary_chain(segments: &[Annotated<Expr>], op: &str) -> Doc {
    let mut parts: Vec<Doc> = Vec::new();
    for (i, seg) in segments.iter().enumerate() {
        if i > 0 {
            parts.push(Doc::text(op));
        }
        parts.push(format_expr(&seg.node));
    }
    docs_from_vec(parts)
}

/// Build a nested body for a braced block: each item gets a hardline before it,
/// trivia is emitted inline, and dangling trivia omits its trailing hardline.
/// The result should be wrapped in `Doc::nest(indent, body)`.
fn format_braced_body(items: &[Doc], dangling_trivia: &[Trivia]) -> Doc {
    let mut body = Doc::Nil;
    for item in items {
        body = body.append(item.clone());
    }
    if !dangling_trivia.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling_trivia));
    }
    body
}

pub fn format_expr(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { value } => super::helpers::format_lit(value),
        ExprKind::Var { name } => Doc::text(name),
        ExprKind::Constructor { name } => Doc::text(name),
        ExprKind::QualifiedName { module, name } => Doc::text(format!("{}.{}", module, name)),

        ExprKind::App { .. } => {
            // Flatten nested App chain: App(App(App(f, a), b), c) -> [f, a, b, c]
            let (func, args) = flatten_app(expr);
            let func_doc = format_expr(func);

            // Check if the last arg is a lambda with a block-like body.
            // If so, treat it as a "trailing lambda": keep `(fun params -> {`
            // on the same line as the call, with the block body indented from
            // the call site, not nested inside the arg list.
            if let Some((last, rest)) = args.split_last()
                && let ExprKind::Lambda { params, body } = &last.kind
                && is_block_like(body)
            {
                let mut prefix = func_doc;
                for a in rest {
                    prefix = prefix.append(Doc::text(" ")).append(format_expr_atom(a));
                }
                let mut lhs = Doc::text("(fun ");
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        lhs = lhs.append(Doc::text(" "));
                    }
                    lhs = lhs.append(format_pat(p));
                }
                lhs = lhs.append(Doc::text(" -> "));
                let body_doc = format_expr(body);
                return docs![prefix, Doc::text(" "), lhs, body_doc, Doc::text(")")];
            }

            let arg_docs: Vec<Doc> = args.iter().map(|a| format_expr_atom(a)).collect();

            // flat: `func arg1 arg2 arg3`
            // broken: `func\n  arg1\n  arg2\n  arg3`
            let mut tail = Doc::Nil;
            for arg in arg_docs {
                tail = tail.append(Doc::line()).append(arg);
            }
            Doc::group(docs![func_doc, Doc::nest(2, tail)])
        }

        ExprKind::BinOp { op, .. } => {
            // Flatten same-operator chains: (a + b) + c -> [a, b, c]
            let (operands, chain_op) = flatten_binop(expr, op);
            let op_str = format_binop(chain_op);

            let first = format_expr(operands[0]);
            let mut tail = Doc::Nil;
            for operand in &operands[1..] {
                tail = tail
                    .append(Doc::line())
                    .append(Doc::text(format!("{} ", op_str)))
                    .append(format_expr(operand));
            }
            Doc::group(docs![first, tail])
        }

        ExprKind::UnaryMinus { expr } => {
            docs![Doc::text("-"), format_expr(expr)]
        }

        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => Doc::group(docs![
            Doc::text("if "),
            format_expr(cond),
            Doc::text(" then "),
            format_expr(then_branch),
            Doc::line(),
            Doc::text("else "),
            format_expr(else_branch),
        ]),

        ExprKind::Case {
            scrutinee,
            arms,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for ann in arms {
                let arm = &ann.node;
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                let mut arm_doc = format_pat(&arm.pattern);
                if let Some(g) = &arm.guard {
                    arm_doc = arm_doc.append(Doc::text(" | ")).append(format_expr(g));
                }
                arm_doc = arm_doc
                    .append(Doc::text(" -> "))
                    .append(format_expr(&arm.body));
                body_items.push(arm_doc);
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("case "),
                format_expr(scrutinee),
                Doc::text(" {"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Block {
            stmts,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for ann in stmts {
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                body_items.push(format_stmt(&ann.node));
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("{"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Lambda { params, body } => {
            let mut lhs = Doc::text("fun ");
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    lhs = lhs.append(Doc::text(" "));
                }
                lhs = lhs.append(format_pat(p));
            }
            lhs = lhs.append(Doc::text(" ->"));
            let body_doc = format_expr(body);
            Doc::group(docs![lhs, Doc::nest(2, docs![Doc::line(), body_doc])])
        }

        ExprKind::FieldAccess { expr, field } => {
            docs![format_expr(expr), Doc::text(format!(".{}", field))]
        }

        ExprKind::RecordCreate { name, fields } => format_record_create(Some(name), fields),
        ExprKind::AnonRecordCreate { fields } => format_record_create(None, fields),

        ExprKind::RecordUpdate { record, fields } => {
            let field_docs: Vec<Doc> = fields
                .iter()
                .map(|(name, _, val)| docs![Doc::text(format!("{}: ", name)), format_expr(val)])
                .collect();
            // flat: { u | age: 31, name: "New" }
            // broken: { u |\n  age: 31,\n  name: "New"\n}
            let opener = docs![Doc::text("{ "), format_expr(record), Doc::text(" |")];
            format_comma_list_spaced(opener, "}", field_docs)
        }

        ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            let mut d = match qualifier {
                Some(q) => Doc::text(format!("{}.{}!", q, name)),
                None => Doc::text(format!("{}!", name)),
            };
            for arg in args {
                d = d.append(Doc::text(" ")).append(format_expr_atom(arg));
            }
            d
        }

        ExprKind::With { expr, handler } => {
            let expr_doc = format_expr(expr);
            let handler_doc = format_handler(handler);
            match handler.as_ref() {
                // Inline handler: always break the block, but keep expr with { on same line
                Handler::Inline { .. } => {
                    docs![expr_doc, Doc::text(" with "), handler_doc]
                }
                // Named handler: try one line, break before with if too long
                Handler::Named(..) => Doc::group(docs![
                    expr_doc,
                    Doc::nest(2, docs![Doc::line(), Doc::text("with "), handler_doc])
                ]),
            }
        }

        ExprKind::Resume { value } => {
            docs![Doc::text("resume "), format_expr(value)]
        }

        ExprKind::Tuple { elements } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_expr).collect();
            format_comma_list(Doc::text("("), ")", elem_docs)
        }

        ExprKind::Do {
            bindings,
            success,
            else_arms,
            dangling_trivia,
        } => {
            let mut do_body = Doc::Nil;
            for (pat, expr) in bindings {
                do_body = do_body.append(Doc::hardline());
                do_body = do_body.append(format_pat(pat));
                do_body = do_body.append(Doc::text(" <- "));
                do_body = do_body.append(format_expr(expr));
            }
            do_body = do_body.append(Doc::hardline()).append(format_expr(success));

            let mut else_items = Vec::new();
            for ann in else_arms {
                let arm = &ann.node;
                else_items.push(Doc::hardline());
                else_items.push(format_trivia(&ann.leading_trivia));
                let arm_doc = docs![
                    format_pat(&arm.pattern),
                    Doc::text(" -> "),
                    format_expr(&arm.body)
                ];
                else_items.push(arm_doc);
                else_items.push(format_trailing(&ann.trailing_comment));
            }
            let else_body = format_braced_body(&else_items, dangling_trivia);

            docs![
                Doc::text("do {"),
                Doc::nest(2, do_body),
                Doc::hardline(),
                Doc::text("} else {"),
                Doc::nest(2, else_body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Receive {
            arms,
            after_clause,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for ann in arms {
                let arm = &ann.node;
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                let mut arm_doc = format_pat(&arm.pattern);
                if let Some(g) = &arm.guard {
                    arm_doc = arm_doc.append(Doc::text(" | ")).append(format_expr(g));
                }
                arm_doc = arm_doc
                    .append(Doc::text(" -> "))
                    .append(format_expr(&arm.body));
                body_items.push(arm_doc);
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            if let Some((timeout, timeout_body)) = after_clause {
                body_items.push(Doc::hardline());
                body_items.push(docs![
                    Doc::text("after "),
                    format_expr(timeout),
                    Doc::text(" -> "),
                    format_expr(timeout_body)
                ]);
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("receive {"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Ascription { expr, type_expr } => {
            docs![
                Doc::text("("),
                format_expr(expr),
                Doc::text(" : "),
                format_type_expr(type_expr),
                Doc::text(")")
            ]
        }

        // --- Surface syntax sugar ---
        ExprKind::Pipe {
            segments,
            multiline,
        } => {
            let force_multiline = *multiline
                || segments.iter().any(|s| {
                    s.trailing_comment.is_some()
                        || !s.leading_trivia.is_empty()
                        || !s.trailing_trivia.is_empty()
                });
            // Head segment
            let mut head = format_expr(&segments[0].node);
            head = head.append(format_trailing(&segments[0].trailing_comment));

            // Tail segments — same indent level as head (no extra nest)
            let mut tail = Doc::Nil;
            for seg in &segments[1..] {
                if force_multiline {
                    tail = tail.append(Doc::hardline());
                } else {
                    tail = tail.append(Doc::line());
                }
                if !seg.leading_trivia.is_empty() {
                    tail = tail.append(format_trivia(&seg.leading_trivia));
                }
                tail = tail.append(docs![Doc::text("|> "), format_expr(&seg.node)]);
                tail = tail.append(format_trailing(&seg.trailing_comment));
                // Trailing trivia (own-line comments after last segment)
                if !seg.trailing_trivia.is_empty() {
                    tail = tail.append(Doc::hardline());
                    tail = tail.append(format_trivia(&seg.trailing_trivia));
                }
            }

            let result = docs![head, tail];
            if force_multiline {
                result
            } else {
                Doc::group(result)
            }
        }
        ExprKind::PipeBack { segments } => format_binary_chain(segments, " <| "),
        ExprKind::ComposeForward { segments } => format_binary_chain(segments, " >> "),
        ExprKind::ComposeBack { segments } => format_binary_chain(segments, " << "),
        ExprKind::Cons { head, tail } => {
            docs![format_expr(head), Doc::text(" :: "), format_expr(tail)]
        }
        ExprKind::ListLit { elements } => {
            if elements.is_empty() {
                Doc::text("[]")
            } else {
                let elem_docs: Vec<Doc> = elements.iter().map(format_expr).collect();
                format_comma_list(Doc::text("["), "]", elem_docs)
            }
        }
        ExprKind::StringInterp { parts, kind } => format_interp_string(parts, *kind),
        ExprKind::ListComprehension { body, qualifiers } => {
            let mut parts = vec![Doc::text("["), format_expr(body), Doc::text(" | ")];
            let qual_docs: Vec<Doc> = qualifiers
                .iter()
                .map(|q| match q {
                    ComprehensionQualifier::Generator(pat, expr) => {
                        docs![format_pat(pat), Doc::text(" <- "), format_expr(expr)]
                    }
                    ComprehensionQualifier::Guard(expr) => format_expr(expr),
                    ComprehensionQualifier::Let(pat, expr) => {
                        docs![
                            Doc::text("let "),
                            format_pat(pat),
                            Doc::text(" = "),
                            format_expr(expr)
                        ]
                    }
                })
                .collect();
            parts.push(Doc::join(Doc::text(", "), qual_docs));
            parts.push(Doc::text("]"));
            docs_from_vec(parts)
        }

        // Elaboration-only
        ExprKind::DictMethodAccess { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::ForeignCall { .. } => Doc::text("<elaboration-only>"),
    }
}

/// Format an expression in "atom" position (parenthesize if complex).
pub fn format_expr_atom(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::Tuple { .. }
        | ExprKind::Block { .. }
        | ExprKind::StringInterp { .. }
        | ExprKind::ListLit { .. } => format_expr(expr),
        _ => docs![Doc::text("("), format_expr(expr), Doc::text(")")],
    }
}

fn format_record_create(name: Option<&String>, fields: &[(String, Span, Expr)]) -> Doc {
    let field_docs: Vec<Doc> = fields
        .iter()
        .map(|(fname, _, val)| docs![Doc::text(format!("{}: ", fname)), format_expr(val)])
        .collect();
    let opener = match name {
        Some(n) => Doc::text(format!("{} {{", n)),
        None => Doc::text("{"),
    };
    // flat: Name { a: 1, b: 2 }
    // broken: Name {\n  a: 1,\n  b: 2,\n}
    format_comma_list_spaced(opener, "}", field_docs)
}

/// Format a delimited, comma-separated list with group/break.
/// Flat: `open item1, item2 close`
/// Broken: `open\n  item1,\n  item2,\nclose`
/// Format a delimited, comma-separated list with group/break.
/// When `spaced` is true (records): flat has spaces inside: `{ a, b }`
/// When `spaced` is false (lists, tuples): flat has no spaces: `[a, b]`
fn format_comma_list(open: Doc, close: &str, items: Vec<Doc>) -> Doc {
    format_comma_list_inner(open, close, items, false)
}

fn format_comma_list_spaced(open: Doc, close: &str, items: Vec<Doc>) -> Doc {
    format_comma_list_inner(open, close, items, true)
}

fn format_comma_list_inner(open: Doc, close: &str, items: Vec<Doc>, spaced: bool) -> Doc {
    let fields_joined = Doc::join(docs![Doc::text(","), Doc::line()], items);
    let trailing_comma = Doc::if_break(Doc::text(","), Doc::Nil);
    // Spaced (records): `{ a, b }` flat, `{\n  a,\n  b,\n}` broken
    // Unspaced (lists, tuples): `[a, b]` flat, `[\n  a,\n  b,\n]` broken
    let pad = if spaced { Doc::line() } else { Doc::softline() };
    Doc::group(docs![
        open,
        Doc::nest(2, docs![pad.clone(), fields_joined, trailing_comma]),
        pad,
        Doc::text(close)
    ])
}

fn format_handler(handler: &Handler) -> Doc {
    match handler {
        Handler::Named(name, _) => Doc::text(name),
        Handler::Inline {
            named,
            arms,
            return_clause,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for name in named {
                body_items.push(Doc::hardline());
                body_items.push(Doc::text(format!("{},", name)));
            }
            for ann in arms {
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                body_items.push(format_handler_arm(&ann.node));
                body_items.push(Doc::text(","));
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            if let Some(rc) = return_clause {
                body_items.push(Doc::hardline());
                body_items.push(format_handler_arm(rc));
                body_items.push(Doc::text(","));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("{"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }
    }
}

fn format_handler_arm(arm: &HandlerArm) -> Doc {
    let mut d = Doc::text(&arm.op_name);
    for (param, _) in &arm.params {
        d = d.append(Doc::text(format!(" {}", param)));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(&arm.body));
    d
}

pub fn format_stmt(stmt: &Stmt) -> Doc {
    match stmt {
        Stmt::Let {
            pattern,
            annotation,
            value,
            assert,
            ..
        } => {
            let kw = if *assert { "let! " } else { "let " };
            let mut lhs = Doc::text(kw).append(format_pat(pattern));
            if let Some(ty) = annotation {
                lhs = lhs.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            super::decl::format_binding(lhs, value)
        }
        Stmt::LetFun {
            name,
            params,
            guard,
            body,
            ..
        } => {
            let mut lhs = Doc::text(format!("let {}", name));
            for p in params {
                lhs = lhs.append(Doc::text(" ")).append(format_pat(p));
            }
            if let Some(g) = guard {
                lhs = lhs.append(Doc::text(" | ")).append(format_expr(g));
            }
            super::decl::format_binding(lhs, body)
        }
        Stmt::Expr(expr) => format_expr(expr),
    }
}

/// Format an interpolated string, choosing single-line or triple-quoted form.
fn format_interp_string(parts: &[StringPart], kind: StringKind) -> Doc {
    match kind {
        StringKind::InterpolatedMultiline => format_interp_multiline(parts),
        _ => format_interp_single_line(parts),
    }
}

/// Format a single-line interpolated string: `$"text {expr} text"`.
fn format_interp_single_line(parts: &[StringPart]) -> Doc {
    let mut s = String::from("$\"");
    for part in parts {
        match part {
            StringPart::Lit(text) => s.push_str(&escape_interp_string(text)),
            StringPart::Expr(expr) => {
                let expr_doc = format_expr(expr);
                let rendered = super::pretty(10000, &expr_doc);
                let rendered = rendered.trim_end();
                s.push('{');
                s.push_str(rendered);
                s.push('}');
            }
        }
    }
    s.push('"');
    Doc::text(s)
}

/// Escape special characters in interpolated string literal segments.
fn escape_interp_string(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            ch => out.push(ch),
        }
    }
    out
}

/// Format a multiline interpolated string: `$"""\n  text {expr}\n  """`.
fn format_interp_multiline(parts: &[StringPart]) -> Doc {
    // Build the full text content (with {expr} rendered inline) then split into lines.
    // We need to handle Doc construction line-by-line.
    //
    // Approach: walk parts, split literal text at newlines. Each line becomes a
    // HardLine + Doc::text(...). Expression holes are rendered inline on their
    // current line.
    let mut inner = Vec::new();
    let mut current_line = String::new();

    for part in parts {
        match part {
            StringPart::Lit(text) => {
                let mut first = true;
                for segment in text.split('\n') {
                    if !first {
                        // Emit current line and start new one
                        inner.push(Doc::hardline());
                        if !current_line.is_empty() {
                            inner.push(Doc::text(std::mem::take(&mut current_line)));
                        }
                    }
                    current_line.push_str(segment);
                    first = false;
                }
            }
            StringPart::Expr(expr) => {
                let expr_doc = format_expr(expr);
                let rendered = super::pretty(10000, &expr_doc);
                let rendered = rendered.trim_end();
                current_line.push('{');
                current_line.push_str(rendered);
                current_line.push('}');
            }
        }
    }

    // Emit remaining line content
    inner.push(Doc::hardline());
    if !current_line.is_empty() {
        inner.push(Doc::text(current_line));
    }
    inner.push(Doc::hardline());
    inner.push(Doc::text("\"\"\""));

    Doc::text("$\"\"\"").append(Doc::nest(2, docs_from_vec(inner)))
}
