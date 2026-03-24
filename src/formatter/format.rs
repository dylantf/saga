use crate::ast::*;
use crate::token::Span;
use crate::docs;
use super::Doc;

// =============================================================================
// Top-level
// =============================================================================

/// Format an entire program (list of declarations).
pub fn format_program(decls: &[Decl]) -> Doc {
    let docs: Vec<Doc> = decls
        .iter()
        .filter_map(format_decl)
        .collect();
    Doc::join(Doc::hardline(), docs)
}

/// Format a single declaration. Returns None for elaboration-only nodes.
fn format_decl(decl: &Decl) -> Option<Doc> {
    Some(match decl {
        Decl::ModuleDecl { path, .. } => {
            Doc::text(format!("module {}", path.join(".")))
        }
        Decl::Import { module_path, alias, exposing, .. } => {
            format_import(module_path, alias, exposing)
        }
        Decl::FunSignature { doc, public, name, params, return_type, effects, effect_row_var, where_clause, annotations, .. } => {
            let mut parts = Vec::new();
            for ann in annotations {
                parts.push(format_annotation(ann));
                parts.push(Doc::hardline());
            }
            if !doc.is_empty() {
                parts.push(format_doc_comment(doc));
                parts.push(Doc::hardline());
            }
            if *public {
                parts.push(Doc::text("pub "));
            }
            parts.push(Doc::text(format!("fun {} : ", name)));
            parts.push(format_fun_type(params, return_type, effects, effect_row_var));
            if !where_clause.is_empty() {
                parts.push(Doc::text(" "));
                parts.push(format_where_clause(where_clause));
            }
            docs_from_vec(parts)
        }
        Decl::FunBinding { name, params, guard, body, .. } => {
            format_fun_binding(name, params, guard, body)
        }
        Decl::Let { name, annotation, value, .. } => {
            let mut d = Doc::text(format!("let {}", name));
            if let Some(ty) = annotation {
                d = d.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            d = d.append(Doc::text(" = ")).append(format_expr(value));
            d
        }
        Decl::TypeDef { doc, public, opaque, name, type_params, variants, deriving, .. } => {
            format_type_def(doc, *public, *opaque, name, type_params, variants, deriving)
        }
        Decl::RecordDef { doc, public, name, type_params, fields, deriving, .. } => {
            format_record_def(doc, *public, name, type_params, fields, deriving)
        }
        Decl::EffectDef { doc, public, name, type_params, operations, .. } => {
            format_effect_def(doc, *public, name, type_params, operations)
        }
        Decl::TraitDef { doc, public, name, type_param, supertraits, methods, .. } => {
            format_trait_def(doc, *public, name, type_param, supertraits, methods)
        }
        Decl::HandlerDef { doc, public, name, effects, needs, where_clause, arms, return_clause, .. } => {
            format_handler_def(doc, *public, name, effects, needs, where_clause, arms, return_clause)
        }
        Decl::ImplDef { doc, trait_name, target_type, type_params, where_clause, needs, methods, .. } => {
            format_impl_def(doc, trait_name, target_type, type_params, where_clause, needs, methods)
        }
        // Elaboration-only nodes -- skip
        Decl::DictConstructor { .. } => return None,
    })
}

// =============================================================================
// Declarations
// =============================================================================

fn format_import(path: &[String], alias: &Option<String>, exposing: &Option<Vec<ExposedItem>>) -> Doc {
    let mut d = Doc::text(format!("import {}", path.join(".")));
    if let Some(a) = alias {
        d = d.append(Doc::text(format!(" as {}", a)));
    }
    if let Some(items) = exposing {
        d = d.append(Doc::text(" ("))
            .append(Doc::text(items.join(", ")))
            .append(Doc::text(")"));
    }
    d
}

fn format_annotation(ann: &Annotation) -> Doc {
    let mut d = Doc::text(format!("@{}", ann.name));
    if !ann.args.is_empty() {
        let args: Vec<String> = ann.args.iter().map(format_lit_raw).collect();
        d = d.append(Doc::text("("))
            .append(Doc::text(args.join(", ")))
            .append(Doc::text(")"));
    }
    d
}

fn format_fun_binding(name: &str, params: &[Pat], guard: &Option<Box<Expr>>, body: &Expr) -> Doc {
    let mut d = Doc::text(name.to_string());
    for p in params {
        d = d.append(Doc::text(" ")).append(format_pat(p));
    }
    if let Some(g) = guard {
        d = d.append(Doc::text(" | ")).append(format_expr(g));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(body));
    d
}

fn format_type_def(
    doc: &[String], public: bool, opaque: bool, name: &str,
    type_params: &[String], variants: &[TypeConstructor], deriving: &[String],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if opaque {
        header.push_str("opaque ");
    } else if public {
        header.push_str("pub ");
    }
    header.push_str("type ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }

    parts.push(Doc::text(header));

    // Format variants
    for (i, variant) in variants.iter().enumerate() {
        let prefix = if i == 0 { "\n  = " } else { "\n  | " };
        parts.push(Doc::text(prefix));
        parts.push(Doc::text(&variant.name));
        if !variant.fields.is_empty() {
            let fields: Vec<Doc> = variant.fields.iter().map(|(label, ty)| {
                match label {
                    Some(l) => docs![Doc::text(format!("{}: ", l)), format_type_expr(ty)],
                    None => format_type_expr(ty),
                }
            }).collect();
            parts.push(Doc::text("("));
            parts.push(Doc::join(Doc::text(", "), fields));
            parts.push(Doc::text(")"));
        }
    }

    if !deriving.is_empty() {
        parts.push(Doc::text(format!(" deriving ({})", deriving.join(", "))));
    }

    docs_from_vec(parts)
}

fn format_record_def(
    doc: &[String], public: bool, name: &str,
    type_params: &[String], fields: &[(String, TypeExpr)], deriving: &[String],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("record ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }
    header.push_str(" {");
    parts.push(Doc::text(header));

    let field_docs: Vec<Doc> = fields.iter().map(|(fname, ty)| {
        docs![Doc::text(format!("  {} : ", fname)), format_type_expr(ty), Doc::text(",")]
    }).collect();

    parts.push(Doc::nest(0, Doc::join(Doc::hardline(), field_docs)));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));

    if !deriving.is_empty() {
        parts.push(Doc::text(format!(" deriving ({})", deriving.join(", "))));
    }

    docs_from_vec(parts)
}

fn format_effect_def(
    doc: &[String], public: bool, name: &str,
    type_params: &[String], operations: &[EffectOp],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("effect ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }
    header.push_str(" {");
    parts.push(Doc::text(header));

    for op in operations {
        parts.push(Doc::hardline());
        if !op.doc.is_empty() {
            parts.push(format_doc_comment(&op.doc));
            parts.push(Doc::hardline());
        }
        parts.push(Doc::text(format!("  fun {} : ", op.name)));
        parts.push(format_fun_type(&op.params, &op.return_type, &[], &None));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

fn format_trait_def(
    doc: &[String], public: bool, name: &str, type_param: &str,
    supertraits: &[(String, Span)], methods: &[TraitMethod],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("trait ");
    header.push_str(name);
    header.push(' ');
    header.push_str(type_param);
    parts.push(Doc::text(header));

    if !supertraits.is_empty() {
        let st_names: Vec<&str> = supertraits.iter().map(|(n, _): &(String, Span)| n.as_str()).collect();
        parts.push(Doc::text(format!(" where {{{}: {}}}", type_param, st_names.join(" + "))));
    }

    parts.push(Doc::text(" {"));

    for method in methods {
        parts.push(Doc::hardline());
        if !method.doc.is_empty() {
            parts.push(format_doc_comment(&method.doc));
            parts.push(Doc::hardline());
        }
        parts.push(Doc::text(format!("  fun {} : ", method.name)));
        parts.push(format_fun_type(&method.params, &method.return_type, &[], &None));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

#[allow(clippy::too_many_arguments)]
fn format_handler_def(
    doc: &[String], public: bool, name: &str,
    effects: &[EffectRef], needs: &[EffectRef], where_clause: &[TraitBound],
    arms: &[HandlerArm], return_clause: &Option<Box<HandlerArm>>,
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("handler ");
    header.push_str(name);
    header.push_str(" for ");
    let eff_strs: Vec<String> = effects.iter().map(format_effect_ref_str).collect();
    header.push_str(&eff_strs.join(", "));
    parts.push(Doc::text(header));

    if !needs.is_empty() {
        let need_strs: Vec<String> = needs.iter().map(format_effect_ref_str).collect();
        parts.push(Doc::text(format!(" needs {{{}}}", need_strs.join(", "))));
    }
    if !where_clause.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(format_where_clause(where_clause));
    }

    parts.push(Doc::text(" {"));

    for arm in arms {
        parts.push(Doc::hardline());
        parts.push(format_handler_arm(arm));
    }
    if let Some(rc) = return_clause {
        parts.push(Doc::hardline());
        parts.push(format_handler_arm(rc));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

fn format_handler_arm(arm: &HandlerArm) -> Doc {
    let mut d = Doc::text(format!("  {}", arm.op_name));
    for (param, _) in &arm.params {
        d = d.append(Doc::text(format!(" {}", param)));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(&arm.body));
    d
}

fn format_impl_def(
    doc: &[String], trait_name: &str, target_type: &str,
    type_params: &[String], where_clause: &[TraitBound], needs: &[EffectRef],
    methods: &[(String, Span, Vec<Pat>, Expr)],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = format!("impl {} for {}", trait_name, target_type);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }
    parts.push(Doc::text(header));

    if !needs.is_empty() {
        let need_strs: Vec<String> = needs.iter().map(format_effect_ref_str).collect();
        parts.push(Doc::text(format!(" needs {{{}}}", need_strs.join(", "))));
    }
    if !where_clause.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(format_where_clause(where_clause));
    }

    parts.push(Doc::text(" {"));

    for (method_name, _, params, body) in methods {
        parts.push(Doc::hardline());
        parts.push(format_fun_binding(method_name, params, &None, body));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

// =============================================================================
// Type expressions
// =============================================================================

fn format_type_expr(ty: &TypeExpr) -> Doc {
    match ty {
        TypeExpr::Named { name, .. } => Doc::text(name),
        TypeExpr::Var { name, .. } => Doc::text(name),
        TypeExpr::App { func, arg, .. } => {
            let arg_doc = match arg.as_ref() {
                // Parenthesize nested applications in arg position
                TypeExpr::App { .. } => docs![Doc::text("("), format_type_expr(arg), Doc::text(")")],
                _ => format_type_expr(arg),
            };
            docs![format_type_expr(func), Doc::text(" "), arg_doc]
        }
        TypeExpr::Arrow { from, to, effects, effect_row_var, .. } => {
            let from_doc = match from.as_ref() {
                // Parenthesize arrow types on the left of another arrow
                TypeExpr::Arrow { .. } => docs![Doc::text("("), format_type_expr(from), Doc::text(")")],
                _ => format_type_expr(from),
            };
            let mut d = docs![from_doc, Doc::text(" -> "), format_type_expr(to)];
            if !effects.is_empty() || effect_row_var.is_some() {
                d = d.append(Doc::text(" needs {"));
                let mut eff_parts: Vec<String> = effects.iter().map(format_effect_ref_str).collect();
                if let Some((var, _)) = effect_row_var {
                    eff_parts.push(format!("..{}", var));
                }
                d = d.append(Doc::text(eff_parts.join(", "))).append(Doc::text("}"));
            }
            d
        }
        TypeExpr::Record { fields, .. } => {
            let field_docs: Vec<Doc> = fields.iter().map(|(name, ty)| {
                docs![Doc::text(format!("{}: ", name)), format_type_expr(ty)]
            }).collect();
            docs![Doc::text("{ "), Doc::join(Doc::text(", "), field_docs), Doc::text(" }")]
        }
    }
}

/// Format a function type signature: params -> return_type [needs {...}]
fn format_fun_type(
    params: &[(String, TypeExpr)], return_type: &TypeExpr,
    effects: &[EffectRef], effect_row_var: &Option<(String, Span)>,
) -> Doc {
    let mut parts: Vec<Doc> = params.iter().map(|(label, ty)| {
        if label.starts_with('_') {
            format_type_expr(ty)
        } else {
            docs![Doc::text(format!("({}: ", label)), format_type_expr(ty), Doc::text(")")]
        }
    }).collect();
    parts.push(format_type_expr(return_type));

    let mut d = Doc::join(Doc::text(" -> "), parts);

    if !effects.is_empty() || effect_row_var.is_some() {
        d = d.append(Doc::text(" needs {"));
        let mut eff_parts: Vec<String> = effects.iter().map(format_effect_ref_str).collect();
        if let Some((var, _)) = effect_row_var {
            eff_parts.push(format!("..{}", var));
        }
        d = d.append(Doc::text(eff_parts.join(", "))).append(Doc::text("}"));
    }
    d
}

fn format_effect_ref_str(e: &EffectRef) -> String {
    if e.type_args.is_empty() {
        e.name.clone()
    } else {
        let args: Vec<String> = e.type_args.iter().map(format_type_expr_str).collect();
        format!("{} {}", e.name, args.join(" "))
    }
}

/// Simple string-based type formatting (for contexts where we need a String, not a Doc).
fn format_type_expr_str(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::App { func, arg, .. } => {
            let arg_str = match arg.as_ref() {
                TypeExpr::App { .. } | TypeExpr::Arrow { .. } => format!("({})", format_type_expr_str(arg)),
                _ => format_type_expr_str(arg),
            };
            format!("{} {}", format_type_expr_str(func), arg_str)
        }
        TypeExpr::Arrow { from, to, .. } => {
            format!("{} -> {}", format_type_expr_str(from), format_type_expr_str(to))
        }
        TypeExpr::Record { fields, .. } => {
            let fs: Vec<String> = fields.iter()
                .map(|(n, t)| format!("{}: {}", n, format_type_expr_str(t)))
                .collect();
            format!("{{ {} }}", fs.join(", "))
        }
    }
}

fn format_where_clause(bounds: &[TraitBound]) -> Doc {
    let bound_strs: Vec<String> = bounds.iter().map(|b| {
        let traits: Vec<&str> = b.traits.iter().map(|(n, _)| n.as_str()).collect();
        format!("{}: {}", b.type_var, traits.join(" + "))
    }).collect();
    Doc::text(format!("where {{{}}}", bound_strs.join(", ")))
}

// =============================================================================
// Expressions
// =============================================================================

fn format_expr(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { value } => format_lit(value),
        ExprKind::Var { name } => Doc::text(name),
        ExprKind::Constructor { name } => Doc::text(name),
        ExprKind::QualifiedName { module, name } => Doc::text(format!("{}.{}", module, name)),

        ExprKind::App { func, arg } => {
            let func_doc = format_expr(func);
            let arg_doc = match &arg.kind {
                // Parenthesize applications and binops in arg position
                ExprKind::App { .. } | ExprKind::BinOp { .. } => {
                    docs![Doc::text("("), format_expr(arg), Doc::text(")")]
                }
                _ => format_expr(arg),
            };
            docs![func_doc, Doc::text(" "), arg_doc]
        }

        ExprKind::BinOp { op, left, right } => {
            let op_str = format_binop(op);
            docs![format_expr(left), Doc::text(format!(" {} ", op_str)), format_expr(right)]
        }

        ExprKind::UnaryMinus { expr } => {
            docs![Doc::text("-"), format_expr(expr)]
        }

        ExprKind::If { cond, then_branch, else_branch } => {
            docs![
                Doc::text("if "),
                format_expr(cond),
                Doc::text(" then "),
                format_expr(then_branch),
                Doc::hardline(),
                Doc::text("else "),
                format_expr(else_branch),
            ]
        }

        ExprKind::Case { scrutinee, arms } => {
            let mut parts = vec![
                Doc::text("case "),
                format_expr(scrutinee),
                Doc::text(" {"),
            ];
            for arm in arms {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  "));
                parts.push(format_pat(&arm.pattern));
                if let Some(g) = &arm.guard {
                    parts.push(Doc::text(" | "));
                    parts.push(format_expr(g));
                }
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(&arm.body));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }

        ExprKind::Block { stmts } => {
            if stmts.len() == 1 && let Stmt::Expr(e) = &stmts[0] {
                return format_expr(e);
            }
            let mut parts = vec![Doc::text("{")];
            for stmt in stmts {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  "));
                parts.push(format_stmt(stmt));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }

        ExprKind::Lambda { params, body } => {
            let mut d = Doc::text("fun ");
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    d = d.append(Doc::text(" "));
                }
                d = d.append(format_pat(p));
            }
            d = d.append(Doc::text(" -> ")).append(format_expr(body));
            d
        }

        ExprKind::FieldAccess { expr, field } => {
            docs![format_expr(expr), Doc::text(format!(".{}", field))]
        }

        ExprKind::RecordCreate { name, fields } => {
            format_record_create(Some(name), fields)
        }
        ExprKind::AnonRecordCreate { fields } => {
            format_record_create(None, fields)
        }

        ExprKind::RecordUpdate { record, fields } => {
            let field_docs: Vec<Doc> = fields.iter().map(|(name, _, val)| {
                docs![Doc::text(format!("{}: ", name)), format_expr(val)]
            }).collect();
            Doc::group(docs![
                Doc::text("{ "),
                format_expr(record),
                Doc::text(" | "),
                Doc::join(Doc::text(", "), field_docs),
                Doc::text(" }"),
            ])
        }

        ExprKind::EffectCall { name, qualifier, args } => {
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
            docs![expr_doc, Doc::text(" with "), handler_doc]
        }

        ExprKind::Resume { value } => {
            docs![Doc::text("resume "), format_expr(value)]
        }

        ExprKind::Tuple { elements } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_expr).collect();
            docs![Doc::text("("), Doc::join(Doc::text(", "), elem_docs), Doc::text(")")]
        }

        ExprKind::Do { bindings, success, else_arms } => {
            let mut parts = vec![Doc::text("do {")];
            for (pat, expr) in bindings {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  "));
                parts.push(format_pat(pat));
                parts.push(Doc::text(" <- "));
                parts.push(format_expr(expr));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("  "));
            parts.push(format_expr(success));
            parts.push(Doc::hardline());
            parts.push(Doc::text("} else {"));
            for arm in else_arms {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  "));
                parts.push(format_pat(&arm.pattern));
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(&arm.body));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }

        ExprKind::Receive { arms, after_clause } => {
            let mut parts = vec![Doc::text("receive {")];
            for arm in arms {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  "));
                parts.push(format_pat(&arm.pattern));
                if let Some(g) = &arm.guard {
                    parts.push(Doc::text(" | "));
                    parts.push(format_expr(g));
                }
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(&arm.body));
            }
            if let Some((timeout, body)) = after_clause {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  after "));
                parts.push(format_expr(timeout));
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(body));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }

        ExprKind::Ascription { expr, type_expr } => {
            docs![Doc::text("("), format_expr(expr), Doc::text(" : "), format_type_expr(type_expr), Doc::text(")")]
        }

        // Elaboration-only -- shouldn't appear in formatter input
        ExprKind::DictMethodAccess { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::ForeignCall { .. } => Doc::text("<elaboration-only>"),
    }
}

/// Format an expression in "atom" position (parenthesize if complex).
fn format_expr_atom(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::Tuple { .. }
        | ExprKind::Block { .. } => format_expr(expr),
        _ => docs![Doc::text("("), format_expr(expr), Doc::text(")")],
    }
}

fn format_record_create(name: Option<&String>, fields: &[(String, Span, Expr)]) -> Doc {
    let field_docs: Vec<Doc> = fields.iter().map(|(fname, _, val)| {
        docs![Doc::text(format!("{}: ", fname)), format_expr(val)]
    }).collect();
    let mut d = match name {
        Some(n) => Doc::text(format!("{} {{ ", n)),
        None => Doc::text("{ "),
    };
    d = d.append(Doc::join(Doc::text(", "), field_docs));
    d.append(Doc::text(" }"))
}

fn format_handler(handler: &Handler) -> Doc {
    match handler {
        Handler::Named(name, _) => Doc::text(name),
        Handler::Inline { named, arms, return_clause, .. } => {
            let mut parts = vec![Doc::text("{")];
            for name in named {
                parts.push(Doc::hardline());
                parts.push(Doc::text(format!("  {},", name)));
            }
            for arm in arms {
                parts.push(Doc::hardline());
                parts.push(format_handler_arm(arm));
                parts.push(Doc::text(","));
            }
            if let Some(rc) = return_clause {
                parts.push(Doc::hardline());
                parts.push(format_handler_arm(rc));
                parts.push(Doc::text(","));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }
    }
}

// =============================================================================
// Statements
// =============================================================================

fn format_stmt(stmt: &Stmt) -> Doc {
    match stmt {
        Stmt::Let { pattern, annotation, value, assert, .. } => {
            let kw = if *assert { "let! " } else { "let " };
            let mut d = Doc::text(kw).append(format_pat(pattern));
            if let Some(ty) = annotation {
                d = d.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            d.append(Doc::text(" = ")).append(format_expr(value))
        }
        Stmt::LetFun { name, params, guard, body, .. } => {
            let mut d = Doc::text(format!("let {}", name));
            for p in params {
                d = d.append(Doc::text(" ")).append(format_pat(p));
            }
            if let Some(g) = guard {
                d = d.append(Doc::text(" | ")).append(format_expr(g));
            }
            d.append(Doc::text(" = ")).append(format_expr(body))
        }
        Stmt::Expr(expr) => format_expr(expr),
    }
}

// =============================================================================
// Patterns
// =============================================================================

fn format_pat(pat: &Pat) -> Doc {
    match pat {
        Pat::Wildcard { .. } => Doc::text("_"),
        Pat::Var { name, .. } => Doc::text(name),
        Pat::Lit { value, .. } => format_lit(value),
        Pat::Constructor { name, args, .. } => {
            if args.is_empty() {
                Doc::text(name)
            } else {
                let arg_docs: Vec<Doc> = args.iter().map(format_pat).collect();
                docs![Doc::text(format!("{}(", name)), Doc::join(Doc::text(", "), arg_docs), Doc::text(")")]
            }
        }
        Pat::Record { name, fields, as_name, .. } => {
            let field_docs: Vec<Doc> = fields.iter().map(|(fname, alias)| {
                match alias {
                    Some(p) => docs![Doc::text(format!("{}: ", fname)), format_pat(p)],
                    None => Doc::text(fname),
                }
            }).collect();
            let mut d = docs![Doc::text(format!("{} {{ ", name)), Doc::join(Doc::text(", "), field_docs), Doc::text(" }")];
            if let Some(a) = as_name {
                d = d.append(Doc::text(format!(" as {}", a)));
            }
            d
        }
        Pat::AnonRecord { fields, .. } => {
            let field_docs: Vec<Doc> = fields.iter().map(|(fname, alias)| {
                match alias {
                    Some(p) => docs![Doc::text(format!("{}: ", fname)), format_pat(p)],
                    None => Doc::text(fname),
                }
            }).collect();
            docs![Doc::text("{ "), Doc::join(Doc::text(", "), field_docs), Doc::text(" }")]
        }
        Pat::Tuple { elements, .. } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_pat).collect();
            docs![Doc::text("("), Doc::join(Doc::text(", "), elem_docs), Doc::text(")")]
        }
        Pat::StringPrefix { prefix, rest, .. } => {
            docs![Doc::text(format!("\"{}\" <> ", prefix)), format_pat(rest)]
        }
    }
}

// =============================================================================
// Literals
// =============================================================================

fn format_lit(lit: &Lit) -> Doc {
    Doc::text(format_lit_raw(lit))
}

fn format_lit_raw(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => n.to_string(),
        Lit::Float(f) => format!("{}", f),
        Lit::String(s) => format!("\"{}\"", s),
        Lit::Bool(true) => "True".to_string(),
        Lit::Bool(false) => "False".to_string(),
        Lit::Unit => "()".to_string(),
    }
}

fn format_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::FloatDiv | BinOp::IntDiv => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "==",
        BinOp::NotEq => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::LtEq => "<=",
        BinOp::GtEq => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Concat => "<>",
    }
}

fn format_doc_comment(doc: &[String]) -> Doc {
    let lines: Vec<Doc> = doc.iter().map(|line| Doc::text(format!("#@ {}", line))).collect();
    Doc::join(Doc::hardline(), lines)
}

// =============================================================================
// Helpers
// =============================================================================

/// Concatenate a Vec<Doc> into a single Doc.
fn docs_from_vec(docs: Vec<Doc>) -> Doc {
    let mut result = Doc::Nil;
    for d in docs {
        result = result.append(d);
    }
    result
}
