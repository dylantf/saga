use dylang::ast::{Decl, EffectRef, Expr, ExprKind, NodeId, Pat, Stmt, TypeExpr};
use dylang::token::Span;
use dylang::typechecker::CheckResult;

/// Find the name, span, and optional NodeId of the identifier at the given byte offset.
/// Returns `Some(node_id)` for Expr nodes, `None` for Pat bindings.
pub fn find_name_at_offset(
    program: &[Decl],
    offset: usize,
) -> Option<(String, Span, Option<NodeId>)> {
    for decl in program {
        if let Some(result) = find_in_decl(decl, offset) {
            return Some(result);
        }
    }
    None
}

fn contains(span: &Span, offset: usize) -> bool {
    offset >= span.start && offset < span.end
}

/// Like `contains` but inclusive of the end position. Used for leaf identifiers
/// where the cursor right after the last character is still "on" the name.
fn contains_ident(span: &Span, offset: usize) -> bool {
    offset >= span.start && offset <= span.end
}

fn find_in_decl(decl: &Decl, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    match decl {
        Decl::FunBinding {
            name,
            name_span,
            params,
            body,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for pat in params {
                if let Some(r) = find_in_pat(pat, offset) {
                    return Some(r);
                }
            }
            if let Some(r) = find_in_expr(body, offset) {
                return Some(r);
            }
            if contains_ident(name_span, offset) {
                return Some((name.clone(), *name_span, None));
            }
            None
        }
        Decl::FunAnnotation { name, name_span, params, return_type, effects, span, .. } if contains(span, offset) => {
            if contains_ident(name_span, offset) {
                return Some((name.clone(), *name_span, None));
            }
            for (_, ty) in params {
                if let Some(r) = find_in_type_expr(ty, offset) {
                    return Some(r);
                }
            }
            if let Some(r) = find_in_type_expr(return_type, offset) {
                return Some(r);
            }
            for eff in effects {
                if let Some(r) = find_in_effect_ref(eff, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::HandlerDef {
            name,
            name_span,
            effects,
            arms,
            recovered_arms,
            return_clause,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for arm in arms.iter().chain(recovered_arms.iter()) {
                if contains(&arm.span, offset) {
                    // Check if cursor is on the op name (first token of the arm)
                    let op_name_end = arm.span.start + arm.op_name.len();
                    if offset >= arm.span.start && offset <= op_name_end {
                        return Some((arm.op_name.clone(), Span { start: arm.span.start, end: op_name_end }, None));
                    }
                }
                if let Some(r) = find_in_expr(&arm.body, offset) {
                    return Some(r);
                }
            }
            if let Some(rc) = return_clause
                && let Some(r) = find_in_expr(&rc.body, offset)
            {
                return Some(r);
            }
            // Check effect refs in `for Effect1, Effect2`
            for eff in effects {
                if let Some(r) = find_in_effect_ref(eff, offset) {
                    return Some(r);
                }
            }
            // Check if cursor is on the handler name
            if offset >= name_span.start && offset <= name_span.end {
                return Some((name.clone(), *name_span, None));
            }
            None
        }
        Decl::ImplDef { methods, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            for (_, params, body) in methods {
                for pat in params {
                    if let Some(r) = find_in_pat(pat, offset) {
                        return Some(r);
                    }
                }
                if let Some(r) = find_in_expr(body, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::Let {
            name, value, span, ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            if let Some(r) = find_in_expr(value, offset) {
                return Some(r);
            }
            // Only return the name if cursor is in the name region (after "let ")
            let name_start = span.start + 4; // "let "
            if offset >= name_start && offset <= name_start + name.len() {
                return Some((name.clone(), *span, None));
            }
            None
        }
        Decl::EffectDef { operations, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            for op in operations {
                if contains(&op.span, offset) {
                    for (_, ty) in &op.params {
                        if let Some(r) = find_in_type_expr(ty, offset) {
                            return Some(r);
                        }
                    }
                    if let Some(r) = find_in_type_expr(&op.return_type, offset) {
                        return Some(r);
                    }
                }
            }
            None
        }
        Decl::RecordDef { fields, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            for (_, ty) in fields {
                if let Some(r) = find_in_type_expr(ty, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::TraitDef { methods, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            for method in methods {
                if contains(&method.span, offset) {
                    for (_, ty) in &method.params {
                        if let Some(r) = find_in_type_expr(ty, offset) {
                            return Some(r);
                        }
                    }
                    if let Some(r) = find_in_type_expr(&method.return_type, offset) {
                        return Some(r);
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn find_in_expr(expr: &Expr, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    // Quick span check: skip if cursor is outside this expression
    if !contains(&expr.span, offset) {
        return None;
    }

    let span = expr.span;
    let node_id = expr.id;
    match &expr.kind {
        ExprKind::Var { name } if contains_ident(&span, offset) => {
            Some((name.clone(), span, Some(node_id)))
        }
        ExprKind::Constructor { name }
            if contains_ident(&span, offset) && name != "Cons" && name != "Nil" =>
        {
            Some((name.clone(), span, Some(node_id)))
        }
        ExprKind::QualifiedName { module, name } => {
            // The span covers "Module.name". The dot separates them.
            // module part: span.start .. span.start + module.len()
            // name part:   span.start + module.len() + 1 .. span.end
            let dot_offset = span.start + module.len();
            if offset <= dot_offset {
                Some((format!("module:{}", module), span, Some(node_id)))
            } else {
                Some((name.clone(), span, Some(node_id)))
            }
        }
        ExprKind::App { func, arg, .. } => {
            find_in_expr(func, offset).or_else(|| find_in_expr(arg, offset))
        }
        ExprKind::BinOp { left, right, .. } => {
            find_in_expr(left, offset).or_else(|| find_in_expr(right, offset))
        }
        ExprKind::UnaryMinus { expr, .. } => find_in_expr(expr, offset),
        ExprKind::Lambda { params, body, .. } => {
            for pat in params {
                if let Some(r) = find_in_pat(pat, offset) {
                    return Some(r);
                }
            }
            find_in_expr(body, offset)
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                if let Some(r) = find_in_stmt(stmt, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_in_expr(cond, offset)
            .or_else(|| find_in_expr(then_branch, offset))
            .or_else(|| find_in_expr(else_branch, offset)),
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            if let Some(r) = find_in_expr(scrutinee, offset) {
                return Some(r);
            }
            for arm in arms {
                if let Some(r) = find_in_pat(&arm.pattern, offset) {
                    return Some(r);
                }
                if let Some(guard) = &arm.guard
                    && let Some(r) = find_in_expr(guard, offset)
                {
                    return Some(r);
                }
                if let Some(r) = find_in_expr(&arm.body, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::Tuple { elements, .. } => {
            for e in elements {
                if let Some(r) = find_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::RecordCreate { fields, .. } => {
            for (_, _, e) in fields {
                if let Some(r) = find_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            if let Some(r) = find_in_expr(record, offset) {
                return Some(r);
            }
            for (_, _, e) in fields {
                if let Some(r) = find_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::FieldAccess { expr, .. } => find_in_expr(expr, offset),
        ExprKind::With { expr, handler, .. } => {
            match handler.as_ref() {
                dylang::ast::Handler::Named(name, span) if contains(span, offset) => {
                    return Some((name.clone(), *span, None));
                }
                dylang::ast::Handler::Inline {
                    arms,
                    return_clause,
                    ..
                } => {
                    for arm in arms.iter().chain(return_clause.iter().map(|r| r.as_ref())) {
                        if contains(&arm.span, offset) {
                            let body_span = arm.body.span;
                            if contains(&body_span, offset) {
                                return find_in_expr(&arm.body, offset);
                            }
                            // Cursor is on the op name / params, before the arrow.
                            // Return the arm span so goto-def can look it up in handler_arm_targets.
                            return Some((arm.op_name.clone(), arm.span, None));
                        }
                    }
                }
                _ => {}
            }
            find_in_expr(expr, offset)
        }
        ExprKind::Resume { value, .. } => find_in_expr(value, offset),
        ExprKind::EffectCall { name, args, .. } => {
            if contains(&span, offset) {
                // Check if cursor is on the effect name itself
                // Return the effect op name for lookup
                return Some((name.clone(), span, Some(node_id)));
            }
            for arg in args {
                if let Some(r) = find_in_expr(arg, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pat, expr) in bindings {
                if let Some(r) = find_in_pat(pat, offset) {
                    return Some(r);
                }
                if let Some(r) = find_in_expr(expr, offset) {
                    return Some(r);
                }
            }
            if let Some(r) = find_in_expr(success, offset) {
                return Some(r);
            }
            for arm in else_arms {
                if let Some(r) = find_in_pat(&arm.pattern, offset) {
                    return Some(r);
                }
                if let Some(r) = find_in_expr(&arm.body, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                if let Some(r) = find_in_pat(&arm.pattern, offset) {
                    return Some(r);
                }
                if let Some(guard) = &arm.guard
                    && let Some(r) = find_in_expr(guard, offset)
                {
                    return Some(r);
                }
                if let Some(r) = find_in_expr(&arm.body, offset) {
                    return Some(r);
                }
            }
            if let Some((timeout_expr, timeout_body)) = after_clause {
                if let Some(r) = find_in_expr(timeout_expr, offset) {
                    return Some(r);
                }
                if let Some(r) = find_in_expr(timeout_body, offset) {
                    return Some(r);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_in_stmt(stmt: &Stmt, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    match stmt {
        Stmt::Let { pattern, value, .. } => {
            find_in_pat(pattern, offset).or_else(|| find_in_expr(value, offset))
        }
        Stmt::LetFun {
            id,
            name,
            name_span,
            params,
            body,
            ..
        } => {
            for pat in params {
                if let Some(r) = find_in_pat(pat, offset) {
                    return Some(r);
                }
            }
            if let Some(r) = find_in_expr(body, offset) {
                return Some(r);
            }
            if contains_ident(name_span, offset) {
                return Some((name.clone(), *name_span, Some(*id)));
            }
            None
        }
        Stmt::Expr(expr) => find_in_expr(expr, offset),
    }
}

fn find_in_pat(pat: &Pat, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    match pat {
        Pat::Var { id, name, span } if contains_ident(span, offset) => {
            Some((name.clone(), *span, Some(*id)))
        }
        Pat::Constructor { args, .. } => {
            for arg in args {
                if let Some(r) = find_in_pat(arg, offset) {
                    return Some(r);
                }
            }
            None
        }
        Pat::Tuple { elements, .. } => {
            for e in elements {
                if let Some(r) = find_in_pat(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        Pat::StringPrefix { rest, .. } => find_in_pat(rest, offset),
        Pat::Record { fields, .. } => {
            for (_, alias) in fields {
                if let Some(pat) = alias
                    && let Some(r) = find_in_pat(pat, offset)
                {
                    return Some(r);
                }
            }
            None
        }
        _ => None,
    }
}

/// Look up the type of a name in the checker's environment.
/// At usage sites (node_id present), prefer the resolved/instantiated type.
/// At definition sites (no node_id), prefer the annotation (includes labels).
pub fn type_at_name(
    result: &CheckResult,
    name: &str,
    span: Option<&Span>,
    node_id: Option<&NodeId>,
    program: &[Decl],
) -> Option<String> {
    // Check node-based type map first (Expr nodes at usage sites get resolved types)
    if let Some(id) = node_id
        && let Some(ty_str) = result.type_at_node(id)
    {
        // Graft annotation labels onto the resolved type if available
        if let Some(labels) = annotation_labels(program, name) {
            return Some(labeled_type(&labels, &ty_str));
        }
        return Some(ty_str);
    }

    // Check span-based type map (Pat bindings)
    if let Some(span) = span
        && let Some(ty_str) = result.type_at_span(span)
    {
        return Some(ty_str);
    }

    // Check for a FunAnnotation (has labeled params, good for definitions)
    if let Some(sig) = find_annotation(program, name) {
        return Some(sig);
    }

    // Check env (functions, variables)
    if let Some(scheme) = result.env.get(name) {
        return Some(scheme.display_with_constraints(&result.sub));
    }

    // Check constructors
    if let Some(scheme) = result.constructors.get(name) {
        return Some(scheme.display_with_constraints(&result.sub));
    }

    None
}

/// Get just the parameter labels from a FunAnnotation.
/// Returns None if no annotation exists or if no params have real labels.
pub(crate) fn annotation_labels(program: &[Decl], name: &str) -> Option<Vec<String>> {
    for decl in program {
        if let Decl::FunAnnotation {
            name: fn_name,
            params,
            ..
        } = decl
            && fn_name == name
        {
            let labels: Vec<String> = params.iter().map(|(label, _)| label.clone()).collect();
            // Only return labels if at least one is a real (non-synthetic) label
            if labels.iter().any(|l| !l.starts_with('_')) {
                return Some(labels);
            }
            return None;
        }
    }
    None
}

/// Graft parameter labels onto a resolved type string.
/// E.g., labels=["a", "b"], type_str="Int -> Int -> String" => "(a: Int) (b: Int) -> String"
fn labeled_type(labels: &[String], type_str: &str) -> String {
    let parts: Vec<&str> = type_str.splitn(labels.len() + 1, " -> ").collect();
    if parts.len() <= labels.len() {
        return type_str.to_string();
    }
    let labeled: Vec<String> = labels
        .iter()
        .zip(parts.iter())
        .map(|(label, ty)| {
            if label.starts_with('_') {
                ty.to_string()
            } else {
                format!("({}: {})", label, ty)
            }
        })
        .collect();
    let rest = parts[labels.len()..].join(" -> ");
    format!("{} -> {}", labeled.join(" -> "), rest)
}

/// Find a FunAnnotation for the given name and format it with labels.
pub(crate) fn find_annotation(program: &[Decl], name: &str) -> Option<String> {
    for decl in program {
        if let Decl::FunAnnotation {
            name: fn_name,
            params,
            return_type,
            effects,
            ..
        } = decl
            && fn_name == name
        {
            let params_str: Vec<String> = params
                .iter()
                .map(|(label, ty)| {
                    if label.starts_with('_') {
                        format_type_expr(ty)
                    } else {
                        format!("({}: {})", label, format_type_expr(ty))
                    }
                })
                .collect();
            let mut sig = if params_str.is_empty() {
                format_type_expr(return_type)
            } else {
                format!(
                    "{} -> {}",
                    params_str.join(" -> "),
                    format_type_expr(return_type)
                )
            };
            if !effects.is_empty() {
                let effs: Vec<String> = effects
                    .iter()
                    .map(|e| {
                        if e.type_args.is_empty() {
                            e.name.clone()
                        } else {
                            let args: Vec<String> =
                                e.type_args.iter().map(format_type_expr).collect();
                            format!("{} {}", e.name, args.join(" "))
                        }
                    })
                    .collect();
                sig.push_str(&format!(" needs {{{}}}", effs.join(", ")));
            }
            return Some(sig);
        }
    }
    None
}

/// Find a type name at the given offset within a TypeExpr tree.
fn find_in_type_expr(ty: &TypeExpr, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    match ty {
        TypeExpr::Named { name, span } => {
            if offset >= span.start && offset <= span.end {
                Some((name.clone(), *span, None))
            } else {
                None
            }
        }
        TypeExpr::App { func, arg, span, .. } => {
            if offset < span.start || offset > span.end {
                return None;
            }
            find_in_type_expr(func, offset).or_else(|| find_in_type_expr(arg, offset))
        }
        TypeExpr::Arrow { from, to, effects, span } => {
            if offset < span.start || offset > span.end {
                return None;
            }
            find_in_type_expr(from, offset)
                .or_else(|| find_in_type_expr(to, offset))
                .or_else(|| {
                    for eff in effects {
                        if let Some(r) = find_in_effect_ref(eff, offset) {
                            return Some(r);
                        }
                    }
                    None
                })
        }
        TypeExpr::Record { fields, span } => {
            if offset < span.start || offset > span.end {
                return None;
            }
            for (_, ty) in fields {
                if let Some(r) = find_in_type_expr(ty, offset) {
                    return Some(r);
                }
            }
            None
        }
        TypeExpr::Var { .. } => None,
    }
}

/// Find a type/effect name at the given offset within an EffectRef.
fn find_in_effect_ref(eff: &EffectRef, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    if offset < eff.span.start || offset > eff.span.end {
        return None;
    }
    // Check the effect name itself (before any type args)
    let name_end = eff.span.start + eff.name.len();
    if offset >= eff.span.start && offset <= name_end {
        return Some((eff.name.clone(), Span { start: eff.span.start, end: name_end }, None));
    }
    // Check type args
    for arg in &eff.type_args {
        if let Some(r) = find_in_type_expr(arg, offset) {
            return Some(r);
        }
    }
    None
}

pub(crate) fn format_type_expr(ty: &dylang::ast::TypeExpr) -> String {
    use dylang::ast::TypeExpr;
    match ty {
        TypeExpr::Named { name, .. } => name.clone(),
        TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::App { func, arg, .. } => format!("{} {}", format_type_expr(func), format_type_expr(arg)),
        TypeExpr::Arrow { from, to, effects, .. } => {
            let arrow = format!("{} -> {}", format_type_expr(from), format_type_expr(to));
            if effects.is_empty() {
                arrow
            } else {
                let effs_str: Vec<String> = effects
                    .iter()
                    .map(|e| {
                        if e.type_args.is_empty() {
                            e.name.clone()
                        } else {
                            let args: Vec<String> =
                                e.type_args.iter().map(format_type_expr).collect();
                            format!("{} {}", e.name, args.join(" "))
                        }
                    })
                    .collect();
                format!("{} needs {{{}}}", arrow, effs_str.join(", "))
            }
        }
        TypeExpr::Record { fields, .. } => {
            let field_strs: Vec<String> = fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", name, format_type_expr(ty)))
                .collect();
            format!("{{ {} }}", field_strs.join(", "))
        }
    }
}
