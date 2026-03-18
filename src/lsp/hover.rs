use dylang::ast::{Decl, Expr, ExprKind, NodeId, Pat, Stmt};
use dylang::token::Span;
use dylang::typechecker::CheckResult;

/// Find the name, span, and optional NodeId of the identifier at the given byte offset.
/// Returns `Some(node_id)` for Expr nodes, `None` for Pat bindings.
pub fn find_name_at_offset(program: &[Decl], offset: usize) -> Option<(String, Span, Option<NodeId>)> {
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

fn find_in_decl(decl: &Decl, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    match decl {
        Decl::FunBinding {
            params, body, span, ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for pat in params {
                if let Some(r) = find_in_pat(pat, offset) {
                    return Some(r);
                }
            }
            find_in_expr(body, offset)
        }
        Decl::FunAnnotation { name, span, .. } if contains(span, offset) => {
            Some((name.clone(), *span, None))
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
        Decl::Let { value, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            find_in_expr(value, offset)
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
        ExprKind::Var { name } if contains(&span, offset) => Some((name.clone(), span, Some(node_id))),
        ExprKind::Constructor { name }
            if contains(&span, offset) && name != "Cons" && name != "Nil" =>
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
            for (_, e) in fields {
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
            for (_, e) in fields {
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
                dylang::ast::Handler::Inline { arms, return_clause, .. } => {
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
        ExprKind::EffectCall {
            name, args, ..
        } => {
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
        Stmt::LetFun { params, body, .. } => {
            for pat in params {
                if let Some(r) = find_in_pat(pat, offset) {
                    return Some(r);
                }
            }
            find_in_expr(body, offset)
        }
        Stmt::Expr(expr) => find_in_expr(expr, offset),
    }
}

fn find_in_pat(pat: &Pat, offset: usize) -> Option<(String, Span, Option<NodeId>)> {
    match pat {
        Pat::Var { name, span } if contains(span, offset) => Some((name.clone(), *span, None)),
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
/// If a FunAnnotation exists for the name, prefer it (includes labels).
pub fn type_at_name(
    result: &CheckResult,
    name: &str,
    span: Option<&Span>,
    node_id: Option<&NodeId>,
    program: &[Decl],
) -> Option<String> {
    // Check for a FunAnnotation first (has labeled params)
    if let Some(sig) = find_annotation(program, name) {
        return Some(sig);
    }

    // Check node-based type map (Expr nodes)
    if let Some(id) = node_id
        && let Some(ty_str) = result.type_at_node(id)
    {
        return Some(ty_str);
    }

    // Check span-based type map (Pat bindings)
    if let Some(span) = span
        && let Some(ty_str) = result.type_at_span(span)
    {
        return Some(ty_str);
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

/// Find a FunAnnotation for the given name and format it with labels.
fn find_annotation(program: &[Decl], name: &str) -> Option<String> {
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
                .map(|(label, ty)| format!("({}: {})", label, format_type_expr(ty)))
                .collect();
            let mut sig = format!(
                "{} -> {}",
                params_str.join(" -> "),
                format_type_expr(return_type)
            );
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

fn format_type_expr(ty: &dylang::ast::TypeExpr) -> String {
    use dylang::ast::TypeExpr;
    match ty {
        TypeExpr::Named(n) => n.clone(),
        TypeExpr::Var(v) => v.clone(),
        TypeExpr::App(f, arg) => format!("{} {}", format_type_expr(f), format_type_expr(arg)),
        TypeExpr::Arrow(a, b, effs) => {
            let arrow = format!("{} -> {}", format_type_expr(a), format_type_expr(b));
            if effs.is_empty() {
                arrow
            } else {
                let effs_str: Vec<String> = effs
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
    }
}
