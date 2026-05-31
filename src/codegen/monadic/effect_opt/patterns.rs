use super::*;

pub(super) fn collect_atom_var_names(atom: &Atom, out: &mut HashSet<String>) {
    match atom {
        Atom::Var { name, .. } => {
            out.insert(name.name.clone());
        }
        Atom::Ctor { args, .. } => collect_atom_list_names(args, out),
        Atom::Tuple { elements, .. } => collect_atom_list_names(elements, out),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_var_names(atom, out);
            }
        }
        Atom::Lambda { body, .. } => collect_expr_var_names(body, out),
        Atom::BackendSpawnThunk { callback, .. } => collect_atom_var_names(callback, out),
        Atom::QualifiedRef { name, .. } => {
            // Reachability cleanup uses this collector too. A same-module
            // function may survive in monadic IR as a QualifiedRef, so count
            // the short name conservatively rather than deleting a callee that
            // the lowerer will still emit as a local call.
            out.insert(name.clone());
        }
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

pub(super) fn collect_atom_list_names(atoms: &[Atom], out: &mut HashSet<String>) {
    for atom in atoms {
        collect_atom_var_names(atom, out);
    }
}

pub(super) fn expr_contains_target(expr: &MExpr, target: &MVar) -> bool {
    match expr {
        MExpr::Pure(atom) => atom_contains_target(atom, target),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(|a| atom_contains_target(a, target))
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            expr_contains_target(value, target)
                || ((!var_matches(var, target)) && expr_contains_target(body, target))
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_target(body, target) || expr_contains_target(cleanup, target)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_target(scrutinee, target)
                || arms.iter().any(|arm| {
                    pat_has_nonbinding_ref(&arm.pattern, &target.name)
                        || !pat_binds_name(&arm.pattern, &target.name)
                            && (arm
                                .guard
                                .as_ref()
                                .is_some_and(|g| expr_contains_target(g, target))
                                || expr_contains_target(&arm.body, target))
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_target(cond, target)
                || expr_contains_target(then_branch, target)
                || expr_contains_target(else_branch, target)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_target(head, target)
                || args.iter().any(|a| atom_contains_target(a, target))
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_target(handler, target) || expr_contains_target(body, target)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_target(value, target),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_target(record, target)
                || fields.iter().any(|(_, a)| atom_contains_target(a, target))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_target(left, target) || atom_contains_target(right, target)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_target(&seg.value, target)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| atom_contains_target(size, target))
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                pat_has_nonbinding_ref(&arm.pattern, &target.name)
                    || !pat_binds_name(&arm.pattern, &target.name)
                        && (arm
                            .guard
                            .as_ref()
                            .is_some_and(|g| expr_contains_target(g, target))
                            || expr_contains_target(&arm.body, target))
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_target(timeout, target) || expr_contains_target(body, target)
            })
        }
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            ..
        } => {
            if name == &target.name {
                false
            } else {
                (!pats_bind_name(params, &target.name) && expr_contains_target(body, target))
                    || expr_contains_target(rest, target)
            }
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_contains_target(arm, target))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_target(arm, target))
        }
    }
}

pub(super) fn atom_contains_target(atom: &Atom, target: &MVar) -> bool {
    match atom {
        Atom::Var { name, .. } => var_matches(name, target),
        Atom::Ctor { args, .. } => args.iter().any(|a| atom_contains_target(a, target)),
        Atom::Tuple { elements, .. } => elements.iter().any(|a| atom_contains_target(a, target)),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, a)| atom_contains_target(a, target))
        }
        Atom::Lambda { params, body, .. } => {
            !pats_bind_name(params, &target.name) && expr_contains_target(body, target)
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_target(callback, target),
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

pub(super) fn handler_contains_target(handler: &MHandler, target: &MVar) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_contains_target(arm, target))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_target(arm, target))
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => handlers
            .iter()
            .any(|handler| handler_contains_target(handler, target)),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_target(op_tuple, target)
                || return_lambda
                    .as_ref()
                    .is_some_and(|atom| atom_contains_target(atom, target))
        }
    }
}

pub(super) fn handler_arm_contains_target(arm: &MHandlerArm, target: &MVar) -> bool {
    !pats_bind_name(&arm.params, &target.name)
        && (expr_contains_target(&arm.body, target)
            || arm
                .finally_block
                .as_ref()
                .is_some_and(|f| expr_contains_target(f, target)))
}

pub(super) fn collect_expr_var_names(expr: &MExpr, out: &mut HashSet<String>) {
    match expr {
        MExpr::Pure(atom) => collect_atom_var_names(atom, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_names(args, out)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_expr_var_names(value, out);
            collect_expr_var_names(body, out);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_expr_var_names(body, out);
            collect_expr_var_names(cleanup, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_var_names(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_var_names(guard, out);
                }
                collect_expr_var_names(&arm.body, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_var_names(cond, out);
            collect_expr_var_names(then_branch, out);
            collect_expr_var_names(else_branch, out);
        }
        MExpr::App { head, args, .. } => {
            collect_atom_var_names(head, out);
            collect_atom_list_names(args, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_var_names(handler, out);
            collect_expr_var_names(body, out);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_var_names(value, out),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_var_names(record, out);
            for (_, atom) in fields {
                collect_atom_var_names(atom, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_var_names(left, out);
            collect_atom_var_names(right, out);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_var_names(&seg.value, out);
                if let Some(size) = &seg.size {
                    collect_atom_var_names(size, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_var_names(guard, out);
                }
                collect_expr_var_names(&arm.body, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_var_names(timeout, out);
                collect_expr_var_names(body, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_expr_var_names(body, out);
            collect_expr_var_names(rest, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_var_names(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_var_names(arm, out);
            }
        }
    }
}

pub(super) fn collect_handler_var_names(handler: &MHandler, out: &mut HashSet<String>) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_var_names(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_var_names(arm, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_var_names(handler, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_var_names(op_tuple, out);
            if let Some(atom) = return_lambda {
                collect_atom_var_names(atom, out);
            }
        }
    }
}

pub(super) fn collect_handler_arm_var_names(arm: &MHandlerArm, out: &mut HashSet<String>) {
    collect_expr_var_names(&arm.body, out);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_var_names(finally_block, out);
    }
}

pub(super) fn pats_bind_name(params: &[Pat], name: &str) -> bool {
    params.iter().any(|pat| pat_binds_name(pat, name))
}

pub(super) fn pats_capture_replacement(
    params: &[Pat],
    replacement_free_names: &HashSet<String>,
) -> bool {
    params
        .iter()
        .any(|pat| pat_captures_replacement(pat, replacement_free_names))
}

pub(super) fn pat_captures_replacement(
    pat: &Pat,
    replacement_free_names: &HashSet<String>,
) -> bool {
    pat_bound_names(pat)
        .iter()
        .any(|name| replacement_free_names.contains(name))
}

pub(super) fn pat_binds_name(pat: &Pat, name: &str) -> bool {
    pat_bound_names(pat).iter().any(|bound| bound == name)
}

pub(super) fn pat_bound_names(pat: &Pat) -> Vec<String> {
    let mut out = Vec::new();
    collect_pat_bound_names(pat, &mut out);
    out
}

pub(super) fn bound_names_in_pat(pat: &Pat) -> Vec<String> {
    pat_bound_names(pat)
}

pub(super) fn bound_names_in_pats(pats: &[Pat]) -> Vec<String> {
    pats.iter().flat_map(pat_bound_names).collect()
}

pub(super) fn collect_pat_bound_names(pat: &Pat, out: &mut Vec<String>) {
    match pat {
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Constructor { args, .. } => {
            for arg in args {
                collect_pat_bound_names(arg, out);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            for (field_name, alias) in fields {
                match alias {
                    Some(p) => collect_pat_bound_names(p, out),
                    None => out.push(field_name.clone()),
                }
            }
            if let Some(name) = as_name {
                out.push(name.clone());
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (field_name, alias) in fields {
                match alias {
                    Some(p) => collect_pat_bound_names(p, out),
                    None => out.push(field_name.clone()),
                }
            }
        }
        Pat::Tuple { elements, .. } => {
            for element in elements {
                collect_pat_bound_names(element, out);
            }
        }
        Pat::StringPrefix { rest, .. } => collect_pat_bound_names(rest, out),
        Pat::BitStringPat { segments, .. } => {
            for seg in segments {
                collect_pat_bound_names(&seg.value, out);
            }
        }
        Pat::ListPat { elements, .. } => {
            for element in elements {
                collect_pat_bound_names(element, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_bound_names(head, out);
            collect_pat_bound_names(tail, out);
        }
        Pat::Or { patterns, .. } => {
            for pat in patterns {
                collect_pat_bound_names(pat, out);
            }
        }
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
    }
}

pub(super) fn pat_has_nonbinding_ref(pat: &Pat, name: &str) -> bool {
    match pat {
        Pat::Constructor { args, .. } => args.iter().any(|p| pat_has_nonbinding_ref(p, name)),
        Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
            fields.iter().any(|(_, alias)| {
                alias
                    .as_ref()
                    .is_some_and(|p| pat_has_nonbinding_ref(p, name))
            })
        }
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            elements.iter().any(|p| pat_has_nonbinding_ref(p, name))
        }
        Pat::StringPrefix { rest, .. } => pat_has_nonbinding_ref(rest, name),
        Pat::BitStringPat { segments, .. } => segments.iter().any(|seg| {
            pat_has_nonbinding_ref(&seg.value, name)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| expr_mentions_name(size, name))
        }),
        Pat::ConsPat { head, tail, .. } => {
            pat_has_nonbinding_ref(head, name) || pat_has_nonbinding_ref(tail, name)
        }
        Pat::Or { patterns, .. } => patterns.iter().any(|p| pat_has_nonbinding_ref(p, name)),
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => false,
    }
}

pub(super) fn expr_mentions_name(expr: &Expr, name: &str) -> bool {
    match &expr.kind {
        ExprKind::Var { name: var } => var == name,
        ExprKind::App { func, arg, .. } => {
            expr_mentions_name(func, name) || expr_mentions_name(arg, name)
        }
        ExprKind::BinOp { left, right, .. } => {
            expr_mentions_name(left, name) || expr_mentions_name(right, name)
        }
        ExprKind::UnaryMinus { expr } | ExprKind::Ascription { expr, .. } => {
            expr_mentions_name(expr, name)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_mentions_name(cond, name)
                || expr_mentions_name(then_branch, name)
                || expr_mentions_name(else_branch, name)
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            expr_mentions_name(scrutinee, name)
                || arms.iter().any(|arm| {
                    pat_has_nonbinding_ref(&arm.node.pattern, name)
                        || (!pat_binds_name(&arm.node.pattern, name)
                            && arm
                                .node
                                .guard
                                .as_ref()
                                .is_some_and(|g| expr_mentions_name(g, name)))
                        || (!pat_binds_name(&arm.node.pattern, name)
                            && expr_mentions_name(&arm.node.body, name))
                })
        }
        ExprKind::Block { stmts, .. } => stmts
            .iter()
            .any(|stmt| stmt_mentions_name(&stmt.node, name)),
        ExprKind::Lambda { params, body } => {
            params.iter().any(|p| pat_has_nonbinding_ref(p, name))
                || (!pats_bind_name(params, name) && expr_mentions_name(body, name))
        }
        ExprKind::FieldAccess { expr, .. } => expr_mentions_name(expr, name),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            fields.iter().any(|(_, _, e)| expr_mentions_name(e, name))
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            expr_mentions_name(record, name)
                || fields.iter().any(|(_, _, e)| expr_mentions_name(e, name))
        }
        ExprKind::EffectCall { args, .. } | ExprKind::ForeignCall { args, .. } => {
            args.iter().any(|e| expr_mentions_name(e, name))
        }
        ExprKind::With { expr, handler } => {
            expr_mentions_name(expr, name) || handler_mentions_name(handler, name)
        }
        ExprKind::Resume { value } => expr_mentions_name(value, name),
        ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
            elements.iter().any(|e| expr_mentions_name(e, name))
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            bindings
                .iter()
                .any(|(p, e)| pat_has_nonbinding_ref(p, name) || expr_mentions_name(e, name))
                || expr_mentions_name(success, name)
                || else_arms.iter().any(|arm| {
                    pat_has_nonbinding_ref(&arm.node.pattern, name)
                        || (!pat_binds_name(&arm.node.pattern, name)
                            && expr_mentions_name(&arm.node.body, name))
                })
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            arms.iter().any(|arm| {
                pat_has_nonbinding_ref(&arm.node.pattern, name)
                    || (!pat_binds_name(&arm.node.pattern, name)
                        && arm
                            .node
                            .guard
                            .as_ref()
                            .is_some_and(|g| expr_mentions_name(g, name)))
                    || (!pat_binds_name(&arm.node.pattern, name)
                        && expr_mentions_name(&arm.node.body, name))
            }) || after_clause.as_ref().is_some_and(|(timeout, body)| {
                expr_mentions_name(timeout, name) || expr_mentions_name(body, name)
            })
        }
        ExprKind::BitString { segments } => segments.iter().any(|seg| {
            expr_mentions_name(&seg.value, name)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| expr_mentions_name(size, name))
        }),
        ExprKind::HandlerExpr { body } => {
            body.arms.iter().any(|arm| {
                pat_has_nonbinding_ref_in_handler_arm(&arm.node.params, name)
                    || (!pats_bind_name(&arm.node.params, name)
                        && expr_mentions_name(&arm.node.body, name))
            }) || body.return_clause.as_ref().is_some_and(|arm| {
                pat_has_nonbinding_ref_in_handler_arm(&arm.params, name)
                    || (!pats_bind_name(&arm.params, name) && expr_mentions_name(&arm.body, name))
            })
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            segments.iter().any(|s| expr_mentions_name(&s.node, name))
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            segments.iter().any(|s| expr_mentions_name(&s.node, name))
        }
        ExprKind::Cons { head, tail } => {
            expr_mentions_name(head, name) || expr_mentions_name(tail, name)
        }
        ExprKind::StringInterp { parts, .. } => parts.iter().any(|part| match part {
            StringPart::Expr(e) => expr_mentions_name(e, name),
            StringPart::Lit(_) => false,
        }),
        ExprKind::ListComprehension { body, qualifiers } => {
            expr_mentions_name(body, name)
                || qualifiers.iter().any(|q| match q {
                    ComprehensionQualifier::Generator(p, e) | ComprehensionQualifier::Let(p, e) => {
                        pat_has_nonbinding_ref(p, name) || expr_mentions_name(e, name)
                    }
                    ComprehensionQualifier::Guard(e) => expr_mentions_name(e, name),
                })
        }
        ExprKind::DictMethodAccess { dict, .. } => expr_mentions_name(dict, name),
        ExprKind::Lit { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => false,
    }
}

pub(super) fn stmt_mentions_name(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::Let { pattern, value, .. } => {
            pat_has_nonbinding_ref(pattern, name) || expr_mentions_name(value, name)
        }
        Stmt::LetFun {
            name: fun_name,
            params,
            body,
            guard,
            ..
        } => {
            fun_name == name
                || params.iter().any(|p| pat_has_nonbinding_ref(p, name))
                || (!pats_bind_name(params, name)
                    && (expr_mentions_name(body, name)
                        || guard.as_ref().is_some_and(|g| expr_mentions_name(g, name))))
        }
        Stmt::Expr(e) => expr_mentions_name(e, name),
    }
}

pub(super) fn handler_mentions_name(handler: &Handler, name: &str) -> bool {
    match handler {
        Handler::Named(n) => n.name == name,
        Handler::Inline { items, .. } => items.iter().any(|item| match &item.node {
            HandlerItem::Named(n) => n.name == name,
            HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                pat_has_nonbinding_ref_in_handler_arm(&arm.params, name)
                    || (!pats_bind_name(&arm.params, name) && expr_mentions_name(&arm.body, name))
                    || arm
                        .finally_block
                        .as_ref()
                        .is_some_and(|f| expr_mentions_name(f, name))
            }
        }),
    }
}

pub(super) fn pat_has_nonbinding_ref_in_handler_arm(params: &[Pat], name: &str) -> bool {
    params.iter().any(|p| pat_has_nonbinding_ref(p, name))
}
