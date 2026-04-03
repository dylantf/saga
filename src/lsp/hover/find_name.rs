use dylang::ast::{self, Annotated, CaseArm, Decl, EffectRef, Expr, ExprKind, NodeId, Pat, Stmt, TraitBound, TypeExpr};
use dylang::token::Span;

type Found = Option<(String, Span, Option<NodeId>)>;

/// Find the name, span, and optional NodeId of the identifier at the given byte offset.
/// Returns `Some(node_id)` for Expr nodes, `None` for Pat bindings.
pub fn find_name_at_offset(program: &[Decl], offset: usize) -> Found {
    program.iter().find_map(|decl| find_in_decl(decl, offset))
}

fn contains(span: &Span, offset: usize) -> bool {
    offset >= span.start && offset < span.end
}

/// Like `contains` but inclusive of the end position. Used for leaf identifiers
/// where the cursor right after the last character is still "on" the name.
fn contains_ident(span: &Span, offset: usize) -> bool {
    offset >= span.start && offset <= span.end
}

/// Search a list of patterns then an expression body.
fn find_in_params_body(params: &[Pat], body: &Expr, offset: usize) -> Found {
    find_in_pats(params, offset).or_else(|| find_in_expr(body, offset))
}

/// Search a list of patterns.
fn find_in_pats(pats: &[Pat], offset: usize) -> Found {
    pats.iter().find_map(|p| find_in_pat(p, offset))
}

/// Search a list of typed parameters (label, TypeExpr).
fn find_in_typed_params(params: &[(String, TypeExpr)], offset: usize) -> Found {
    params
        .iter()
        .find_map(|(_, ty)| find_in_type_expr(ty, offset))
}

/// Search effect refs.
fn find_in_effect_refs(effects: &[EffectRef], offset: usize) -> Found {
    effects
        .iter()
        .find_map(|eff| find_in_effect_ref(eff, offset))
}

/// Search case/receive arms (pattern + optional guard + body).
fn find_in_arms(arms: &[Annotated<CaseArm>], offset: usize) -> Found {
    for arm_ann in arms {
        let arm = &arm_ann.node;
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

/// Search a list of expressions.
fn find_in_exprs(exprs: &[Expr], offset: usize) -> Found {
    exprs.iter().find_map(|e| find_in_expr(e, offset))
}

/// Search where clause trait bounds for trait names.
fn find_in_where_clause(bounds: &[TraitBound], offset: usize) -> Found {
    for bound in bounds {
        for (trait_name, _, trait_span) in &bound.traits {
            if contains_ident(trait_span, offset) {
                return Some((trait_name.clone(), *trait_span, None));
            }
        }
    }
    None
}

/// Search record fields (name, span, value_expr).
fn find_in_record_fields(fields: &[(String, Span, Expr)], offset: usize) -> Found {
    fields.iter().find_map(|(_, _, e)| find_in_expr(e, offset))
}

fn find_in_decl(decl: &Decl, offset: usize) -> Found {
    match decl {
        Decl::FunBinding {
            id,
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
            find_in_params_body(params, body, offset).or_else(|| {
                contains_ident(name_span, offset).then(|| (name.clone(), *name_span, Some(*id)))
            })
        }
        Decl::FunSignature {
            id,
            name,
            name_span,
            params,
            return_type,
            effects,
            where_clause,
            span,
            ..
        } if contains(span, offset) => {
            if contains_ident(name_span, offset) {
                return Some((name.clone(), *name_span, Some(*id)));
            }
            find_in_typed_params(params, offset)
                .or_else(|| find_in_type_expr(return_type, offset))
                .or_else(|| find_in_effect_refs(effects, offset))
                .or_else(|| find_in_where_clause(where_clause, offset))
        }
        Decl::HandlerDef {
            id,
            name,
            name_span,
            body,
            recovered_arms,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for arm_ann in body.arms.iter().chain(recovered_arms.iter()) {
                let arm = &arm_ann.node;
                if contains(&arm.span, offset) {
                    let qualifier_len = arm.qualifier.as_ref().map_or(0, |q: &String| q.len() + 1); // +1 for '.'
                    let op_name_end = arm.span.start + qualifier_len + arm.op_name.len();
                    if offset >= arm.span.start && offset <= op_name_end {
                        return Some((
                            arm.op_name.clone(),
                            Span {
                                start: arm.span.start,
                                end: op_name_end,
                            },
                            None,
                        ));
                    }
                    // Check handler arm parameters
                    for (param_name, param_span) in &arm.params {
                        if contains_ident(param_span, offset) {
                            return Some((param_name.clone(), *param_span, None));
                        }
                    }
                }
                if let Some(r) = find_in_expr(&arm.body, offset) {
                    return Some(r);
                }
                if let Some(ref fb) = arm.finally_block {
                    if let Some(r) = find_in_expr(fb, offset) {
                        return Some(r);
                    }
                }
            }
            if let Some(rc) = &body.return_clause {
                for (param_name, param_span) in &rc.params {
                    if contains_ident(param_span, offset) {
                        return Some((param_name.clone(), *param_span, None));
                    }
                }
                if let Some(r) = find_in_expr(&rc.body, offset) {
                    return Some(r);
                }
            }
            find_in_effect_refs(&body.effects, offset).or_else(|| {
                contains_ident(name_span, offset).then(|| (name.clone(), *name_span, Some(*id)))
            })
        }
        Decl::ImplDef {
            trait_name, trait_name_span, target_type, target_type_span,
            where_clause, needs, methods, span, ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            if contains_ident(trait_name_span, offset) {
                return Some((trait_name.clone(), *trait_name_span, None));
            }
            if contains_ident(target_type_span, offset) {
                return Some((target_type.clone(), *target_type_span, None));
            }
            if let Some(r) = find_in_where_clause(where_clause, offset) {
                return Some(r);
            }
            if let Some(r) = find_in_effect_refs(needs, offset) {
                return Some(r);
            }
            for method in methods {
                let ast::ImplMethod { name: method_name, name_span: method_span, params, body } = &method.node;
                if let Some(r) = find_in_params_body(params, body, offset) {
                    return Some(r);
                }
                // Method name hover
                if contains_ident(method_span, offset) {
                    return Some((method_name.clone(), *method_span, None));
                }
            }
            None
        }
        Decl::Let {
            id, name, name_span, value, span, ..
        }
        | Decl::Val {
            id, name, name_span, value, span, ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            if let Some(r) = find_in_expr(value, offset) {
                return Some(r);
            }
            if contains_ident(name_span, offset) {
                return Some((name.clone(), *name_span, Some(*id)));
            }
            None
        }
        Decl::TypeDef {
            name,
            name_span,
            variants,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for variant in variants {
                let variant = &variant.node;
                if contains_ident(&variant.span, offset) {
                    return Some((variant.name.clone(), variant.span, Some(variant.id)));
                }
            }
            contains_ident(name_span, offset).then(|| (name.clone(), *name_span, None))
        }
        Decl::EffectDef {
            name,
            name_span,
            operations,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for op in operations {
                let op = &op.node;
                if contains(&op.span, offset)
                    && let Some(r) = find_in_typed_params(&op.params, offset)
                        .or_else(|| find_in_type_expr(&op.return_type, offset))
                {
                    return Some(r);
                }
            }
            contains_ident(name_span, offset).then(|| (name.clone(), *name_span, None))
        }
        Decl::RecordDef {
            name,
            name_span,
            fields,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            let fields: Vec<_> = fields.iter().map(|f| f.node.clone()).collect();
            find_in_typed_params(&fields, offset).or_else(|| {
                contains_ident(name_span, offset).then(|| (name.clone(), *name_span, None))
            })
        }
        Decl::TraitDef {
            name,
            name_span,
            supertraits,
            methods,
            span,
            ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for (st_name, st_span) in supertraits {
                if contains_ident(st_span, offset) {
                    return Some((st_name.clone(), *st_span, None));
                }
            }
            for method in methods {
                let method = &method.node;
                if contains(&method.span, offset)
                    && let Some(r) = find_in_typed_params(&method.params, offset)
                        .or_else(|| find_in_type_expr(&method.return_type, offset))
                {
                    return Some(r);
                }
            }
            contains_ident(name_span, offset).then(|| (name.clone(), *name_span, None))
        }
        _ => None,
    }
}

fn find_in_expr(expr: &Expr, offset: usize) -> Found {
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
        ExprKind::QualifiedName { module, name, .. } => {
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
        ExprKind::Lambda { params, body, .. } => find_in_params_body(params, body, offset),
        ExprKind::Block { stmts, .. } => stmts.iter().find_map(|s| find_in_stmt(&s.node, offset)),
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
        } => find_in_expr(scrutinee, offset).or_else(|| find_in_arms(arms, offset)),
        ExprKind::Tuple { elements, .. } => find_in_exprs(elements, offset),
        ExprKind::RecordCreate { name, fields, .. } => find_in_record_fields(fields, offset)
            .or_else(|| {
                let name_end = span.start + name.len();
                (offset >= span.start && offset <= name_end).then(|| {
                    (
                        name.clone(),
                        Span {
                            start: span.start,
                            end: name_end,
                        },
                        None,
                    )
                })
            }),
        ExprKind::RecordUpdate { record, fields, .. } => {
            find_in_expr(record, offset).or_else(|| find_in_record_fields(fields, offset))
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
                    let all_arms: Vec<&dylang::ast::HandlerArm> = arms.iter().map(|a| &a.node)
                        .chain(return_clause.iter().map(|r| r.as_ref()))
                        .collect();
                    for arm in &all_arms {
                        if contains(&arm.span, offset) {
                            if contains(&arm.body.span, offset) {
                                return find_in_expr(&arm.body, offset);
                            }
                            if let Some(ref fb) = arm.finally_block {
                                if contains(&fb.span, offset) {
                                    return find_in_expr(fb, offset);
                                }
                            }
                            // Check inline handler arm parameters
                            for (param_name, param_span) in &arm.params {
                                if contains_ident(param_span, offset) {
                                    return Some((param_name.clone(), *param_span, None));
                                }
                            }
                            let qualifier_len = arm.qualifier.as_ref().map_or(0, |q| q.len() + 1);
                            let op_name_end = arm.span.start + qualifier_len + arm.op_name.len();
                            if offset >= arm.span.start && offset <= op_name_end {
                                return Some((
                                    arm.op_name.clone(),
                                    Span {
                                        start: arm.span.start,
                                        end: op_name_end,
                                    },
                                    None,
                                ));
                            }
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
                return Some((name.clone(), span, Some(node_id)));
            }
            find_in_exprs(args, offset)
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pat, expr) in bindings {
                if let Some(r) = find_in_pat(pat, offset).or_else(|| find_in_expr(expr, offset)) {
                    return Some(r);
                }
            }
            find_in_expr(success, offset).or_else(|| find_in_arms(else_arms, offset))
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => find_in_arms(arms, offset).or_else(|| {
            if let Some((timeout_expr, timeout_body)) = after_clause {
                find_in_expr(timeout_expr, offset).or_else(|| find_in_expr(timeout_body, offset))
            } else {
                None
            }
        }),
        _ => None,
    }
}

fn find_in_stmt(stmt: &Stmt, offset: usize) -> Found {
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
        } => find_in_params_body(params, body, offset).or_else(|| {
            contains_ident(name_span, offset).then(|| (name.clone(), *name_span, Some(*id)))
        }),


        Stmt::Expr(expr) => find_in_expr(expr, offset),
    }
}

fn find_in_pat(pat: &Pat, offset: usize) -> Found {
    match pat {
        Pat::Var { id, name, span } if contains_ident(span, offset) => {
            Some((name.clone(), *span, Some(*id)))
        }
        Pat::Constructor { args, .. } => find_in_pats(args, offset),
        Pat::Tuple { elements, .. } => find_in_pats(elements, offset),
        Pat::StringPrefix { rest, .. } => find_in_pat(rest, offset),
        Pat::Record { fields, .. } => fields
            .iter()
            .find_map(|(_, alias)| alias.as_ref().and_then(|p| find_in_pat(p, offset))),
        _ => None,
    }
}

/// Find a type name at the given offset within a TypeExpr tree.
fn find_in_type_expr(ty: &TypeExpr, offset: usize) -> Found {
    match ty {
        TypeExpr::Named { name, span } if contains_ident(span, offset) => {
            Some((name.clone(), *span, None))
        }
        TypeExpr::App {
            func, arg, span, ..
        } if contains_ident(span, offset) => {
            find_in_type_expr(func, offset).or_else(|| find_in_type_expr(arg, offset))
        }
        TypeExpr::Arrow {
            from,
            to,
            effects,
            span,
            ..
        } if contains_ident(span, offset) => find_in_type_expr(from, offset)
            .or_else(|| find_in_type_expr(to, offset))
            .or_else(|| find_in_effect_refs(effects, offset)),
        TypeExpr::Record { fields, span, .. } if contains_ident(span, offset) => {
            find_in_typed_params(fields, offset)
        }
        TypeExpr::Labeled { inner, span, .. } if contains_ident(span, offset) => {
            find_in_type_expr(inner, offset)
        }
        _ => None,
    }
}

/// Find a type/effect name at the given offset within an EffectRef.
fn find_in_effect_ref(eff: &EffectRef, offset: usize) -> Found {
    if !contains_ident(&eff.span, offset) {
        return None;
    }
    let name_end = eff.span.start + eff.name.len();
    if offset >= eff.span.start && offset <= name_end {
        return Some((
            eff.name.clone(),
            Span {
                start: eff.span.start,
                end: name_end,
            },
            None,
        ));
    }
    eff.type_args
        .iter()
        .find_map(|arg| find_in_type_expr(arg, offset))
}
