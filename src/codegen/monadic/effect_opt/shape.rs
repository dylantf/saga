use super::*;

pub(super) fn expr_node_count(expr: &MExpr) -> usize {
    match expr {
        MExpr::Pure(atom) => 1 + atom_node_count(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => 1 + atoms_node_count(args),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            1 + expr_node_count(value) + expr_node_count(body)
        }
        MExpr::Ensure { body, cleanup } => 1 + expr_node_count(body) + expr_node_count(cleanup),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            1 + atom_node_count(scrutinee)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            1 + atom_node_count(cond) + expr_node_count(then_branch) + expr_node_count(else_branch)
        }
        MExpr::App { head, args, .. } => 1 + atom_node_count(head) + atoms_node_count(args),
        MExpr::With { handler, body, .. } => {
            1 + handler_node_count(handler) + expr_node_count(body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => 1 + atom_node_count(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            1 + atom_node_count(record)
                + fields
                    .iter()
                    .map(|(_, atom)| atom_node_count(atom))
                    .sum::<usize>()
        }
        MExpr::BinOp { left, right, .. } => 1 + atom_node_count(left) + atom_node_count(right),
        MExpr::BitString { segments, .. } => {
            1 + segments
                .iter()
                .map(|seg| {
                    atom_node_count(&seg.value) + seg.size.as_ref().map_or(0, atom_node_count)
                })
                .sum::<usize>()
        }
        MExpr::Receive { arms, after, .. } => {
            1 + arms
                .iter()
                .map(|arm| {
                    arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                })
                .sum::<usize>()
                + after.as_ref().map_or(0, |(timeout, body)| {
                    atom_node_count(timeout) + expr_node_count(body)
                })
        }
        MExpr::LetFun { body, rest, .. } => 1 + expr_node_count(body) + expr_node_count(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            1 + arms.iter().map(handler_arm_node_count).sum::<usize>()
                + return_clause
                    .as_ref()
                    .map_or(0, |arm| handler_arm_node_count(arm))
        }
    }
}

pub(super) fn atom_source(atom: &Atom) -> crate::ast::NodeId {
    match atom {
        Atom::Var { source, .. }
        | Atom::Lit { source, .. }
        | Atom::Ctor { source, .. }
        | Atom::Tuple { source, .. }
        | Atom::AnonRecord { source, .. }
        | Atom::Record { source, .. }
        | Atom::Lambda { source, .. }
        | Atom::DictRef { source, .. }
        | Atom::QualifiedRef { source, .. }
        | Atom::Symbol { source, .. }
        | Atom::BackendAtom { source, .. }
        | Atom::BackendSpawnThunk { source, .. } => *source,
    }
}

pub(super) fn atom_node_count(atom: &Atom) -> usize {
    match atom {
        Atom::Ctor { args, .. } => 1 + atoms_node_count(args),
        Atom::Tuple { elements, .. } => 1 + atoms_node_count(elements),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            1 + fields
                .iter()
                .map(|(_, atom)| atom_node_count(atom))
                .sum::<usize>()
        }
        Atom::Lambda { body, .. } => 1 + expr_node_count(body),
        Atom::BackendSpawnThunk { callback, .. } => 1 + atom_node_count(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => 1,
    }
}

pub(super) fn atoms_node_count(atoms: &[Atom]) -> usize {
    atoms.iter().map(atom_node_count).sum()
}

pub(super) fn handler_node_count(handler: &MHandler) -> usize {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            1 + arms.iter().map(handler_arm_node_count).sum::<usize>()
                + return_clause.as_ref().map_or(0, handler_arm_node_count)
        }
        MHandler::Native { .. } => 1,
        MHandler::Composite { handlers, .. } => {
            1 + handlers.iter().map(handler_node_count).sum::<usize>()
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => 1 + atom_node_count(op_tuple) + return_lambda.as_ref().map_or(0, atom_node_count),
    }
}

pub(super) fn handler_arm_node_count(arm: &MHandlerArm) -> usize {
    expr_node_count(&arm.body)
        + arm
            .finally_block
            .as_ref()
            .map_or(0, |cleanup| expr_node_count(cleanup))
}

pub(super) fn handler_frame(handler: &MHandler) -> Option<HandlerFrame> {
    match handler {
        MHandler::Static { effects, arms, .. } => {
            let effects = static_frame_effects(effects, arms);
            if effects.is_empty() {
                None
            } else {
                Some(HandlerFrame::Static {
                    effects,
                    arms: arms.clone(),
                })
            }
        }
        MHandler::Native {
            effects, handler, ..
        } => {
            if effects.is_empty() {
                None
            } else {
                Some(HandlerFrame::Native {
                    effects: effects.clone(),
                    handler: handler.clone(),
                })
            }
        }
        MHandler::Dynamic { effects, .. } => blocking_frame(effects.clone()),
        MHandler::Composite { handlers, .. } => {
            let mut effects = Vec::new();
            for handler in handlers {
                collect_handler_effects(handler, &mut effects);
            }
            blocking_frame(effects)
        }
    }
}

pub(super) fn static_frame_effects(effects: &[String], arms: &[MHandlerArm]) -> Vec<String> {
    let mut out = Vec::new();
    for effect in effects {
        push_unique_effect(&mut out, effect);
    }
    for arm in arms {
        push_unique_effect(&mut out, &arm.op.effect);
    }
    out
}

pub(super) fn effect_names_match(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    let a_is_qualified = a.contains('.');
    let b_is_qualified = b.contains('.');
    if a_is_qualified && b_is_qualified {
        return false;
    }
    a.rsplit('.').next() == b.rsplit('.').next()
}

pub(super) fn handler_effect_sets_match(left: &[String], right: &[String]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .all(|l| right.iter().any(|r| effect_names_match(l, r)))
}

pub(super) fn handler_value_candidate(expr: &MExpr) -> Option<HandlerValueCandidate> {
    let MExpr::HandlerValue {
        effects,
        arms,
        return_clause,
        source,
    } = expr
    else {
        return None;
    };

    Some(HandlerValueCandidate {
        effects: effects.clone(),
        arms: arms.clone(),
        return_clause: return_clause.clone(),
        source: *source,
    })
}

pub(super) fn expr_ends_in_handler_value(expr: &MExpr) -> bool {
    match expr {
        MExpr::HandlerValue { .. } => true,
        MExpr::Bind { body, .. } | MExpr::Let { body, .. } => expr_ends_in_handler_value(body),
        _ => false,
    }
}

pub(super) fn split_handler_factory_body(
    expr: MExpr,
) -> Option<(Vec<HandlerFactoryPrefixBinding>, MExpr)> {
    match expr {
        MExpr::HandlerValue { .. } => Some((Vec::new(), expr)),
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let (mut prefix, handler_value) = split_handler_factory_body(*body)?;
            prefix.insert(
                0,
                HandlerFactoryPrefixBinding {
                    var,
                    value: *value,
                    mode: Some(mode),
                },
            );
            Some((prefix, handler_value))
        }
        MExpr::Let { var, value, body } => {
            let (mut prefix, handler_value) = split_handler_factory_body(*body)?;
            prefix.insert(
                0,
                HandlerFactoryPrefixBinding {
                    var,
                    value: *value,
                    mode: None,
                },
            );
            Some((prefix, handler_value))
        }
        _ => None,
    }
}

pub(super) fn splice_handler_factory_prefix(
    prefix: Vec<HandlerFactoryPrefixBinding>,
    body: MExpr,
) -> MExpr {
    prefix.into_iter().rev().fold(body, |body, binding| {
        rebuild_binding(
            binding.var,
            Box::new(binding.value),
            Box::new(body),
            binding.mode,
        )
    })
}

pub(super) fn rebuild_binding(
    var: MVar,
    value: Box<MExpr>,
    body: Box<MExpr>,
    mode: Option<crate::codegen::monadic::ir::BindMode>,
) -> MExpr {
    if let Some(mode) = mode {
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        }
    } else {
        MExpr::Let { var, value, body }
    }
}

pub(super) fn atom_is_var_name(atom: &Atom, var: &MVar) -> bool {
    matches!(
        atom,
        Atom::Var { name, .. } if name.name == var.name
    )
}

pub(super) fn single_matching_arm<'a>(
    arms: &'a [MHandlerArm],
    op: &crate::codegen::monadic::ir::EffectOpRef,
) -> Option<&'a MHandlerArm> {
    let mut matching = arms
        .iter()
        .filter(|arm| effect_names_match(&arm.op.effect, &op.effect) && arm.op.op == op.op);
    let arm = matching.next()?;
    if matching.next().is_some() {
        return None;
    }
    Some(arm)
}

pub(super) fn collect_handler_effects(handler: &MHandler, out: &mut Vec<String>) {
    match handler {
        MHandler::Static { effects, arms, .. } => {
            for effect in static_frame_effects(effects, arms) {
                push_unique_effect(out, &effect);
            }
        }
        MHandler::Dynamic { effects, .. } | MHandler::Native { effects, .. } => {
            for effect in effects {
                push_unique_effect(out, effect);
            }
        }
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_effects(handler, out);
            }
        }
    }
}

pub(super) fn blocking_frame(effects: Vec<String>) -> Option<HandlerFrame> {
    if effects.is_empty() {
        None
    } else {
        Some(HandlerFrame::Blocking { effects })
    }
}

pub(super) fn push_unique_effect(out: &mut Vec<String>, effect: &str) {
    if !out.iter().any(|e| e == effect) {
        out.push(effect.to_string());
    }
}

pub(super) fn expr_yield_count(expr: &MExpr) -> usize {
    match expr {
        MExpr::Yield { args, .. } => 1 + atoms_yield_count(args),
        MExpr::Pure(atom) => atom_yield_count(atom),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_yield_count(value) + expr_yield_count(body)
        }
        MExpr::Ensure { body, cleanup } => expr_yield_count(body) + expr_yield_count(cleanup),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_yield_count(scrutinee)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_yield_count) + expr_yield_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => atom_yield_count(cond) + expr_yield_count(then_branch) + expr_yield_count(else_branch),
        MExpr::App { head, args, .. } => atom_yield_count(head) + atoms_yield_count(args),
        MExpr::With { handler, body, .. } => handler_yield_count(handler) + expr_yield_count(body),
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_yield_count(value),
        MExpr::ForeignCall { args, .. } => atoms_yield_count(args),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_yield_count(record)
                + fields
                    .iter()
                    .map(|(_, atom)| atom_yield_count(atom))
                    .sum::<usize>()
        }
        MExpr::BinOp { left, right, .. } => atom_yield_count(left) + atom_yield_count(right),
        MExpr::BitString { segments, .. } => segments
            .iter()
            .map(|seg| atom_yield_count(&seg.value) + seg.size.as_ref().map_or(0, atom_yield_count))
            .sum(),
        MExpr::Receive { arms, after, .. } => {
            arms.iter()
                .map(|arm| {
                    arm.guard.as_ref().map_or(0, expr_yield_count) + expr_yield_count(&arm.body)
                })
                .sum::<usize>()
                + after.as_ref().map_or(0, |(timeout, body)| {
                    atom_yield_count(timeout) + expr_yield_count(body)
                })
        }
        MExpr::LetFun { body, rest, .. } => expr_yield_count(body) + expr_yield_count(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().map(handler_arm_yield_count).sum::<usize>()
                + return_clause
                    .as_ref()
                    .map_or(0, |arm| handler_arm_yield_count(arm))
        }
    }
}

pub(super) fn atom_yield_count(atom: &Atom) -> usize {
    match atom {
        Atom::Ctor { args, .. } => atoms_yield_count(args),
        Atom::Tuple { elements, .. } => atoms_yield_count(elements),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().map(|(_, atom)| atom_yield_count(atom)).sum()
        }
        Atom::Lambda { body, .. } => expr_yield_count(body),
        Atom::BackendSpawnThunk { callback, .. } => atom_yield_count(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => 0,
    }
}

pub(super) fn atoms_yield_count(atoms: &[Atom]) -> usize {
    atoms.iter().map(atom_yield_count).sum()
}

pub(super) fn handler_yield_count(handler: &MHandler) -> usize {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().map(handler_arm_yield_count).sum::<usize>()
                + return_clause.as_ref().map_or(0, handler_arm_yield_count)
        }
        MHandler::Native { .. } => 0,
        MHandler::Composite { handlers, .. } => handlers.iter().map(handler_yield_count).sum(),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => atom_yield_count(op_tuple) + return_lambda.as_ref().map_or(0, atom_yield_count),
    }
}

pub(super) fn handler_arm_yield_count(arm: &MHandlerArm) -> usize {
    expr_yield_count(&arm.body)
        + arm
            .finally_block
            .as_ref()
            .map_or(0, |finally_block| expr_yield_count(finally_block))
}

pub(super) fn expr_contains_yield(expr: &MExpr) -> bool {
    match expr {
        MExpr::Yield { .. } => true,
        MExpr::Pure(atom) => atom_contains_yield(atom),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_yield(value) || expr_contains_yield(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_yield(body) || expr_contains_yield(cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_yield(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(expr_contains_yield)
                        || expr_contains_yield(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_yield(cond)
                || expr_contains_yield(then_branch)
                || expr_contains_yield(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_yield(head) || args.iter().any(atom_contains_yield)
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_yield(handler) || expr_contains_yield(body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_yield(value),
        MExpr::ForeignCall { args, .. } => args.iter().any(atom_contains_yield),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_yield(record) || fields.iter().any(|(_, atom)| atom_contains_yield(atom))
        }
        MExpr::BinOp { left, right, .. } => atom_contains_yield(left) || atom_contains_yield(right),
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_yield(&seg.value) || seg.size.as_ref().is_some_and(atom_contains_yield)
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard.as_ref().is_some_and(expr_contains_yield)
                    || expr_contains_yield(&arm.body)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_yield(timeout) || expr_contains_yield(body)
            })
        }
        MExpr::LetFun { body, rest, .. } => expr_contains_yield(body) || expr_contains_yield(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_yield)
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_yield(arm))
        }
    }
}

pub(super) fn expr_contains_inline_forbidden_shape(expr: &MExpr) -> bool {
    match expr {
        MExpr::With { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => true,
        MExpr::Pure(atom) => atom_contains_inline_forbidden_shape(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_inline_forbidden_shape)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_inline_forbidden_shape(value)
                || expr_contains_inline_forbidden_shape(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_inline_forbidden_shape(body)
                || expr_contains_inline_forbidden_shape(cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_inline_forbidden_shape(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_inline_forbidden_shape)
                        || expr_contains_inline_forbidden_shape(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_inline_forbidden_shape(cond)
                || expr_contains_inline_forbidden_shape(then_branch)
                || expr_contains_inline_forbidden_shape(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_inline_forbidden_shape(head)
                || args.iter().any(atom_contains_inline_forbidden_shape)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_inline_forbidden_shape(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_inline_forbidden_shape(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_inline_forbidden_shape(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_inline_forbidden_shape(left)
                || atom_contains_inline_forbidden_shape(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_inline_forbidden_shape(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_inline_forbidden_shape)
        }),
    }
}

pub(super) fn atom_contains_inline_forbidden_shape(atom: &Atom) -> bool {
    match atom {
        Atom::Lambda { .. } => true,
        Atom::Ctor { args, .. } => args.iter().any(atom_contains_inline_forbidden_shape),
        Atom::Tuple { elements, .. } => elements.iter().any(atom_contains_inline_forbidden_shape),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_contains_inline_forbidden_shape(atom)),
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_inline_forbidden_shape(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

pub(super) fn expr_contains_xmod_variant_forbidden_shape_with_resolution(
    expr: &MExpr,
    resolution: &ResolutionMap,
) -> bool {
    xmod_forbidden_shape_reason(expr, "body", Some(resolution)).is_some()
}

pub(super) fn expr_contains_imported_handler_factory_forbidden_shape(expr: &MExpr) -> bool {
    match expr {
        MExpr::With { .. } | MExpr::Receive { .. } | MExpr::LetFun { .. } => true,
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(|arm| {
                expr_contains_imported_handler_factory_forbidden_shape(&arm.body)
                    || arm.finally_block.as_ref().is_some_and(|cleanup| {
                        expr_contains_imported_handler_factory_forbidden_shape(cleanup)
                    })
            }) || return_clause.as_ref().is_some_and(|arm| {
                expr_contains_imported_handler_factory_forbidden_shape(&arm.body)
                    || arm.finally_block.as_ref().is_some_and(|cleanup| {
                        expr_contains_imported_handler_factory_forbidden_shape(cleanup)
                    })
            })
        }
        MExpr::Pure(atom) => atom_contains_xmod_variant_forbidden_shape(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_xmod_variant_forbidden_shape)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_imported_handler_factory_forbidden_shape(value)
                || expr_contains_imported_handler_factory_forbidden_shape(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_imported_handler_factory_forbidden_shape(body)
                || expr_contains_imported_handler_factory_forbidden_shape(cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_xmod_variant_forbidden_shape(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_imported_handler_factory_forbidden_shape)
                        || expr_contains_imported_handler_factory_forbidden_shape(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_xmod_variant_forbidden_shape(cond)
                || expr_contains_imported_handler_factory_forbidden_shape(then_branch)
                || expr_contains_imported_handler_factory_forbidden_shape(else_branch)
        }
        MExpr::App { head, args, .. } => match head {
            Atom::Lambda { params, body, .. }
                if immediate_lambda_app_is_supported(params, body, args.len()) =>
            {
                args.iter().any(atom_contains_xmod_variant_forbidden_shape)
                    || expr_contains_imported_handler_factory_forbidden_shape(body)
            }
            _ => {
                atom_contains_xmod_variant_forbidden_shape(head)
                    || args.iter().any(atom_contains_xmod_variant_forbidden_shape)
            }
        },
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_xmod_variant_forbidden_shape(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_xmod_variant_forbidden_shape(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_xmod_variant_forbidden_shape(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_xmod_variant_forbidden_shape(left)
                || atom_contains_xmod_variant_forbidden_shape(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_xmod_variant_forbidden_shape(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_xmod_variant_forbidden_shape)
        }),
    }
}

pub(super) fn atom_contains_xmod_variant_forbidden_shape(atom: &Atom) -> bool {
    xmod_forbidden_atom_reason(atom, "atom").is_some()
}

pub(super) fn expr_calls_any(expr: &MExpr, names: &HashSet<String>) -> bool {
    match expr {
        MExpr::App { head, args, .. } => {
            atom_is_call_to_any(head, names) || args.iter().any(|arg| atom_calls_any(arg, names))
        }
        MExpr::Pure(atom) => atom_calls_any(atom, names),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(|arg| atom_calls_any(arg, names))
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_calls_any(value, names) || expr_calls_any(body, names)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_calls_any(body, names) || expr_calls_any(cleanup, names)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_calls_any(scrutinee, names)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|g| expr_calls_any(g, names))
                        || expr_calls_any(&arm.body, names)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_calls_any(cond, names)
                || expr_calls_any(then_branch, names)
                || expr_calls_any(else_branch, names)
        }
        MExpr::With { handler, body, .. } => {
            handler_calls_any(handler, names) || expr_calls_any(body, names)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_calls_any(value, names),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_calls_any(record, names)
                || fields.iter().any(|(_, atom)| atom_calls_any(atom, names))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_calls_any(left, names) || atom_calls_any(right, names)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_calls_any(&seg.value, names)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| atom_calls_any(size, names))
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard.as_ref().is_some_and(|g| expr_calls_any(g, names))
                    || expr_calls_any(&arm.body, names)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_calls_any(timeout, names) || expr_calls_any(body, names)
            })
        }
        MExpr::LetFun { body, rest, .. } => {
            expr_calls_any(body, names) || expr_calls_any(rest, names)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(|arm| handler_arm_calls_any(arm, names))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_calls_any(arm, names))
        }
    }
}

pub(super) fn atom_is_call_to_any(atom: &Atom, names: &HashSet<String>) -> bool {
    matches!(atom, Atom::Var { name, .. } if names.contains(&name.name))
}

pub(super) fn atom_calls_any(atom: &Atom, names: &HashSet<String>) -> bool {
    match atom {
        Atom::Lambda { body, .. } => expr_calls_any(body, names),
        Atom::Ctor { args, .. } => args.iter().any(|arg| atom_calls_any(arg, names)),
        Atom::Tuple { elements, .. } => elements.iter().any(|arg| atom_calls_any(arg, names)),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, atom)| atom_calls_any(atom, names))
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_calls_any(callback, names),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

pub(super) fn handler_calls_any(handler: &MHandler, names: &HashSet<String>) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(|arm| handler_arm_calls_any(arm, names))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_calls_any(arm, names))
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => handlers
            .iter()
            .any(|handler| handler_calls_any(handler, names)),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_calls_any(op_tuple, names)
                || return_lambda
                    .as_ref()
                    .is_some_and(|atom| atom_calls_any(atom, names))
        }
    }
}

pub(super) fn handler_arm_calls_any(arm: &MHandlerArm, names: &HashSet<String>) -> bool {
    expr_calls_any(&arm.body, names)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|cleanup| expr_calls_any(cleanup, names))
}

pub(super) fn expr_has_private_same_module_refs(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
) -> bool {
    expr_has_private_same_module_refs_except(
        expr,
        source_module,
        self_name,
        public_names,
        resolution,
        &HashSet::new(),
    )
}

pub(super) fn expr_has_private_same_module_refs_except(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
    allowed_private_names: &HashSet<String>,
) -> bool {
    let mut refs = Vec::new();
    collect_app_head_refs(expr, &mut refs);
    refs.into_iter().any(|(name, source)| {
        let Some(resolved) = resolution.get(&source) else {
            return false;
        };
        if !matches!(
            resolved.kind,
            ResolvedCodegenKind::BeamFunction { .. }
                | ResolvedCodegenKind::ExternalFunction { .. }
                | ResolvedCodegenKind::Intrinsic { .. }
        ) {
            return false;
        }
        let same_module = resolved
            .source_module
            .as_deref()
            .is_none_or(|module| module == source_module);
        same_module
            && name != self_name
            && !public_names.contains(&name)
            && !allowed_private_names.contains(&name)
    })
}

pub(super) fn collect_app_head_refs(expr: &MExpr, out: &mut Vec<(String, crate::ast::NodeId)>) {
    match expr {
        MExpr::App { head, args, .. } => {
            if let Atom::Var { name, source } = head {
                out.push((name.name.clone(), *source));
            }
            collect_atom_list_app_refs(args, out);
        }
        MExpr::Pure(atom) => collect_atom_app_refs(atom, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_app_refs(args, out)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_app_head_refs(value, out);
            collect_app_head_refs(body, out);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_app_head_refs(body, out);
            collect_app_head_refs(cleanup, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_app_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_app_head_refs(guard, out);
                }
                collect_app_head_refs(&arm.body, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_app_refs(cond, out);
            collect_app_head_refs(then_branch, out);
            collect_app_head_refs(else_branch, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_app_refs(handler, out);
            collect_app_head_refs(body, out);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_app_refs(value, out),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_app_refs(record, out);
            for (_, atom) in fields {
                collect_atom_app_refs(atom, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_app_refs(left, out);
            collect_atom_app_refs(right, out);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_app_refs(&seg.value, out);
                if let Some(size) = &seg.size {
                    collect_atom_app_refs(size, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_app_head_refs(guard, out);
                }
                collect_app_head_refs(&arm.body, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_app_refs(timeout, out);
                collect_app_head_refs(body, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_app_head_refs(body, out);
            collect_app_head_refs(rest, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_app_refs(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_app_refs(arm, out);
            }
        }
    }
}

pub(super) fn collect_atom_app_refs(atom: &Atom, out: &mut Vec<(String, crate::ast::NodeId)>) {
    match atom {
        Atom::Lambda { body, .. } => collect_app_head_refs(body, out),
        Atom::Ctor { args, .. } => collect_atom_list_app_refs(args, out),
        Atom::Tuple { elements, .. } => collect_atom_list_app_refs(elements, out),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_app_refs(atom, out);
            }
        }
        Atom::BackendSpawnThunk { callback, .. } => collect_atom_app_refs(callback, out),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

pub(super) fn collect_atom_list_app_refs(
    atoms: &[Atom],
    out: &mut Vec<(String, crate::ast::NodeId)>,
) {
    for atom in atoms {
        collect_atom_app_refs(atom, out);
    }
}

pub(super) fn collect_handler_app_refs(
    handler: &MHandler,
    out: &mut Vec<(String, crate::ast::NodeId)>,
) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_app_refs(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_app_refs(arm, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_app_refs(handler, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_app_refs(op_tuple, out);
            if let Some(atom) = return_lambda {
                collect_atom_app_refs(atom, out);
            }
        }
    }
}

pub(super) fn collect_handler_arm_app_refs(
    arm: &MHandlerArm,
    out: &mut Vec<(String, crate::ast::NodeId)>,
) {
    collect_app_head_refs(&arm.body, out);
    if let Some(cleanup) = &arm.finally_block {
        collect_app_head_refs(cleanup, out);
    }
}

pub(super) fn atom_contains_yield(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } => args.iter().any(atom_contains_yield),
        Atom::Tuple { elements, .. } => elements.iter().any(atom_contains_yield),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, atom)| atom_contains_yield(atom))
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_yield(callback),
        Atom::Lambda { body, .. } => expr_contains_yield(body),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

pub(super) fn handler_contains_yield(handler: &MHandler) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_yield)
                || return_clause
                    .as_ref()
                    .is_some_and(handler_arm_contains_yield)
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => handlers.iter().any(handler_contains_yield),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_yield(op_tuple) || return_lambda.as_ref().is_some_and(atom_contains_yield)
        }
    }
}

pub(super) fn handler_arm_contains_yield(arm: &MHandlerArm) -> bool {
    expr_contains_yield(&arm.body)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|finally_block| expr_contains_yield(finally_block))
}

pub(super) fn cleanup_vars_are_available_at_perform_site(cleanup: &MExpr, args: &[Atom]) -> bool {
    let mut available = HashSet::new();
    for arg in args {
        collect_atom_var_names(arg, &mut available);
    }

    let mut cleanup_names = HashSet::new();
    collect_expr_var_names(cleanup, &mut cleanup_names);
    cleanup_names.is_subset(&available)
}
