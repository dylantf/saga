use super::*;

pub(super) fn local_is_only_called_in_expr(local: &str, expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(atom) => !atom_mentions_local(local, atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().all(|arg| !atom_mentions_local(local, arg))
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            local_is_only_called_in_expr(local, value)
                && (var.name == local || local_is_only_called_in_expr(local, body))
        }
        MExpr::Ensure { body, cleanup } => {
            local_is_only_called_in_expr(local, body)
                && local_is_only_called_in_expr(local, cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            !atom_mentions_local(local, scrutinee)
                && arms.iter().all(|arm| {
                    arm.guard
                        .as_ref()
                        .is_none_or(|guard| local_is_only_called_in_expr(local, guard))
                        && (pat_binds_name(&arm.pattern, local)
                            || local_is_only_called_in_expr(local, &arm.body))
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            !atom_mentions_local(local, cond)
                && local_is_only_called_in_expr(local, then_branch)
                && local_is_only_called_in_expr(local, else_branch)
        }
        MExpr::App { head, args, .. } => {
            let head_is_local = matches!(head, Atom::Var { name, .. } if name.name == local);
            (head_is_local || !atom_mentions_local(local, head))
                && args.iter().all(|arg| !atom_mentions_local(local, arg))
        }
        MExpr::With { handler, body, .. } => {
            !handler_mentions_local(local, handler) && local_is_only_called_in_expr(local, body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::UnaryMinus { value, .. } => !atom_mentions_local(local, value),
        MExpr::RecordUpdate { record, fields, .. } => {
            !atom_mentions_local(local, record)
                && fields
                    .iter()
                    .all(|(_, atom)| !atom_mentions_local(local, atom))
        }
        MExpr::DictMethodAccess { dict, .. } => !atom_mentions_local(local, dict),
        MExpr::BinOp { left, right, .. } => {
            !atom_mentions_local(local, left) && !atom_mentions_local(local, right)
        }
        MExpr::BitString { segments, .. } => segments
            .iter()
            .all(|segment| !atom_mentions_local(local, &segment.value)),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().all(|arm| {
                arm.guard
                    .as_ref()
                    .is_none_or(|guard| local_is_only_called_in_expr(local, guard))
                    && (pat_binds_name(&arm.pattern, local)
                        || local_is_only_called_in_expr(local, &arm.body))
            }) && after.as_ref().is_none_or(|(timeout, body)| {
                !atom_mentions_local(local, timeout) && local_is_only_called_in_expr(local, body)
            })
        }
        MExpr::LetFun {
            name, body, rest, ..
        } => {
            (name == local || local_is_only_called_in_expr(local, body))
                && local_is_only_called_in_expr(local, rest)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .all(|arm| !handler_arm_mentions_local(local, arm))
                && return_clause
                    .as_ref()
                    .is_none_or(|arm| !handler_arm_mentions_local(local, arm))
        }
    }
}

fn expr_mentions_local(local: &str, expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(atom) => atom_mentions_local(local, atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(|arg| atom_mentions_local(local, arg))
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            expr_mentions_local(local, value)
                || (var.name != local && expr_mentions_local(local, body))
        }
        MExpr::Ensure { body, cleanup } => {
            expr_mentions_local(local, body) || expr_mentions_local(local, cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_mentions_local(local, scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_mentions_local(local, guard))
                        || (!pat_binds_name(&arm.pattern, local)
                            && expr_mentions_local(local, &arm.body))
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_mentions_local(local, cond)
                || expr_mentions_local(local, then_branch)
                || expr_mentions_local(local, else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_mentions_local(local, head)
                || args.iter().any(|arg| atom_mentions_local(local, arg))
        }
        MExpr::With { handler, body, .. } => {
            handler_mentions_local(local, handler) || expr_mentions_local(local, body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_mentions_local(local, value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_mentions_local(local, record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_mentions_local(local, atom))
        }
        MExpr::DictMethodAccess { dict, .. } => atom_mentions_local(local, dict),
        MExpr::BinOp { left, right, .. } => {
            atom_mentions_local(local, left) || atom_mentions_local(local, right)
        }
        MExpr::BitString { segments, .. } => segments
            .iter()
            .any(|segment| atom_mentions_local(local, &segment.value)),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(|guard| expr_mentions_local(local, guard))
                    || (!pat_binds_name(&arm.pattern, local)
                        && expr_mentions_local(local, &arm.body))
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_mentions_local(local, timeout) || expr_mentions_local(local, body)
            })
        }
        MExpr::LetFun {
            name, body, rest, ..
        } => {
            (name != local && expr_mentions_local(local, body))
                || expr_mentions_local(local, rest)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_mentions_local(local, arm))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_mentions_local(local, arm))
        }
    }
}

fn atom_mentions_local(local: &str, atom: &Atom) -> bool {
    match atom {
        Atom::Var { name, .. } => name.name == local,
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            args.iter().any(|arg| atom_mentions_local(local, arg))
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_mentions_local(local, atom)),
        Atom::Lambda { params, body, .. } => {
            !params.iter().any(|param| pat_binds_name(param, local))
                && expr_mentions_local(local, body)
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_mentions_local(local, callback),
    }
}

fn handler_mentions_local(local: &str, handler: &MHandler) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_mentions_local(local, arm))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_mentions_local(local, arm))
        }
        MHandler::Composite { handlers, .. } => handlers
            .iter()
            .any(|handler| handler_mentions_local(local, handler)),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_mentions_local(local, op_tuple)
                || return_lambda
                    .as_ref()
                    .is_some_and(|atom| atom_mentions_local(local, atom))
        }
        MHandler::Native { .. } => false,
    }
}

fn handler_arm_mentions_local(local: &str, arm: &MHandlerArm) -> bool {
    if arm.params.iter().any(|param| pat_binds_name(param, local)) {
        return false;
    }
    expr_mentions_local(local, &arm.body)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|body| expr_mentions_local(local, body))
}
