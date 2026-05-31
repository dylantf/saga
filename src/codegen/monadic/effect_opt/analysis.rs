use super::*;

pub(super) fn expr_is_pure(expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(_) => true,
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_is_pure(value) && expr_is_pure(body)
        }
        MExpr::Ensure { .. } => false,
        MExpr::Case { arms, .. } => arms
            .iter()
            .all(|arm| arm.guard.as_ref().is_none_or(expr_is_pure) && expr_is_pure(&arm.body)),
        MExpr::If {
            then_branch,
            else_branch,
            ..
        } => expr_is_pure(then_branch) && expr_is_pure(else_branch),
        MExpr::FieldAccess { .. }
        | MExpr::RecordUpdate { .. }
        | MExpr::DictMethodAccess { .. }
        | MExpr::BinOp { .. }
        | MExpr::UnaryMinus { .. }
        | MExpr::BitString { .. } => true,
        MExpr::App {
            head: Atom::DictRef { .. },
            ..
        } => true,
        MExpr::Yield { .. }
        | MExpr::App { .. }
        | MExpr::With { .. }
        | MExpr::Resume { .. }
        | MExpr::ForeignCall { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => false,
    }
}

pub(super) fn expr_is_handler_independent_value(expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(atom) => atom_is_handler_independent_value(atom),
        MExpr::Let { value, body, .. } => {
            expr_is_handler_independent_value(value) && expr_is_handler_independent_value(body)
        }
        MExpr::Case { arms, .. } => arms.iter().all(|arm| {
            arm.guard
                .as_ref()
                .is_none_or(expr_is_handler_independent_value)
                && expr_is_handler_independent_value(&arm.body)
        }),
        MExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            expr_is_handler_independent_value(then_branch)
                && expr_is_handler_independent_value(else_branch)
        }
        MExpr::FieldAccess { .. }
        | MExpr::RecordUpdate { .. }
        | MExpr::DictMethodAccess { .. }
        | MExpr::BinOp { .. }
        | MExpr::UnaryMinus { .. }
        | MExpr::BitString { .. } => true,
        MExpr::App { .. }
        | MExpr::Yield { .. }
        | MExpr::Bind { .. }
        | MExpr::Ensure { .. }
        | MExpr::With { .. }
        | MExpr::Resume { .. }
        | MExpr::ForeignCall { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => false,
    }
}

pub(super) fn atom_is_handler_independent_value(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } => args.iter().all(atom_is_handler_independent_value),
        Atom::Tuple { elements, .. } => elements.iter().all(atom_is_handler_independent_value),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .all(|(_, atom)| atom_is_handler_independent_value(atom)),
        Atom::Lambda { .. } | Atom::BackendSpawnThunk { .. } => false,
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => true,
    }
}

pub(super) fn expr_contains_dict_method_access(expr: &MExpr) -> bool {
    match expr {
        MExpr::DictMethodAccess { .. } => true,
        MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
            atom_contains_dict_method_access(atom)
        }
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_dict_method_access)
        }
        MExpr::Bind { value, body, .. }
        | MExpr::Let { value, body, .. }
        | MExpr::Ensure {
            body: value,
            cleanup: body,
        } => expr_contains_dict_method_access(value) || expr_contains_dict_method_access(body),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_dict_method_access(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_dict_method_access)
                        || expr_contains_dict_method_access(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_dict_method_access(cond)
                || expr_contains_dict_method_access(then_branch)
                || expr_contains_dict_method_access(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_dict_method_access(head)
                || args.iter().any(atom_contains_dict_method_access)
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_dict_method_access(handler) || expr_contains_dict_method_access(body)
        }
        MExpr::FieldAccess { record, .. } | MExpr::UnaryMinus { value: record, .. } => {
            atom_contains_dict_method_access(record)
        }
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_dict_method_access(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_dict_method_access(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_dict_method_access(left) || atom_contains_dict_method_access(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_dict_method_access(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_dict_method_access)
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(expr_contains_dict_method_access)
                    || expr_contains_dict_method_access(&arm.body)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_dict_method_access(timeout) || expr_contains_dict_method_access(body)
            })
        }
        MExpr::LetFun { body, rest, .. } => {
            expr_contains_dict_method_access(body) || expr_contains_dict_method_access(rest)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_dict_method_access)
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_dict_method_access(arm))
        }
    }
}

pub(super) fn handler_contains_dict_method_access(handler: &MHandler) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_dict_method_access)
                || return_clause
                    .as_ref()
                    .is_some_and(handler_arm_contains_dict_method_access)
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => {
            handlers.iter().any(handler_contains_dict_method_access)
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_dict_method_access(op_tuple)
                || return_lambda
                    .as_ref()
                    .is_some_and(atom_contains_dict_method_access)
        }
    }
}

pub(super) fn handler_arm_contains_dict_method_access(arm: &MHandlerArm) -> bool {
    expr_contains_dict_method_access(&arm.body)
        || arm
            .finally_block
            .as_deref()
            .is_some_and(expr_contains_dict_method_access)
}

pub(super) fn atom_contains_dict_method_access(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            args.iter().any(atom_contains_dict_method_access)
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_contains_dict_method_access(atom)),
        Atom::Lambda { body, .. } => expr_contains_dict_method_access(body),
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_dict_method_access(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}
