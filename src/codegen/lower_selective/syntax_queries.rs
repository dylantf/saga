use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn expr_contains_yield(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { .. } => true,
            MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => self.atom_contains_yield(atom),
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.expr_contains_yield(value) || self.expr_contains_yield(body)
            }
            MExpr::Ensure { body, cleanup } => {
                self.expr_contains_yield(body) || self.expr_contains_yield(cleanup)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.atom_contains_yield(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| self.expr_contains_yield(guard))
                            || self.expr_contains_yield(&arm.body)
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_contains_yield(cond)
                    || self.expr_contains_yield(then_branch)
                    || self.expr_contains_yield(else_branch)
            }
            MExpr::App { head, args, .. } => {
                self.atom_contains_yield(head)
                    || args.iter().any(|arg| self.atom_contains_yield(arg))
            }
            MExpr::With { handler, body, .. } => {
                self.handler_contains_yield(handler) || self.expr_contains_yield(body)
            }
            MExpr::FieldAccess { record, .. }
            | MExpr::DictMethodAccess { dict: record, .. }
            | MExpr::RecordUpdate { record, .. } => self.atom_contains_yield(record),
            MExpr::ForeignCall { args, .. } => args.iter().any(|arg| self.atom_contains_yield(arg)),
            MExpr::BitString { segments, .. } => segments
                .iter()
                .any(|segment| self.atom_contains_yield(&segment.value)),
            MExpr::BinOp { left, right, .. } => {
                self.atom_contains_yield(left) || self.atom_contains_yield(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_contains_yield(value),
            MExpr::Receive { .. } | MExpr::LetFun { .. } | MExpr::HandlerValue { .. } => true,
        }
    }

    pub(super) fn handler_contains_yield(&self, handler: &MHandler) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().any(|arm| {
                    self.expr_contains_yield(&arm.body)
                        || arm
                            .finally_block
                            .as_ref()
                            .is_some_and(|cleanup| self.expr_contains_yield(cleanup))
                }) || return_clause
                    .as_ref()
                    .is_some_and(|arm| self.expr_contains_yield(&arm.body))
            }
            MHandler::Composite { handlers, .. } => handlers
                .iter()
                .any(|handler| self.handler_contains_yield(handler)),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                self.atom_contains_yield(op_tuple)
                    || return_lambda
                        .as_ref()
                        .is_some_and(|atom| self.atom_contains_yield(atom))
            }
            MHandler::Native { .. } => false,
        }
    }

    pub(super) fn atom_contains_yield(&self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { body, .. } => self.expr_contains_yield(body),
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                args.iter().any(|atom| self.atom_contains_yield(atom))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .any(|(_, atom)| self.atom_contains_yield(atom)),
            Atom::BackendSpawnThunk { callback, .. } => self.atom_contains_yield(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::QualifiedRef { .. }
            | Atom::DictRef { .. }
            | Atom::BackendAtom { .. } => false,
        }
    }

    pub(super) fn atom_contains_resume(&self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { body, .. } => self.expr_contains_resume(body),
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                args.iter().any(|atom| self.atom_contains_resume(atom))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .any(|(_, atom)| self.atom_contains_resume(atom)),
            Atom::BackendSpawnThunk { callback, .. } => self.atom_contains_resume(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::QualifiedRef { .. }
            | Atom::DictRef { .. }
            | Atom::BackendAtom { .. } => false,
        }
    }

    pub(super) fn expr_contains_resume(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Resume { .. } => true,
            MExpr::Pure(atom) => self.atom_contains_resume(atom),
            MExpr::Yield { args, .. } => args.iter().any(|arg| self.atom_contains_resume(arg)),
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.expr_contains_resume(value) || self.expr_contains_resume(body)
            }
            MExpr::Ensure { body, cleanup } => {
                self.expr_contains_resume(body) || self.expr_contains_resume(cleanup)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.atom_contains_resume(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| self.expr_contains_resume(guard))
                            || self.expr_contains_resume(&arm.body)
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_contains_resume(cond)
                    || self.expr_contains_resume(then_branch)
                    || self.expr_contains_resume(else_branch)
            }
            MExpr::App { head, args, .. } => {
                self.atom_contains_resume(head)
                    || args.iter().any(|arg| self.atom_contains_resume(arg))
            }
            MExpr::With { handler, body, .. } => {
                self.handler_contains_resume(handler) || self.expr_contains_resume(body)
            }
            MExpr::FieldAccess { record, .. }
            | MExpr::DictMethodAccess { dict: record, .. }
            | MExpr::RecordUpdate { record, .. } => self.atom_contains_resume(record),
            MExpr::ForeignCall { args, .. } => {
                args.iter().any(|arg| self.atom_contains_resume(arg))
            }
            MExpr::BitString { segments, .. } => segments
                .iter()
                .any(|segment| self.atom_contains_resume(&segment.value)),
            MExpr::BinOp { left, right, .. } => {
                self.atom_contains_resume(left) || self.atom_contains_resume(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_contains_resume(value),
            MExpr::Receive { .. } | MExpr::LetFun { .. } | MExpr::HandlerValue { .. } => true,
        }
    }

    pub(super) fn handler_contains_resume(&self, handler: &MHandler) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().any(|arm| {
                    self.expr_contains_resume(&arm.body)
                        || arm
                            .finally_block
                            .as_ref()
                            .is_some_and(|cleanup| self.expr_contains_resume(cleanup))
                }) || return_clause
                    .as_ref()
                    .is_some_and(|arm| self.expr_contains_resume(&arm.body))
            }
            MHandler::Composite { handlers, .. } => handlers
                .iter()
                .any(|handler| self.handler_contains_resume(handler)),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                self.atom_contains_resume(op_tuple)
                    || return_lambda
                        .as_ref()
                        .is_some_and(|atom| self.atom_contains_resume(atom))
            }
            MHandler::Native { .. } => false,
        }
    }

    pub(super) fn effect_names_match(left: &str, right: &str) -> bool {
        if left == right {
            return true;
        }
        let left_qualified = left.contains('.');
        let right_qualified = right.contains('.');
        if left_qualified && right_qualified {
            return false;
        }
        left.rsplit('.').next() == right.rsplit('.').next()
    }
}
