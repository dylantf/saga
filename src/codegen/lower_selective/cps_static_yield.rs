use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_static_direct_call_yield(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let arm = self.static_direct_call_arm_for_yield(op, args)?;
        let bindings = self.direct_call_param_bindings(&arm.params, args)?;

        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let lowered_body = self.lower_cps_handler_arm_expr(&arm.body, evidence, return_k, None);
        self.pop_scope();

        Some(
            bindings
                .into_iter()
                .rev()
                .fold(lowered_body, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                }),
        )
    }

    pub(super) fn lower_static_direct_call_yield_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
    ) -> Option<CExpr> {
        let arm = self.static_direct_call_arm_for_yield(op, args)?;
        let bindings = self.direct_call_param_bindings(&arm.params, args)?;
        let MExpr::Resume { value, .. } = &*arm.body else {
            return None;
        };

        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let lowered_value = self.lower_atom(value);
        self.pop_scope();

        Some(
            bindings
                .into_iter()
                .rev()
                .fold(lowered_value, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                }),
        )
    }

    pub(super) fn static_direct_call_arm_for_yield(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
    ) -> Option<MHandlerArm> {
        let mut candidate = None;
        for frame in self.direct_handler_stack.iter().rev() {
            if !frame.handles_effect(&op.effect) {
                continue;
            }
            let DirectHandlerFrame::Static { arms: frame } = frame else {
                return None;
            };

            let mut matching = frame.iter().filter(|arm| {
                Self::effect_names_match(&arm.op.effect, &op.effect) && arm.op.op == op.op
            });
            let arm = matching.next()?;
            if matching.next().is_some() {
                return None;
            }
            candidate = Some(arm.clone());
            break;
        }

        let arm: MHandlerArm = candidate?;
        if arm.finally_block.is_some()
            || args.len() != arm.params.len()
            || self.handler_info.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive)
            || self.expr_contains_yield(&arm.body)
        {
            return None;
        }
        if !self.direct_call_params_supported(&arm.params)
            || !self.handler_arm_expr_is_cps_island_subset(&arm.body)
        {
            return None;
        }
        Some(arm)
    }

    pub(super) fn direct_call_param_bindings(
        &mut self,
        params: &[Pat],
        args: &[Atom],
    ) -> Option<Vec<(String, CExpr)>> {
        if params.len() != args.len() {
            return None;
        }
        let mut bindings = Vec::new();
        for (param, arg) in params.iter().zip(args) {
            match param {
                Pat::Var { name, .. } => {
                    bindings.push((core_var(name), self.lower_atom(arg)));
                }
                Pat::Wildcard { .. }
                | Pat::Lit {
                    value: crate::ast::Lit::Unit,
                    ..
                } => {}
                _ => return None,
            }
        }
        Some(bindings)
    }

    pub(super) fn direct_call_params_supported(&self, params: &[Pat]) -> bool {
        params.iter().all(|param| {
            matches!(
                param,
                Pat::Var { .. }
                    | Pat::Wildcard { .. }
                    | Pat::Lit {
                        value: crate::ast::Lit::Unit,
                        ..
                    }
            )
        })
    }
}
