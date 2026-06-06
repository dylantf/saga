use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_resume_with_finally(
        &mut self,
        value: &Atom,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
        outer_evidence: CExpr,
    ) -> CExpr {
        let resumed = CExpr::Apply(Box::new(arm_k), vec![self.lower_atom(value)]);
        match finally_block {
            Some(cleanup) => {
                let result_var = self.fresh_cps_temp("_FinallyValue");
                CExpr::Let(
                    result_var.clone(),
                    Box::new(resumed),
                    Box::new(self.sequence_direct_finally_then(
                        cleanup,
                        CExpr::Var(result_var),
                        outer_evidence,
                    )),
                )
            }
            None => resumed,
        }
    }

    pub(super) fn lower_direct_handler_result_with_finally(
        &mut self,
        expr: &MExpr,
        finally_block: &MExpr,
        outer_evidence: CExpr,
    ) -> CExpr {
        match expr {
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if self.expr_is_direct_subset(value) =>
            {
                let local_shape = self.direct_local_shape_for_expr(value);
                let lowered_value = self.lower_expr(value);
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let lowered_body = self.lower_direct_handler_result_with_finally(
                    body,
                    finally_block,
                    outer_evidence,
                );
                self.pop_scope();
                CExpr::Let(
                    core_var(&var.name),
                    Box::new(lowered_value),
                    Box::new(lowered_body),
                )
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => CExpr::Case(
                Box::new(self.lower_atom(cond)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: self.lower_direct_handler_result_with_finally(
                            then_branch,
                            finally_block,
                            outer_evidence.clone(),
                        ),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_direct_handler_result_with_finally(
                            else_branch,
                            finally_block,
                            outer_evidence,
                        ),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter()
                    .map(|arm| {
                        self.lower_direct_handler_result_case_arm_with_finally(
                            arm,
                            finally_block,
                            outer_evidence.clone(),
                        )
                    })
                    .collect(),
            ),
            _ => {
                let result_var = self.fresh_cps_temp("_FinallyValue");
                CExpr::Let(
                    result_var.clone(),
                    Box::new(self.lower_expr(expr)),
                    Box::new(self.sequence_direct_finally_then(
                        finally_block,
                        CExpr::Var(result_var),
                        outer_evidence,
                    )),
                )
            }
        }
    }

    pub(super) fn lower_direct_handler_result_case_arm_with_finally(
        &mut self,
        arm: &MArm,
        finally_block: &MExpr,
        outer_evidence: CExpr,
    ) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
        let body =
            self.lower_direct_handler_result_with_finally(&arm.body, finally_block, outer_evidence);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }

    pub(super) fn lower_handler_finally_expr(
        &mut self,
        finally_block: &MExpr,
        outer_evidence: CExpr,
    ) -> CExpr {
        if self.handler_arm_expr_is_cps_callback_call_subset(finally_block) {
            let MExpr::App { head, args, .. } = finally_block else {
                unreachable!();
            };
            return self.lower_cps_callback_call_result_value(head, args, outer_evidence);
        }
        self.lower_expr(finally_block)
    }

    pub(super) fn lower_cps_callback_call_result_value(
        &mut self,
        head: &Atom,
        args: &[Atom],
        outer_evidence: CExpr,
    ) -> CExpr {
        let result_var = self.fresh_cps_temp("_CpsCallbackValue");
        let return_k = CExpr::Fun(vec![result_var.clone()], Box::new(CExpr::Var(result_var)));
        self.lower_cps_app(head, args, outer_evidence, return_k)
    }

    pub(super) fn sequence_direct_finally_then(
        &mut self,
        finally_block: &MExpr,
        next: CExpr,
        outer_evidence: CExpr,
    ) -> CExpr {
        let cleanup_var = self.fresh_cps_temp("_FinallyCleanup");
        CExpr::Let(
            cleanup_var,
            Box::new(self.lower_handler_finally_expr(finally_block, outer_evidence)),
            Box::new(next),
        )
    }

    pub(super) fn lower_cps_handler_case_arm(
        &mut self,
        arm: &MArm,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
        let body = self.lower_cps_handler_arm_expr(&arm.body, outer_evidence, arm_k, finally_block);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }
}
