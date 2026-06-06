use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_return_clause_closure(
        &mut self,
        arm: &MHandlerArm,
        outer_evidence: CExpr,
        outer_return_k: CExpr,
    ) -> CExpr {
        if arm.finally_block.is_some() {
            self.unsupported("selective CPS return-clause finally blocks");
        }
        if arm.params.len() > 1 {
            self.unsupported("selective CPS return clauses with multiple params");
        }

        let params = match arm.params.as_slice() {
            [] => vec![self.fresh_cps_temp("_ReturnValue")],
            [pat] => lower_param_names(std::slice::from_ref(pat)),
            _ => unreachable!(),
        };

        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let body = self.lower_cps_expr(&arm.body, outer_evidence, outer_return_k);
        let body = if arm.params.is_empty() {
            body
        } else {
            self.wrap_param_match(&arm.params, &params, body)
        };
        self.pop_scope();

        CExpr::Fun(params, Box::new(body))
    }

    pub(super) fn lower_cps_static_handler_op_tuple(
        &mut self,
        effect: &str,
        arms: &[&MHandlerArm],
        outer_evidence: &CExpr,
        abort_marker: Option<&str>,
    ) -> CExpr {
        let mut by_op_index: std::collections::BTreeMap<u32, Vec<&MHandlerArm>> =
            std::collections::BTreeMap::new();
        for arm in arms {
            by_op_index.entry(arm.op.op_index).or_default().push(*arm);
        }

        let max_op_index = by_op_index.keys().next_back().copied().unwrap_or(0);
        let mut closures = Vec::with_capacity(max_op_index as usize);
        for expected in 1..=max_op_index {
            let Some(op_arms) = by_op_index.get(&expected) else {
                self.unsupported(&format!(
                    "static handler for effect '{effect}' is missing op_index {expected}"
                ));
            };
            closures.push(self.lower_cps_static_handler_arm_group(
                op_arms,
                outer_evidence.clone(),
                abort_marker,
            ));
        }
        CExpr::Tuple(closures)
    }

    pub(super) fn lower_cps_handler_value(
        &mut self,
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
        outer_evidence: CExpr,
    ) -> CExpr {
        let ops_by_effect =
            self.lower_cps_handler_value_ops_by_effect(arms, outer_evidence.clone());
        let return_value = return_clause
            .map(|arm| self.lower_cps_handler_value_return_lambda(arm))
            .unwrap_or_else(|| CExpr::Lit(CLit::Atom("unit".to_string())));
        CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("__saga_handler_value".to_string())),
            ops_by_effect,
            return_value,
        ])
    }

    pub(super) fn lower_cps_handler_value_expr(
        &mut self,
        expr: &MExpr,
        outer_evidence: CExpr,
    ) -> CExpr {
        match expr {
            MExpr::Pure(atom) => {
                let Some(info) = self.handler_value_info_for_atom(atom).cloned() else {
                    self.unsupported_expr(expr);
                };
                self.lower_cps_handler_value(
                    &info.arms,
                    info.return_clause.as_ref(),
                    outer_evidence,
                )
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => self.lower_cps_handler_value(arms, return_clause.as_deref(), outer_evidence),
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
                        body: self
                            .lower_cps_handler_value_expr(then_branch, outer_evidence.clone()),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_handler_value_expr(else_branch, outer_evidence),
                    },
                ],
            ),
            _ => self.unsupported_expr(expr),
        }
    }

    pub(super) fn lower_cps_handler_value_ops_by_effect(
        &mut self,
        arms: &[MHandlerArm],
        outer_evidence: CExpr,
    ) -> CExpr {
        let mut by_effect: BTreeMap<String, Vec<&MHandlerArm>> = BTreeMap::new();
        for arm in arms {
            by_effect
                .entry(arm.op.effect.clone())
                .or_default()
                .push(arm);
        }

        let pairs = by_effect
            .into_iter()
            .map(|(effect, mut effect_arms)| {
                effect_arms.sort_by_key(|arm| arm.op.op_index);
                let op_tuple = self.lower_cps_static_handler_op_tuple(
                    &effect,
                    &effect_arms,
                    &outer_evidence,
                    None,
                );
                CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(effect)), op_tuple])
            })
            .collect();
        CExpr::Tuple(pairs)
    }

    pub(super) fn lower_cps_handler_value_return_lambda(&mut self, arm: &MHandlerArm) -> CExpr {
        let value_param = self.fresh_cps_temp("_HandlerReturnValue");
        let evidence_param = self.fresh_cps_temp("_HandlerReturnEvidence");
        let return_k_param = self.fresh_cps_temp("_HandlerReturnK");

        if arm.params.len() > 1 {
            self.unsupported("handler value return clauses with multiple params");
        }

        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let body = self.lower_cps_expr(
            &arm.body,
            CExpr::Var(evidence_param.clone()),
            CExpr::Var(return_k_param.clone()),
        );
        let body = match arm.params.as_slice() {
            [] => body,
            [pat] => CExpr::Case(
                Box::new(CExpr::Var(value_param.clone())),
                vec![CArm {
                    pat: self.lower_pat(pat),
                    guard: None,
                    body,
                }],
            ),
            _ => unreachable!(),
        };
        self.pop_scope();

        CExpr::Fun(
            vec![value_param, evidence_param, return_k_param],
            Box::new(body),
        )
    }
}
