use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_case_chain(
        &mut self,
        scrutinee: &Atom,
        arms: &[MArm],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        if let Some(known_scrutinee) = self.known_direct_atom_for_case_scrutinee(scrutinee) {
            for arm in arms {
                if arm.guard.is_some() {
                    break;
                }
                let Some(bindings) =
                    self.match_known_direct_atom_pattern(&known_scrutinee, &arm.pattern)
                else {
                    continue;
                };
                self.push_scope();
                self.bind_cps_pat_locals_for_expr_use(&arm.pattern, &arm.body);
                self.bind_known_direct_atom_pattern_values(bindings);
                let body = self.lower_cps_expr(&arm.body, evidence, return_k);
                self.pop_scope();
                return body;
            }
        }

        let scrutinee = self.lower_atom(scrutinee);
        let scrut_var = self.fresh_cps_temp("_CpsCaseScrut");
        let mut rest = self.case_clause_error();

        for arm in arms.iter().rev() {
            let rest_var = self.fresh_cps_temp("_CpsCaseRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_cps_pat_locals_for_expr_use(&arm.pattern, &arm.body);
            let body = self.lower_cps_expr(&arm.body, evidence.clone(), return_k.clone());
            let body = match arm.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = self.lower_pat(&arm.pattern);
            self.pop_scope();

            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }

        CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest))
    }

    pub(super) fn lower_cps_receive(
        &mut self,
        arms: &[MArm],
        after: Option<&(Atom, Box<MExpr>)>,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        let arms = arms
            .iter()
            .map(|arm| self.lower_cps_receive_arm(arm, evidence.clone(), return_k.clone()))
            .collect();
        let (timeout, timeout_body) = match after {
            Some((timeout, body)) => (
                self.lower_atom(timeout),
                self.lower_cps_expr(body, evidence, return_k),
            ),
            None => (
                CExpr::Lit(CLit::Atom("infinity".to_string())),
                CExpr::Lit(CLit::Atom("true".to_string())),
            ),
        };
        CExpr::Receive(arms, Box::new(timeout), Box::new(timeout_body))
    }

    pub(super) fn lower_cps_receive_arm(
        &mut self,
        arm: &MArm,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CArm {
        self.push_scope();
        self.bind_cps_pat_locals_for_expr_use(&arm.pattern, &arm.body);
        let raw_body = self.lower_cps_expr(&arm.body, evidence, return_k);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let (pat, reason_wrapper) = self.lower_receive_pat(&arm.pattern);
        let body = match reason_wrapper {
            Some((user_var, raw_var)) => {
                let conversion = self.exit_reason_from_erlang(&raw_var);
                CExpr::Let(user_var, Box::new(conversion), Box::new(raw_body))
            }
            None => raw_body,
        };
        self.pop_scope();
        CArm { pat, guard, body }
    }
}
