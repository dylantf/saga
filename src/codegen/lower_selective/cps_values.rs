use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_arg_atom(
        &mut self,
        atom: &Atom,
        expected_cps_callback: Option<(usize, usize)>,
    ) -> CExpr {
        if let Some((source_arity, adapter_arity)) = expected_cps_callback {
            return self.lower_cps_runtime_value_atom(atom, source_arity, adapter_arity);
        }
        self.lower_atom(atom)
    }

    pub(super) fn lower_effect_protocol_arg_atom(&mut self, atom: &Atom) -> CExpr {
        if let Some(LocalValueShape::PureCallable { arity }) = self.pure_value_atom_shape(atom) {
            return self.pure_to_cps_adapter_value_closure(atom, arity, arity + 2);
        }
        self.lower_cps_value_atom(atom)
    }

    pub(super) fn lower_cps_value_atom(&mut self, atom: &Atom) -> CExpr {
        match self.cps_value_atom_shape(atom) {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                ..
            }) if matches!(atom, Atom::Lambda { .. }) => {
                let Atom::Lambda { params, body, .. } = atom else {
                    unreachable!();
                };
                self.assert_app_arity("CPS lambda", source_arity + 2, adapter_arity);
                self.lower_cps_lambda_atom(params, body)
            }
            Some(LocalValueShape::RuntimeCpsCallable { .. })
                if matches!(atom, Atom::Var { .. }) =>
            {
                let Atom::Var { name, .. } = atom else {
                    unreachable!();
                };
                CExpr::Var(core_var(&name.name))
            }
            Some(LocalValueShape::CpsCallable {
                module,
                name,
                source_arity,
                adapter_arity,
                ..
            }) => self.cps_adapter_value_closure(module, name, source_arity, adapter_arity),
            _ => self.lower_atom(atom),
        }
    }

    pub(super) fn lower_cps_runtime_value_atom(
        &mut self,
        atom: &Atom,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CExpr {
        if let Atom::Lambda { params, body, .. } = atom
            && self.lambda_is_cps_subset(atom)
        {
            self.assert_app_arity("CPS lambda", params.len(), source_arity);
            self.assert_app_arity("CPS lambda", params.len() + 2, adapter_arity);
            return self.lower_cps_lambda_atom(params, body);
        }

        match self.cps_value_atom_shape(atom) {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity: actual_source_arity,
                adapter_arity: actual_adapter_arity,
                ..
            }) if !matches!(atom, Atom::Lambda { .. })
                || self.lambda_is_cps_subset(atom)
                || matches!(atom, Atom::Lambda { params, body, .. } if self.lambda_is_direct_subset(params, body)) =>
            {
                self.assert_app_arity("CPS lambda/value", actual_source_arity, source_arity);
                self.assert_app_arity("CPS lambda/value", actual_adapter_arity, adapter_arity);
                match atom {
                    Atom::Var { name, .. } => CExpr::Var(core_var(&name.name)),
                    Atom::Lambda { params, body, .. } => self.lower_cps_lambda_atom(params, body),
                    _ => self.unsupported_atom(atom),
                }
            }
            Some(LocalValueShape::CpsCallable {
                module,
                name,
                source_arity: actual_source_arity,
                adapter_arity: actual_adapter_arity,
                ..
            }) => {
                self.assert_app_arity(&name, actual_source_arity, source_arity);
                self.assert_app_arity(&name, actual_adapter_arity, adapter_arity);
                self.cps_adapter_value_closure(module, name, source_arity, adapter_arity)
            }
            _ if self.pure_value_atom_shape(atom).is_some() => {
                self.pure_to_cps_adapter_value_closure(atom, source_arity, adapter_arity)
            }
            _ => self.lower_atom(atom),
        }
    }

    pub(super) fn lower_cps_lambda_atom(&mut self, params: &[Pat], body: &MExpr) -> CExpr {
        if params.iter().any(|p| !direct_param_supported(p)) {
            self.unsupported("CPS lambda with unsupported parameter pattern");
        }
        let direct_params = lower_param_names(params);
        let evidence_name = self.fresh_cps_temp("_LambdaEvidence");
        let return_k_name = self.fresh_cps_temp("_LambdaK");
        let mut lambda_params = direct_params.clone();
        lambda_params.push(evidence_name.clone());
        lambda_params.push(return_k_name.clone());

        self.push_scope();
        for pat in params {
            self.bind_cps_pat_locals(pat);
        }
        let lowered_body =
            self.lower_cps_expr(body, CExpr::Var(evidence_name), CExpr::Var(return_k_name));
        let lowered_body = self.wrap_param_match(params, &direct_params, lowered_body);
        self.pop_scope();

        CExpr::Fun(lambda_params, Box::new(lowered_body))
    }

    pub(super) fn lower_cps_runtime_value_expr(
        &mut self,
        expr: &MExpr,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CExpr {
        match expr {
            MExpr::Pure(atom) => {
                self.lower_cps_runtime_value_atom(atom, source_arity, adapter_arity)
            }
            MExpr::DictMethodAccess { .. } => self.lower_expr(expr),
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
                        body: self.lower_cps_runtime_value_expr(
                            then_branch,
                            source_arity,
                            adapter_arity,
                        ),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_runtime_value_expr(
                            else_branch,
                            source_arity,
                            adapter_arity,
                        ),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter()
                    .map(|arm| self.lower_cps_runtime_value_arm(arm, source_arity, adapter_arity))
                    .collect(),
            ),
            _ => self.unsupported_expr(expr),
        }
    }

    pub(super) fn lower_cps_runtime_value_arm(
        &mut self,
        arm: &MArm,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CArm {
        self.push_scope();
        self.bind_cps_pat_locals(&arm.pattern);
        let body = self.lower_cps_runtime_value_expr(&arm.body, source_arity, adapter_arity);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }

    pub(super) fn pure_to_cps_adapter_value_closure(
        &mut self,
        atom: &Atom,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CExpr {
        self.assert_app_arity("pure CPS callback adapter", source_arity + 2, adapter_arity);
        let pure_arity = self
            .pure_callback_arity_for_atom(atom)
            .or_else(|| match self.pure_value_atom_shape(atom) {
                Some(LocalValueShape::PureCallable { arity }) => Some(arity),
                Some(LocalValueShape::PureCallableFromUseType)
                | Some(LocalValueShape::CpsCallable { .. })
                | Some(LocalValueShape::RuntimeCpsCallable { .. })
                | None => None,
            })
            .unwrap_or_else(|| self.unsupported_atom(atom));
        self.assert_app_arity("pure CPS callback adapter", pure_arity, source_arity);

        let arg_names: Vec<String> = (0..source_arity)
            .map(|_| self.fresh_cps_temp("_PureCpsArg"))
            .collect();
        let evidence_name = self.fresh_cps_temp("_PureCpsEvidence");
        let return_k_name = self.fresh_cps_temp("_PureCpsK");
        let mut params = arg_names.clone();
        params.push(evidence_name);
        params.push(return_k_name.clone());

        let pure_call_args: Vec<CExpr> = arg_names.into_iter().map(CExpr::Var).collect();
        let pure_call = if let Some(callable) = self.direct_function_callable(atom) {
            self.assert_app_arity(&callable.name, pure_call_args.len(), callable.arity);
            match callable.module {
                Some(module) => CExpr::Call(module, callable.name, pure_call_args),
                None => CExpr::Apply(
                    Box::new(CExpr::FunRef(callable.name, callable.arity)),
                    pure_call_args,
                ),
            }
        } else {
            CExpr::Apply(Box::new(self.lower_atom(atom)), pure_call_args)
        };
        CExpr::Fun(
            params,
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(return_k_name)),
                vec![pure_call],
            )),
        )
    }

    pub(super) fn cps_adapter_value_closure(
        &mut self,
        module: Option<String>,
        name: String,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CExpr {
        self.assert_app_arity(&name, source_arity + 2, adapter_arity);
        let arg_names: Vec<String> = (0..source_arity)
            .map(|_| self.fresh_cps_temp("_CpsFnArg"))
            .collect();
        let evidence_name = self.fresh_cps_temp("_CpsFnEvidence");
        let return_k_name = self.fresh_cps_temp("_CpsFnK");
        let mut params = arg_names.clone();
        params.push(evidence_name.clone());
        params.push(return_k_name.clone());

        let mut call_args: Vec<CExpr> = arg_names.into_iter().map(CExpr::Var).collect();
        call_args.push(CExpr::Var(evidence_name));
        call_args.push(CExpr::Var(return_k_name));
        let body = match module {
            Some(module) => CExpr::Call(module, name, call_args),
            None => CExpr::Apply(Box::new(CExpr::FunRef(name, adapter_arity)), call_args),
        };
        CExpr::Fun(params, Box::new(body))
    }
}
