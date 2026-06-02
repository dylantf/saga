use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_expr(
        &mut self,
        expr: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        match expr {
            MExpr::Yield { op, args, .. } => self.lower_cps_yield(op, args, evidence, return_k),
            MExpr::Bind {
                var, value, body, ..
            } => self.lower_cps_bind(var, value, body, evidence, return_k),
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
                        body: self.lower_cps_expr(then_branch, evidence.clone(), return_k.clone()),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_expr(else_branch, evidence, return_k),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter()
                    .map(|arm| self.lower_cps_arm(arm, evidence.clone(), return_k.clone()))
                    .collect(),
            ),
            MExpr::App { head, args, .. } => self.lower_cps_app(head, args, evidence, return_k),
            MExpr::With { handler, body, .. } => {
                self.lower_cps_with(handler, body, evidence, return_k)
            }
            _ if self.expr_is_direct_subset(expr) => {
                CExpr::Apply(Box::new(return_k), vec![self.lower_expr(expr)])
            }
            _ => self.unsupported_expr(expr),
        }
    }

    fn lower_cps_bind(
        &mut self,
        var: &MVar,
        value: &MExpr,
        body: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        if let MExpr::Pure(atom @ Atom::Lambda { .. }) = value
            && self.lambda_is_cps_subset(atom)
        {
            let (source_arity, adapter_arity, _effects) = self
                .cps_lambda_arity_for_atom(atom)
                .unwrap_or_else(|| self.unsupported_atom(atom));
            let local_shape = LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
            };
            let lowered_value =
                self.lower_cps_runtime_value_expr(value, source_arity, adapter_arity);
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            self.current_shape_scope_mut()
                .insert(var.name.clone(), local_shape);
            let lowered_body = self.lower_cps_expr(body, evidence, return_k);
            self.pop_scope();
            return CExpr::Let(
                core_var(&var.name),
                Box::new(lowered_value),
                Box::new(lowered_body),
            );
        }

        if let Some(local_shape) = self.cps_bind_shape_for_expr(value) {
            match local_shape {
                LocalValueShape::CpsCallable { .. } => {
                    self.push_scope();
                    self.current_scope_mut().insert(var.name.clone());
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), local_shape);
                    let lowered_body = self.lower_cps_expr(body, evidence, return_k);
                    self.pop_scope();
                    return lowered_body;
                }
                LocalValueShape::RuntimeCpsCallable {
                    source_arity,
                    adapter_arity,
                } => {
                    let lowered_value =
                        self.lower_cps_runtime_value_expr(value, source_arity, adapter_arity);
                    self.push_scope();
                    self.current_scope_mut().insert(var.name.clone());
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), local_shape);
                    let lowered_body = self.lower_cps_expr(body, evidence, return_k);
                    self.pop_scope();
                    return CExpr::Let(
                        core_var(&var.name),
                        Box::new(lowered_value),
                        Box::new(lowered_body),
                    );
                }
                LocalValueShape::PureCallable { .. } | LocalValueShape::PureCallableFromUseType => {
                }
            }
        }

        if self.expr_is_direct_subset(value) {
            let local_shape = self.direct_local_shape_for_expr(value);
            let lowered_value = self.lower_expr(value);
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            if let Some(shape) = local_shape {
                self.current_shape_scope_mut()
                    .insert(var.name.clone(), shape);
            }
            let lowered_body = self.lower_cps_expr(body, evidence, return_k);
            self.pop_scope();
            return CExpr::Let(
                core_var(&var.name),
                Box::new(lowered_value),
                Box::new(lowered_body),
            );
        }

        let k_arg = self.fresh_cps_temp("_CpsBindArg");
        self.push_scope();
        self.current_scope_mut().insert(var.name.clone());
        let lowered_body = self.lower_cps_expr(body, evidence.clone(), return_k);
        self.pop_scope();
        let k_body = CExpr::Let(
            core_var(&var.name),
            Box::new(CExpr::Var(k_arg.clone())),
            Box::new(lowered_body),
        );
        let k_fun = CExpr::Fun(vec![k_arg], Box::new(k_body));
        self.lower_cps_expr(value, evidence, k_fun)
    }

    fn lower_cps_yield(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        if let Some(lowered) =
            self.lower_static_direct_call_yield(op, args, evidence.clone(), return_k.clone())
        {
            return lowered;
        }

        let find_call = CExpr::Call(
            "std_evidence_bridge".to_string(),
            "find_evidence".to_string(),
            vec![evidence.clone(), CExpr::Lit(CLit::Atom(op.effect.clone()))],
        );
        let op_closure = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(op.op_index as i64)), find_call],
        );

        let mut apply_args: Vec<CExpr> = args.iter().map(|arg| self.lower_atom(arg)).collect();
        apply_args.push(evidence);
        apply_args.push(return_k);
        CExpr::Apply(Box::new(op_closure), apply_args)
    }

    fn lower_static_direct_call_yield(
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

    fn static_direct_call_arm_for_yield(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
    ) -> Option<MHandlerArm> {
        let mut candidate = None;
        for frame in self.static_handler_stack.iter().rev() {
            let handles_effect = frame
                .iter()
                .any(|arm| Self::effect_names_match(&arm.op.effect, &op.effect));
            if !handles_effect {
                continue;
            }

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

    fn direct_call_param_bindings(
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

    fn direct_call_params_supported(&self, params: &[Pat]) -> bool {
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

    fn lower_cps_app(
        &mut self,
        head: &Atom,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        if let Some((module, specialization)) =
            self.hof_direct_specialization_for_cps_call(head, args)
        {
            let value = self.lower_hof_direct_specialized_call(module, &specialization, args);
            return CExpr::Apply(Box::new(return_k), vec![value]);
        }

        if let Some((source_arity, adapter_arity, _effects)) = self.cps_lambda_arity_for_atom(head)
            && let Atom::Lambda { params, body, .. } = head
        {
            self.assert_app_arity("CPS lambda", args.len(), source_arity);
            self.assert_app_arity("CPS lambda", args.len() + 2, adapter_arity);

            let expected_arg_shapes = self.cps_callback_param_shapes(head);
            let mut lowered_args: Vec<CExpr> = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    self.lower_cps_arg_atom(arg, expected_arg_shapes.get(index).copied().flatten())
                })
                .collect();
            lowered_args.push(evidence);
            lowered_args.push(return_k);
            return CExpr::Apply(
                Box::new(self.lower_cps_lambda_atom(params, body)),
                lowered_args,
            );
        }

        match self.call_shape(head) {
            Some(CallShape::Cps {
                module,
                name,
                source_arity,
                adapter_arity,
                ..
            }) => {
                self.assert_app_arity(&name, args.len(), source_arity);
                self.assert_app_arity(&name, args.len() + 2, adapter_arity);

                let expected_arg_shapes = self.cps_callback_param_shapes(head);
                let mut lowered_args: Vec<CExpr> = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.lower_cps_arg_atom(
                            arg,
                            expected_arg_shapes.get(index).copied().flatten(),
                        )
                    })
                    .collect();
                lowered_args.push(evidence);
                lowered_args.push(return_k);

                match module {
                    Some(module) => CExpr::Call(module, name, lowered_args),
                    None => {
                        CExpr::Apply(Box::new(CExpr::FunRef(name, adapter_arity)), lowered_args)
                    }
                }
            }
            Some(CallShape::LocalCpsCallable {
                name,
                source_arity,
                adapter_arity,
                ..
            }) => {
                self.assert_app_arity(&name, args.len(), source_arity);
                self.assert_app_arity(&name, args.len() + 2, adapter_arity);
                let expected_arg_shapes = self.cps_callback_param_shapes(head);
                let mut lowered_args: Vec<CExpr> = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.lower_cps_arg_atom(
                            arg,
                            expected_arg_shapes.get(index).copied().flatten(),
                        )
                    })
                    .collect();
                lowered_args.push(evidence);
                lowered_args.push(return_k);
                CExpr::Apply(Box::new(CExpr::Var(core_var(&name))), lowered_args)
            }
            _ => {
                if self.expr_is_direct_subset(&MExpr::App {
                    head: head.clone(),
                    args: args.to_vec(),
                    source: NodeId::fresh(),
                }) {
                    let value = self.lower_app(head, args);
                    return CExpr::Apply(Box::new(return_k), vec![value]);
                }
                self.unsupported_expr(&MExpr::App {
                    head: head.clone(),
                    args: args.to_vec(),
                    source: NodeId::fresh(),
                });
            }
        }
    }

    fn hof_direct_specialization_for_cps_call(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<(Option<String>, HofDirectSpecialization)> {
        let (module, specialization) = self.hof_direct_specialization_for_head(head)?;
        if specialization.source_arity != args.len() {
            return None;
        }

        let callback_indices: std::collections::HashSet<usize> = specialization
            .callback_params
            .iter()
            .map(|param| param.index)
            .collect();
        for callback in &specialization.callback_params {
            let arg = args.get(callback.index)?;
            if self.pure_hof_callback_arg_arity(arg)? != callback.source_arity {
                return None;
            }
        }
        for (index, arg) in args.iter().enumerate() {
            if callback_indices.contains(&index) {
                continue;
            }
            if !self.atom_is_direct_subset(arg) {
                return None;
            }
        }
        Some((module, specialization))
    }

    pub(super) fn hof_direct_specialization_for_head(
        &self,
        head: &Atom,
    ) -> Option<(Option<String>, HofDirectSpecialization)> {
        let (local_name, source) = match head {
            Atom::Var { name, source } => (Some(name.name.as_str()), *source),
            Atom::QualifiedRef { source, .. } => (None, *source),
            _ => return None,
        };
        if let Some(local_name) = local_name
            && let Some(LocalValueShape::CpsCallable {
                module,
                hof_direct_specialization: Some(specialization),
                ..
            }) = self.local_shape(local_name)
        {
            return Some((module, specialization));
        }
        if let Some(local_name) = local_name
            && let Some(specialization) = self.local_hof_direct_specializations.get(local_name)
        {
            return Some((None, specialization.clone()));
        }
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            effects,
            ..
        } = &resolved.kind
        else {
            return None;
        };
        if effects.is_empty() {
            return None;
        }
        let module = resolved_erlang_module_for_call(erlang_mod, &self.current_module)?;
        let specialization = self
            .imported_hof_direct_specializations
            .get(&(module.clone(), name.clone()))?
            .clone();
        Some((Some(module), specialization))
    }

    fn pure_hof_callback_arg_arity(&mut self, atom: &Atom) -> Option<usize> {
        if let Atom::Lambda { params, body, .. } = atom {
            if self.lambda_is_direct_subset(params, body) {
                return Some(params.len());
            }
            if self.pure_callback_arity_for_atom(atom) == Some(params.len())
                && self.lambda_is_direct_cps_island_subset(params, body)
            {
                return Some(params.len());
            }
            return None;
        }
        match self.pure_value_atom_shape(atom)? {
            LocalValueShape::PureCallable { arity } => Some(arity),
            LocalValueShape::PureCallableFromUseType
            | LocalValueShape::CpsCallable { .. }
            | LocalValueShape::RuntimeCpsCallable { .. } => None,
        }
    }

    fn lower_hof_direct_specialized_call(
        &mut self,
        module: Option<String>,
        specialization: &HofDirectSpecialization,
        args: &[Atom],
    ) -> CExpr {
        let callback_indices: std::collections::HashSet<usize> = specialization
            .callback_params
            .iter()
            .map(|param| param.index)
            .collect();
        let lowered_args = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                self.lower_hof_direct_specialized_arg(arg, callback_indices.contains(&index))
            })
            .collect();
        match module {
            Some(module) => CExpr::Call(module, specialization.entry_name.clone(), lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(
                    specialization.entry_name.clone(),
                    specialization.source_arity,
                )),
                lowered_args,
            ),
        }
    }

    fn lower_hof_direct_specialized_arg(&mut self, atom: &Atom, callback_arg: bool) -> CExpr {
        if callback_arg
            && let Atom::Lambda { params, body, .. } = atom
            && !self.lambda_is_direct_subset(params, body)
            && self.lambda_is_direct_cps_island_subset(params, body)
        {
            return self.lower_direct_cps_island_lambda_atom(params, body);
        }
        self.lower_atom(atom)
    }

    fn lower_cps_arg_atom(
        &mut self,
        atom: &Atom,
        expected_cps_callback: Option<(usize, usize)>,
    ) -> CExpr {
        if let Some((source_arity, adapter_arity)) = expected_cps_callback {
            return self.lower_cps_runtime_value_atom(atom, source_arity, adapter_arity);
        }
        self.lower_cps_value_atom(atom)
    }

    fn lower_cps_value_atom(&mut self, atom: &Atom) -> CExpr {
        match self.cps_value_atom_shape(atom) {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
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

    fn lower_cps_runtime_value_atom(
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
            }) => {
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
            self.bind_pat_locals(pat);
        }
        let lowered_body =
            self.lower_cps_expr(body, CExpr::Var(evidence_name), CExpr::Var(return_k_name));
        let lowered_body = self.wrap_param_match(params, &direct_params, lowered_body);
        self.pop_scope();

        CExpr::Fun(lambda_params, Box::new(lowered_body))
    }

    fn lower_cps_runtime_value_expr(
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

    fn lower_cps_runtime_value_arm(
        &mut self,
        arm: &MArm,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
        let body = self.lower_cps_runtime_value_expr(&arm.body, source_arity, adapter_arity);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }

    fn pure_to_cps_adapter_value_closure(
        &mut self,
        atom: &Atom,
        source_arity: usize,
        adapter_arity: usize,
    ) -> CExpr {
        self.assert_app_arity("pure CPS callback adapter", source_arity + 2, adapter_arity);
        let pure_arity = self
            .pure_callback_arity_for_atom(atom)
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

    fn cps_adapter_value_closure(
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

    fn lower_cps_with(
        &mut self,
        handler: &MHandler,
        body: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        let MHandler::Static {
            arms,
            return_clause,
            ..
        } = handler
        else {
            self.unsupported("selective CPS with currently supports static handlers only");
        };
        let mut canonical_effects = Vec::new();
        for arm in arms {
            if !canonical_effects.contains(&arm.op.effect) {
                canonical_effects.push(arm.op.effect.clone());
            }
        }

        let mut by_effect: BTreeMap<String, Vec<&MHandlerArm>> = BTreeMap::new();
        for arm in arms {
            by_effect
                .entry(arm.op.effect.clone())
                .or_default()
                .push(arm);
        }

        let mut current_evidence = evidence.clone();
        let mut bindings = Vec::with_capacity(canonical_effects.len());
        for effect in canonical_effects {
            let effect_arms = by_effect
                .get_mut(&effect)
                .unwrap_or_else(|| self.unsupported("static handler effect without arms"));
            effect_arms.sort_by_key(|arm| arm.op.op_index);
            let op_tuple = self.lower_cps_static_handler_op_tuple(&effect, effect_arms, &evidence);
            let entry = CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(effect)), op_tuple]);
            let insert = CExpr::Call(
                "std_evidence_bridge".to_string(),
                "insert_canonical".to_string(),
                vec![current_evidence, entry],
            );
            let evidence_var = self.fresh_cps_temp("_CpsEvidence");
            current_evidence = CExpr::Var(evidence_var.clone());
            bindings.push((evidence_var, insert));
        }

        let return_binding = return_clause.as_ref().map(|arm| {
            let return_k_name = self.fresh_cps_temp("_ReturnClauseK");
            let return_identity = self.identity_cps_continuation();
            let closure =
                self.lower_cps_return_clause_closure(arm, evidence.clone(), return_identity);
            (return_k_name, closure)
        });
        let body_return_k = return_binding
            .as_ref()
            .map(|(name, _)| CExpr::Var(name.clone()))
            .unwrap_or_else(|| self.identity_cps_continuation());

        self.static_handler_stack.push(arms.clone());
        let lowered_body = self.lower_cps_expr(body, current_evidence, body_return_k);
        self.static_handler_stack.pop();
        let with_evidence = bindings
            .into_iter()
            .rev()
            .fold(lowered_body, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            });
        let with_result = self.fresh_cps_temp("_WithResult");
        let apply_outer_return = CExpr::Let(
            with_result.clone(),
            Box::new(with_evidence),
            Box::new(CExpr::Apply(
                Box::new(return_k),
                vec![CExpr::Var(with_result)],
            )),
        );
        match return_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(apply_outer_return)),
            None => apply_outer_return,
        }
    }

    fn lower_cps_return_clause_closure(
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

    fn lower_cps_static_handler_op_tuple(
        &mut self,
        effect: &str,
        arms: &[&MHandlerArm],
        outer_evidence: &CExpr,
    ) -> CExpr {
        let mut closures = Vec::with_capacity(arms.len());
        for (i, arm) in arms.iter().enumerate() {
            let expected = i as u32 + 1;
            if arm.op.op_index != expected {
                self.unsupported(&format!(
                    "static handler for effect '{effect}' is missing op_index {expected}"
                ));
            }
            closures.push(self.lower_cps_static_handler_arm(arm, outer_evidence.clone()));
        }
        CExpr::Tuple(closures)
    }

    fn lower_cps_static_handler_arm(&mut self, arm: &MHandlerArm, outer_evidence: CExpr) -> CExpr {
        let source_params = lower_param_names(&arm.params);
        let perform_evidence = self.fresh_cps_temp("_ArmEvidence");
        let arm_k = self.fresh_cps_temp("_ArmK");
        let mut params = source_params.clone();
        params.push(perform_evidence);
        params.push(arm_k.clone());

        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let body = self.lower_cps_handler_arm_expr(
            &arm.body,
            outer_evidence,
            CExpr::Var(arm_k.clone()),
            arm.finally_block.as_deref(),
        );
        let body = self.wrap_param_match(&arm.params, &source_params, body);
        self.pop_scope();

        CExpr::Fun(params, Box::new(body))
    }

    fn lower_cps_handler_arm_expr(
        &mut self,
        expr: &MExpr,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        if self.expr_is_direct_subset(expr) {
            return match finally_block {
                Some(cleanup) => self.lower_direct_handler_result_with_finally(expr, cleanup),
                None => self.lower_expr(expr),
            };
        }
        match expr {
            MExpr::Resume { value, .. } => {
                self.lower_resume_with_finally(value, arm_k, finally_block)
            }
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
                let lowered_body =
                    self.lower_cps_handler_arm_expr(body, outer_evidence, arm_k, finally_block);
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
                        body: self.lower_cps_handler_arm_expr(
                            then_branch,
                            outer_evidence.clone(),
                            arm_k.clone(),
                            finally_block,
                        ),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_handler_arm_expr(
                            else_branch,
                            outer_evidence,
                            arm_k,
                            finally_block,
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
                        self.lower_cps_handler_case_arm(
                            arm,
                            outer_evidence.clone(),
                            arm_k.clone(),
                            finally_block,
                        )
                    })
                    .collect(),
            ),
            _ => self.unsupported_expr(expr),
        }
    }

    fn lower_resume_with_finally(
        &mut self,
        value: &Atom,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        let resumed = CExpr::Apply(Box::new(arm_k), vec![self.lower_atom(value)]);
        match finally_block {
            Some(cleanup) => {
                let result_var = self.fresh_cps_temp("_FinallyValue");
                CExpr::Let(
                    result_var.clone(),
                    Box::new(resumed),
                    Box::new(self.sequence_direct_finally_then(cleanup, CExpr::Var(result_var))),
                )
            }
            None => resumed,
        }
    }

    fn lower_direct_handler_result_with_finally(
        &mut self,
        expr: &MExpr,
        finally_block: &MExpr,
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
                let lowered_body =
                    self.lower_direct_handler_result_with_finally(body, finally_block);
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
                        body: self
                            .lower_direct_handler_result_with_finally(then_branch, finally_block),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self
                            .lower_direct_handler_result_with_finally(else_branch, finally_block),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter()
                    .map(|arm| {
                        self.lower_direct_handler_result_case_arm_with_finally(arm, finally_block)
                    })
                    .collect(),
            ),
            _ => {
                let result_var = self.fresh_cps_temp("_FinallyValue");
                CExpr::Let(
                    result_var.clone(),
                    Box::new(self.lower_expr(expr)),
                    Box::new(
                        self.sequence_direct_finally_then(finally_block, CExpr::Var(result_var)),
                    ),
                )
            }
        }
    }

    fn lower_direct_handler_result_case_arm_with_finally(
        &mut self,
        arm: &MArm,
        finally_block: &MExpr,
    ) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
        let body = self.lower_direct_handler_result_with_finally(&arm.body, finally_block);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }

    fn sequence_direct_finally_then(&mut self, finally_block: &MExpr, next: CExpr) -> CExpr {
        let cleanup_var = self.fresh_cps_temp("_FinallyCleanup");
        CExpr::Let(
            cleanup_var,
            Box::new(self.lower_expr(finally_block)),
            Box::new(next),
        )
    }

    fn lower_cps_handler_case_arm(
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

    fn lower_cps_arm(&mut self, arm: &MArm, evidence: CExpr, return_k: CExpr) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
        let body = self.lower_cps_expr(&arm.body, evidence, return_k);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }
}
