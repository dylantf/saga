use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_bind(
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
            let (source_arity, adapter_arity, effects) = self
                .cps_lambda_arity_for_atom(atom)
                .unwrap_or_else(|| self.unsupported_atom(atom));
            let local_shape = LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
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

        if let MExpr::Yield { op, args, .. } = value
            && let Some(lowered_value) = self.lower_static_direct_call_yield_result(op, args)
        {
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            let lowered_body = self.lower_cps_expr(body, evidence, return_k);
            self.pop_scope();
            return CExpr::Let(
                core_var(&var.name),
                Box::new(lowered_value),
                Box::new(lowered_body),
            );
        }

        if let Some(known_lambda) = self.known_cps_lambda_for_expr(value) {
            let local_shape = self.cps_bind_shape_for_expr(value);
            let needs_value = self.known_cps_lambda_value_needed_in_expr(&var.name, body);
            let lowered_value =
                needs_value.then(|| self.lower_known_cps_lambda_value(&known_lambda));
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            if let Some(local_shape) = local_shape {
                self.current_shape_scope_mut()
                    .insert(var.name.clone(), local_shape);
            }
            self.bind_known_cps_lambda(var.name.clone(), known_lambda);
            let lowered_body = self.lower_cps_expr(body, evidence, return_k);
            self.pop_scope();
            return if let Some(lowered_value) = lowered_value {
                CExpr::Let(
                    core_var(&var.name),
                    Box::new(lowered_value),
                    Box::new(lowered_body),
                )
            } else {
                lowered_body
            };
        }

        if self.handler_value_expr_is_cps_island_subset(value) {
            let lowered_value = self.lower_cps_handler_value_expr(value, evidence.clone());
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
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
                    ..
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

        let direct_app_needs_cps_bind = match value {
            MExpr::App { head, .. } => {
                self.app_head_has_cps_entry(head) || self.app_head_is_local_runtime_callable(head)
            }
            _ => false,
        };
        if self.expr_is_direct_subset(value) && !direct_app_needs_cps_bind {
            let local_shape = self.direct_local_shape_for_expr(value);
            let known_direct_lambda = self.known_direct_lambda_for_expr(value);
            let known_dict = self.known_dict_value_for_expr(value);
            let known_atom = self.known_direct_atom_for_expr(value);
            let known_value = self.known_direct_value_for_expr(value);
            let can_elide_if_unused =
                known_direct_lambda.is_some() || known_dict.is_some() || known_atom.is_some();
            let lowered_value = self.lower_expr(value);
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            if let Some(shape) = local_shape {
                self.current_shape_scope_mut()
                    .insert(var.name.clone(), shape);
            }
            if let Some(dict) = known_dict {
                self.bind_known_dict_value(var.name.clone(), dict);
            }
            if let Some(lambda) = known_direct_lambda {
                self.bind_known_direct_lambda(var.name.clone(), lambda);
            }
            if let Some(atom) = known_atom {
                self.bind_known_direct_atom(var.name.clone(), atom);
            }
            if let Some(value) = known_value {
                self.bind_known_direct_value(var.name.clone(), value);
            }
            let lowered_body = self.lower_cps_expr(body, evidence, return_k);
            self.pop_scope();
            if can_elide_if_unused
                && !super::direct_core_refs::core_expr_mentions_var(&var.name, &lowered_body)
            {
                return lowered_body;
            }
            return CExpr::Let(
                core_var(&var.name),
                Box::new(lowered_value),
                Box::new(lowered_body),
            );
        }

        let local_shape = self
            .direct_local_shape_for_expr(value)
            .or_else(|| self.cps_bind_shape_for_expr(value))
            .or_else(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body));
        let k_arg = self.fresh_cps_temp("_CpsBindArg");
        self.push_scope();
        self.current_scope_mut().insert(var.name.clone());
        if let Some(shape) = local_shape {
            self.current_shape_scope_mut()
                .insert(var.name.clone(), shape);
        }
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
}
