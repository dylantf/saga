use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_app(
        &mut self,
        head: &Atom,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        match self.classify_cps_call(head, args) {
            CpsCallDecision::HofDirect {
                module,
                specialization,
            } => {
                let value = self.lower_hof_direct_specialized_call(module, &specialization, args);
                CExpr::Apply(Box::new(return_k), vec![value])
            }
            CpsCallDecision::StaticHandlerLocal { function_name } => {
                if let Some(lowered) = self.lower_static_handler_specialized_local_cps_call(
                    &function_name,
                    args,
                    evidence.clone(),
                    return_k.clone(),
                ) {
                    lowered
                } else if let Some(shape) = self.call_shape(head) {
                    self.lower_normal_cps_call(head, args, evidence, return_k, shape)
                } else {
                    self.unsupported("classified local static-handler CPS call did not lower")
                }
            }
            CpsCallDecision::StaticHandlerImported(candidate) => {
                if let Some(lowered) = self.lower_static_handler_specialized_imported_cps_call(
                    candidate,
                    args,
                    evidence.clone(),
                    return_k.clone(),
                ) {
                    lowered
                } else if let Some(shape) = self.call_shape(head) {
                    self.lower_normal_cps_call(head, args, evidence, return_k, shape)
                } else {
                    self.unsupported("classified imported static-handler CPS call did not lower")
                }
            }
            CpsCallDecision::KnownLocalLambda { name } => self
                .lower_known_local_cps_lambda_call(&name, args, evidence, return_k)
                .unwrap_or_else(|| {
                    self.unsupported("classified known local CPS lambda did not lower")
                }),
            CpsCallDecision::Lambda => self.lower_cps_lambda_app(head, args, evidence, return_k),
            CpsCallDecision::Normal(shape) => {
                self.lower_normal_cps_call(head, args, evidence, return_k, shape)
            }
            CpsCallDecision::Direct => {
                let value = self.lower_app(head, args);
                CExpr::Apply(Box::new(return_k), vec![value])
            }
            CpsCallDecision::Unsupported => self.unsupported_expr(&MExpr::App {
                head: head.clone(),
                args: args.to_vec(),
                source: NodeId::fresh(),
            }),
        }
    }

    pub(super) fn classify_cps_call(&mut self, head: &Atom, args: &[Atom]) -> CpsCallDecision {
        // Keep this order explicit: specializations are optional fast paths,
        // and the normal CPS/direct decisions remain the correctness fallback.
        if let Some((module, specialization)) =
            self.hof_direct_specialization_for_cps_call(head, args)
        {
            return CpsCallDecision::HofDirect {
                module,
                specialization,
            };
        }

        if let Some(function_name) =
            self.static_handler_specialized_local_cps_call_candidate(head, args)
        {
            return CpsCallDecision::StaticHandlerLocal { function_name };
        }

        if let Some(candidate) = self.imported_static_handler_call_candidate(head, args) {
            return CpsCallDecision::StaticHandlerImported(candidate);
        }

        if let Atom::Var { name, .. } = head
            && self.known_cps_lambda(&name.name).is_some()
        {
            return CpsCallDecision::KnownLocalLambda {
                name: name.name.clone(),
            };
        }

        if self.cps_lambda_arity_for_atom(head).is_some() && matches!(head, Atom::Lambda { .. }) {
            return CpsCallDecision::Lambda;
        }

        if let Some(shape @ (CallShape::Cps { .. } | CallShape::LocalCpsCallable { .. })) =
            self.call_shape(head)
        {
            return CpsCallDecision::Normal(shape);
        }

        if self.expr_is_direct_subset(&MExpr::App {
            head: head.clone(),
            args: args.to_vec(),
            source: NodeId::fresh(),
        }) {
            return CpsCallDecision::Direct;
        }

        CpsCallDecision::Unsupported
    }

    pub(super) fn lower_cps_lambda_app(
        &mut self,
        head: &Atom,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        let Some((source_arity, adapter_arity, _effects)) = self.cps_lambda_arity_for_atom(head)
        else {
            self.unsupported_atom(head);
        };
        let Atom::Lambda { params, body, .. } = head else {
            self.unsupported_atom(head);
        };
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
        CExpr::Apply(
            Box::new(self.lower_cps_lambda_atom(params, body)),
            lowered_args,
        )
    }

    pub(super) fn known_cps_lambda_value_needed_in_expr(&self, name: &str, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => self.known_cps_lambda_value_needed_in_atom(name, atom),
            MExpr::Yield { args, .. } => args
                .iter()
                .any(|arg| self.known_cps_lambda_value_needed_in_atom(name, arg)),
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                self.known_cps_lambda_value_needed_in_expr(name, value)
                    || (var.name != name && self.known_cps_lambda_value_needed_in_expr(name, body))
            }
            MExpr::Ensure { body, cleanup } => {
                self.known_cps_lambda_value_needed_in_expr(name, body)
                    || self.known_cps_lambda_value_needed_in_expr(name, cleanup)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.known_cps_lambda_value_needed_in_atom(name, scrutinee)
                    || arms
                        .iter()
                        .any(|arm| self.known_cps_lambda_value_needed_in_arm(name, arm))
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.known_cps_lambda_value_needed_in_atom(name, cond)
                    || self.known_cps_lambda_value_needed_in_expr(name, then_branch)
                    || self.known_cps_lambda_value_needed_in_expr(name, else_branch)
            }
            MExpr::App { head, args, .. } => {
                let head_needs_value = !matches!(head, Atom::Var { name: var, .. } if var.name == name)
                    && self.known_cps_lambda_value_needed_in_atom(name, head);
                head_needs_value
                    || args
                        .iter()
                        .any(|arg| self.known_cps_lambda_value_needed_in_atom(name, arg))
            }
            MExpr::With { handler, body, .. } => {
                self.known_cps_lambda_value_needed_in_handler(name, handler)
                    || self.known_cps_lambda_value_needed_in_expr(name, body)
            }
            MExpr::Resume { value, .. } => self.known_cps_lambda_value_needed_in_atom(name, value),
            MExpr::FieldAccess { record, .. } => {
                self.known_cps_lambda_value_needed_in_atom(name, record)
            }
            MExpr::RecordUpdate { record, fields, .. } => {
                self.known_cps_lambda_value_needed_in_atom(name, record)
                    || fields
                        .iter()
                        .any(|(_, atom)| self.known_cps_lambda_value_needed_in_atom(name, atom))
            }
            MExpr::DictMethodAccess { dict, .. } => {
                self.known_cps_lambda_value_needed_in_atom(name, dict)
            }
            MExpr::ForeignCall { args, .. } => args
                .iter()
                .any(|arg| self.known_cps_lambda_value_needed_in_atom(name, arg)),
            MExpr::BinOp { left, right, .. } => {
                self.known_cps_lambda_value_needed_in_atom(name, left)
                    || self.known_cps_lambda_value_needed_in_atom(name, right)
            }
            MExpr::UnaryMinus { value, .. } => {
                self.known_cps_lambda_value_needed_in_atom(name, value)
            }
            MExpr::BitString { segments, .. } => segments.iter().any(|segment| {
                self.known_cps_lambda_value_needed_in_atom(name, &segment.value)
                    || segment
                        .size
                        .as_ref()
                        .is_some_and(|size| self.known_cps_lambda_value_needed_in_atom(name, size))
            }),
            MExpr::Receive { arms, after, .. } => {
                arms.iter()
                    .any(|arm| self.known_cps_lambda_value_needed_in_arm(name, arm))
                    || after.as_ref().is_some_and(|(timeout, body)| {
                        self.known_cps_lambda_value_needed_in_atom(name, timeout)
                            || self.known_cps_lambda_value_needed_in_expr(name, body)
                    })
            }
            MExpr::LetFun {
                name: fun_name,
                params,
                body,
                rest,
                ..
            } => {
                fun_name != name
                    && ((!params.iter().any(|param| pat_binds_name(param, name))
                        && self.known_cps_lambda_value_needed_in_expr(name, body))
                        || self.known_cps_lambda_value_needed_in_expr(name, rest))
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                arms.iter()
                    .any(|arm| self.known_cps_lambda_value_needed_in_handler_arm(name, arm))
                    || return_clause.as_ref().is_some_and(|arm| {
                        self.known_cps_lambda_value_needed_in_handler_arm(name, arm)
                    })
            }
        }
    }

    pub(super) fn known_cps_lambda_value_needed_in_atom(&self, name: &str, atom: &Atom) -> bool {
        match atom {
            Atom::Var { name: var, .. } => var.name == name,
            Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => false,
            Atom::Ctor { args, .. } => args
                .iter()
                .any(|arg| self.known_cps_lambda_value_needed_in_atom(name, arg)),
            Atom::Tuple { elements, .. } => elements
                .iter()
                .any(|arg| self.known_cps_lambda_value_needed_in_atom(name, arg)),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .any(|(_, atom)| self.known_cps_lambda_value_needed_in_atom(name, atom)),
            Atom::Lambda { params, body, .. } => {
                !params.iter().any(|param| pat_binds_name(param, name))
                    && self.known_cps_lambda_value_needed_in_expr(name, body)
            }
            Atom::BackendSpawnThunk { callback, .. } => {
                self.known_cps_lambda_value_needed_in_atom(name, callback)
            }
        }
    }

    pub(super) fn known_cps_lambda_value_needed_in_arm(&self, name: &str, arm: &MArm) -> bool {
        arm.guard
            .as_ref()
            .is_some_and(|guard| self.known_cps_lambda_value_needed_in_expr(name, guard))
            || (!pat_binds_name(&arm.pattern, name)
                && self.known_cps_lambda_value_needed_in_expr(name, &arm.body))
    }

    pub(super) fn known_cps_lambda_value_needed_in_handler(
        &self,
        name: &str,
        handler: &MHandler,
    ) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter()
                    .any(|arm| self.known_cps_lambda_value_needed_in_handler_arm(name, arm))
                    || return_clause.as_ref().is_some_and(|arm| {
                        self.known_cps_lambda_value_needed_in_handler_arm(name, arm)
                    })
            }
            MHandler::Native { .. } => false,
            MHandler::Composite { handlers, .. } => handlers
                .iter()
                .any(|handler| self.known_cps_lambda_value_needed_in_handler(name, handler)),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                self.known_cps_lambda_value_needed_in_atom(name, op_tuple)
                    || return_lambda.as_ref().is_some_and(|lambda| {
                        self.known_cps_lambda_value_needed_in_atom(name, lambda)
                    })
            }
        }
    }

    pub(super) fn known_cps_lambda_value_needed_in_handler_arm(
        &self,
        name: &str,
        arm: &MHandlerArm,
    ) -> bool {
        let params_bind_name = arm.params.iter().any(|param| pat_binds_name(param, name));
        (!params_bind_name && self.known_cps_lambda_value_needed_in_expr(name, &arm.body))
            || arm
                .finally_block
                .as_ref()
                .is_some_and(|block| self.known_cps_lambda_value_needed_in_expr(name, block))
    }

    pub(super) fn lower_known_local_cps_lambda_call(
        &mut self,
        name: &str,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let KnownCpsLambda {
            dict_bindings: atom_dict_bindings,
            params,
            body,
        } = self.known_cps_lambda(name)?;
        if params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        self.assert_app_arity(name, args.len(), params.len());

        let dict_bindings = self.lower_known_cps_lambda_dict_bindings(&atom_dict_bindings)?;
        let arg_names = lower_param_names(&params);
        let lowered_args: Vec<CExpr> = args
            .iter()
            .map(|arg| self.lower_cps_arg_atom(arg, None))
            .collect();
        let known_dict_aliases = self.known_dict_aliases_for_bindings(&atom_dict_bindings);
        let known_atom_bindings = self.known_direct_atom_pattern_bindings_for_params(&params, args);
        let all_params_known = self
            .known_direct_atom_bindings_for_all_params(&params, args)
            .is_some();

        self.push_scope();
        for (name, _) in &dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        self.bind_known_dict_values(known_dict_aliases);
        for pat in &params {
            self.bind_pat_locals(pat);
        }
        self.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let lowered_body = self.lower_cps_expr(&body, evidence, return_k);
        let lowered_body = if all_params_known {
            lowered_body
        } else {
            self.wrap_param_match(&params, &arg_names, lowered_body)
        };
        self.pop_scope();

        let lowered_body = arg_names.into_iter().zip(lowered_args).rev().fold(
            lowered_body,
            |body, (name, value)| {
                if super::direct_core_refs::core_expr_mentions_core_var(&name, &body) {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                } else {
                    body
                }
            },
        );
        Some(
            dict_bindings
                .into_iter()
                .rev()
                .fold(lowered_body, |body, (name, value)| {
                    CExpr::Let(core_var(&name), Box::new(value), Box::new(body))
                }),
        )
    }

    pub(super) fn lower_known_cps_lambda_value(&mut self, known_lambda: &KnownCpsLambda) -> CExpr {
        if known_lambda
            .params
            .iter()
            .any(|p| !direct_param_supported(p))
        {
            self.unsupported("known CPS lambda with unsupported parameter pattern");
        }

        let dict_bindings = self
            .lower_known_cps_lambda_dict_bindings(&known_lambda.dict_bindings)
            .unwrap_or_else(|| self.unsupported("known CPS lambda with unsupported dict binding"));
        let known_dict_aliases = self.known_dict_aliases_for_bindings(&known_lambda.dict_bindings);
        let direct_params = lower_param_names(&known_lambda.params);
        let evidence_name = self.fresh_cps_temp("_LambdaEvidence");
        let return_k_name = self.fresh_cps_temp("_LambdaK");
        let mut lambda_params = direct_params.clone();
        lambda_params.push(evidence_name.clone());
        lambda_params.push(return_k_name.clone());

        self.push_scope();
        for (name, _) in &dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        self.bind_known_dict_values(known_dict_aliases);
        for pat in &known_lambda.params {
            self.bind_pat_locals(pat);
        }
        let lowered_body = self.lower_cps_expr(
            &known_lambda.body,
            CExpr::Var(evidence_name),
            CExpr::Var(return_k_name),
        );
        let lowered_body =
            self.wrap_param_match(&known_lambda.params, &direct_params, lowered_body);
        self.pop_scope();

        let lowered_body = dict_bindings
            .into_iter()
            .rev()
            .fold(lowered_body, |body, (name, value)| {
                CExpr::Let(core_var(&name), Box::new(value), Box::new(body))
            });
        CExpr::Fun(lambda_params, Box::new(lowered_body))
    }

    pub(super) fn lower_known_cps_lambda_dict_bindings(
        &mut self,
        dict_bindings: &[(String, Atom)],
    ) -> Option<Vec<(String, CExpr)>> {
        let mut lowered = Vec::with_capacity(dict_bindings.len());
        for (name, atom) in dict_bindings {
            if !self.atom_is_direct_subset(atom) {
                return None;
            }
            lowered.push((name.clone(), self.lower_atom(atom)));
        }
        Some(lowered)
    }

    pub(super) fn known_dict_aliases_for_bindings(
        &self,
        dict_bindings: &[(String, Atom)],
    ) -> Vec<(String, KnownDictValue)> {
        dict_bindings
            .iter()
            .filter_map(|(binding_name, value)| {
                let Atom::Var { name, .. } = value else {
                    return None;
                };
                if binding_name == &name.name {
                    return None;
                }
                self.known_dict_value(&name.name)
                    .map(|dict| (binding_name.clone(), dict))
            })
            .collect()
    }

    pub(super) fn known_dict_aliases_for_params(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Vec<(String, KnownDictValue)> {
        params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let Pat::Var {
                    name: param_name, ..
                } = param
                else {
                    return None;
                };
                let Atom::Var { name: arg_name, .. } = arg else {
                    return None;
                };
                if param_name == &arg_name.name {
                    return None;
                }
                self.known_dict_value(&arg_name.name)
                    .map(|dict| (param_name.clone(), dict))
            })
            .collect()
    }

    pub(super) fn lower_normal_cps_call(
        &mut self,
        head: &Atom,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
        shape: CallShape,
    ) -> CExpr {
        match shape {
            CallShape::Cps {
                module,
                name,
                source_arity,
                adapter_arity,
                ..
            } => {
                self.assert_app_arity(&name, args.len(), source_arity);
                self.assert_app_arity(&name, args.len() + 2, adapter_arity);
                let call_name = if module.is_none() {
                    self.native_variant_name_for_current_frame(&name)
                        .unwrap_or_else(|| name.clone())
                } else {
                    name.clone()
                };

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
                    Some(module) => CExpr::Call(module, call_name, lowered_args),
                    None => CExpr::Apply(
                        Box::new(CExpr::FunRef(call_name, adapter_arity)),
                        lowered_args,
                    ),
                }
            }
            CallShape::LocalCpsCallable {
                name,
                source_arity,
                adapter_arity,
                ..
            } => {
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
            _ => self.unsupported("classified non-CPS call as normal CPS call"),
        }
    }
}
