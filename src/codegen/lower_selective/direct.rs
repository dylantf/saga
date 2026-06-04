use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_expr(&mut self, expr: &MExpr) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_atom(atom),
            MExpr::Yield { op, args, .. } => self
                .lower_native_direct_call_yield_result(op, args, CExpr::Tuple(vec![]))
                .unwrap_or_else(|| self.unsupported_expr(expr)),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                if let Some(lowered) =
                    self.try_lower_known_dict_immediate_method_sequence(var, value, body)
                {
                    return lowered;
                }
                if let Some(lowered) =
                    self.try_lower_immediate_known_dict_method_bind(var, value, body)
                {
                    return lowered;
                }
                let known_direct_lambda = self.known_direct_lambda_for_expr(value);
                if let Some(lambda) = known_direct_lambda
                    && occurs::local_is_only_called_in_expr(&var.name, body)
                {
                    self.push_scope();
                    self.current_scope_mut().insert(var.name.clone());
                    self.current_shape_scope_mut().insert(
                        var.name.clone(),
                        LocalValueShape::PureCallable {
                            arity: lambda.params.len(),
                        },
                    );
                    self.current_known_direct_lambda_scope_mut()
                        .insert(var.name.clone(), lambda);
                    let body = self.lower_expr(body);
                    self.pop_scope();
                    return body;
                }
                let known_direct_lambda = self.known_direct_lambda_for_expr(value);
                if let Some(lambda) = known_direct_lambda
                    && lambda.params.iter().all(direct_param_supported)
                    && self.lambda_is_direct_subset_with_dict_bindings(
                        &lambda.dict_bindings,
                        &lambda.params,
                        &lambda.body,
                    )
                {
                    let lowered_value = self.lower_known_direct_lambda_value(&lambda);
                    self.push_scope();
                    self.current_scope_mut().insert(var.name.clone());
                    self.current_shape_scope_mut().insert(
                        var.name.clone(),
                        LocalValueShape::PureCallable {
                            arity: lambda.params.len(),
                        },
                    );
                    self.current_known_direct_lambda_scope_mut()
                        .insert(var.name.clone(), lambda);
                    let body = self.lower_expr(body);
                    self.pop_scope();
                    if !core_expr_mentions_var(&var.name, &body) {
                        return body;
                    }
                    return CExpr::Let(
                        core_var(&var.name),
                        Box::new(lowered_value),
                        Box::new(body),
                    );
                }
                let local_shape = self.direct_local_shape_for_expr(value);
                let known_dict = self.known_dict_value_for_expr(value);
                let known_atom = self.known_direct_atom_for_expr(value);
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                if let Some(dict) = known_dict.as_ref() {
                    self.current_known_dict_value_scope_mut()
                        .insert(var.name.clone(), dict.clone());
                }
                if let Some(atom) = known_atom.as_ref() {
                    self.current_known_direct_atom_scope_mut()
                        .insert(var.name.clone(), atom.clone());
                }
                let body = self.lower_expr(body);
                self.pop_scope();
                if known_dict.is_some() && !core_expr_mentions_var(&var.name, &body) {
                    return body;
                }
                if known_atom.is_some() && !core_expr_mentions_var(&var.name, &body) {
                    return body;
                }
                let value = self.lower_expr(value);
                CExpr::Let(core_var(&var.name), Box::new(value), Box::new(body))
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
                        body: self.lower_expr(then_branch),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_expr(else_branch),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => self.lower_case_chain(scrutinee, arms),
            MExpr::App { head, args, .. } => self.lower_app(head, args),
            MExpr::BinOp {
                op, left, right, ..
            } => binop_atoms(op, self.lower_atom(left), self.lower_atom(right)),
            MExpr::UnaryMinus { value, .. } => CExpr::Call(
                "erlang".to_string(),
                "-".to_string(),
                vec![CExpr::Lit(CLit::Int(0)), self.lower_atom(value)],
            ),
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self.lower_field_access(record, field, record_name.as_deref(), anon_fields),
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                anon_fields,
                ..
            } => self.lower_record_update(record, fields, record_name.as_deref(), anon_fields),
            MExpr::ForeignCall {
                module, func, args, ..
            } => self.lower_foreign_call(module, func, args),
            MExpr::With { handler, body, .. } => self.lower_direct_with(handler, body),
            MExpr::Receive { arms, after, .. } => self.lower_direct_receive(arms, after.as_ref()),
            MExpr::BitString { .. } => self.unsupported_expr(expr),
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => {
                let dict = self.lower_atom(dict);
                CExpr::Call(
                    "erlang".to_string(),
                    "element".to_string(),
                    vec![CExpr::Lit(CLit::Int(*method_index as i64 + 1)), dict],
                )
            }
            MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => self.unsupported_expr(expr),
        }
    }

    fn lower_direct_with(&mut self, handler: &MHandler, body: &MExpr) -> CExpr {
        if self.direct_handler_kind(handler).is_some() {
            return self.lower_expr(body);
        }

        let MHandler::Static {
            effects,
            arms,
            return_clause,
            ..
        } = handler
        else {
            self.unsupported("direct lowering for non-static handlers");
        };
        if !effects.is_empty() || !arms.is_empty() {
            let return_k = self.identity_cps_continuation();
            return self.lower_cps_with(handler, body, CExpr::Tuple(vec![]), return_k);
        }

        let body = self.lower_expr(body);
        let Some(return_clause) = return_clause else {
            return body;
        };
        self.lower_direct_return_clause(body, return_clause)
    }

    fn lower_direct_return_clause(&mut self, value: CExpr, arm: &MHandlerArm) -> CExpr {
        if arm.finally_block.is_some() {
            self.unsupported("direct return clauses with finally blocks");
        }
        if arm.params.len() > 1 {
            self.unsupported("direct return clauses with multiple params");
        }

        let return_value = self.fresh_cps_temp("_HandlerReturnValue");
        self.push_scope();
        for param in &arm.params {
            self.bind_pat_locals(param);
        }
        let return_body = self.lower_expr(&arm.body);
        let return_body = match arm.params.as_slice() {
            [] => return_body,
            [pat] => CExpr::Case(
                Box::new(CExpr::Var(return_value.clone())),
                vec![CArm {
                    pat: self.lower_pat(pat),
                    guard: None,
                    body: return_body,
                }],
            ),
            _ => unreachable!(),
        };
        self.pop_scope();

        CExpr::Let(return_value, Box::new(value), Box::new(return_body))
    }

    fn lower_direct_receive(&mut self, arms: &[MArm], after: Option<&(Atom, Box<MExpr>)>) -> CExpr {
        let arms = arms
            .iter()
            .map(|arm| self.lower_direct_receive_arm(arm))
            .collect();
        let (timeout, timeout_body) = match after {
            Some((timeout, body)) => (self.lower_atom(timeout), self.lower_expr(body)),
            None => (
                CExpr::Lit(CLit::Atom("infinity".to_string())),
                CExpr::Lit(CLit::Atom("true".to_string())),
            ),
        };
        CExpr::Receive(arms, Box::new(timeout), Box::new(timeout_body))
    }

    fn lower_direct_receive_arm(&mut self, arm: &MArm) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
        let raw_body = self.lower_expr(&arm.body);
        let guard = arm.guard.as_ref().map(|guard| self.lower_expr(guard));
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

    fn lower_case_chain(&mut self, scrutinee: &Atom, arms: &[MArm]) -> CExpr {
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
                self.bind_pat_locals(&arm.pattern);
                self.bind_known_direct_atom_pattern_values(bindings);
                let body = self.lower_expr(&arm.body);
                self.pop_scope();
                return body;
            }
        }

        let scrutinee = self.lower_atom(scrutinee);
        let scrut_var = self.fresh_cps_temp("_CaseScrut");
        let mut rest = self.case_clause_error();

        for arm in arms.iter().rev() {
            let rest_var = self.fresh_cps_temp("_CaseRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_pat_locals(&arm.pattern);
            let body = self.lower_expr(&arm.body);
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

    fn lower_field_access(
        &mut self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        anon_fields: &Option<Vec<String>>,
    ) -> CExpr {
        if let Some(atom) = self.known_direct_field_value(record, field, record_name, anon_fields) {
            return self.lower_atom(&atom);
        }

        let order = self.record_field_order(record_name, anon_fields.as_deref());
        let index = order
            .iter()
            .position(|candidate| candidate == field)
            .unwrap_or_else(|| {
                panic!(
                    "selective-uniform direct lowerer TODO: field '{}' not found in {:?}",
                    field, order
                )
            }) as i64
            + 2;
        CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(index)), self.lower_atom(record)],
        )
    }

    fn record_field_order(
        &self,
        record_name: Option<&str>,
        anon_fields: Option<&[String]>,
    ) -> Vec<String> {
        if let Some(fields) = anon_fields {
            return fields.to_vec();
        }
        let Some(name) = record_name else {
            self.unsupported("field access without record field metadata");
        };
        self.effect_info
            .records
            .get(name)
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info.records.get(bare)
            })
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info
                    .records
                    .iter()
                    .find(|(candidate, _)| {
                        candidate
                            .rsplit('.')
                            .next()
                            .is_some_and(|last| last == bare)
                    })
                    .map(|(_, info)| info)
            })
            .map(|info| info.fields.iter().map(|(field, _)| field.clone()).collect())
            .unwrap_or_else(|| {
                panic!(
                    "selective-uniform direct lowerer TODO: unknown record '{}'",
                    name
                )
            })
    }

    fn lower_record_update(
        &mut self,
        record: &Atom,
        fields: &[(String, Atom)],
        record_name: Option<&str>,
        anon_fields: &Option<Vec<String>>,
    ) -> CExpr {
        let order = self.record_field_order(record_name, anon_fields.as_deref());
        let rec_var = self.fresh_cps_temp("_RecordUpdate");
        let field_map: HashMap<&str, &Atom> = fields
            .iter()
            .map(|(name, atom)| (name.as_str(), atom))
            .collect();

        let mut elems = Vec::with_capacity(order.len() + 1);
        elems.push(CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(rec_var.clone())],
        ));
        for (index, field_name) in order.iter().enumerate() {
            elems.push(match field_map.get(field_name.as_str()) {
                Some(atom) => self.lower_atom(atom),
                None => CExpr::Call(
                    "erlang".to_string(),
                    "element".to_string(),
                    vec![
                        CExpr::Lit(CLit::Int(index as i64 + 2)),
                        CExpr::Var(rec_var.clone()),
                    ],
                ),
            });
        }

        CExpr::Let(
            rec_var,
            Box::new(self.lower_atom(record)),
            Box::new(CExpr::Tuple(elems)),
        )
    }

    fn lower_foreign_call(&mut self, module: &str, func: &str, args: &[Atom]) -> CExpr {
        CExpr::Call(
            module.to_string(),
            func.to_string(),
            args.iter().map(|arg| self.lower_atom(arg)).collect(),
        )
    }

    fn try_lower_known_dict_immediate_method_sequence(
        &mut self,
        dict_var: &MVar,
        dict_value: &MExpr,
        body: &MExpr,
    ) -> Option<CExpr> {
        let known_dict = self.known_dict_value_for_expr(dict_value)?;
        let (MExpr::Let {
            var: method_var,
            value: method_value,
            body: method_body,
        }
        | MExpr::Bind {
            var: method_var,
            value: method_value,
            body: method_body,
            ..
        }) = body
        else {
            return None;
        };

        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = method_value.as_ref()
        else {
            return None;
        };
        let Atom::Var { name, .. } = dict else {
            return None;
        };
        if name.name != dict_var.name {
            return None;
        }

        let MExpr::App { head, args, .. } = method_body.as_ref() else {
            return None;
        };
        let Atom::Var { name, .. } = head else {
            return None;
        };
        if name.name != method_var.name {
            return None;
        }

        self.lower_known_dict_method_app(&known_dict, *method_index, args)
    }

    fn try_lower_immediate_known_dict_method_bind(
        &mut self,
        method_var: &MVar,
        method_value: &MExpr,
        body: &MExpr,
    ) -> Option<CExpr> {
        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = method_value
        else {
            return None;
        };
        let Atom::Var { name, .. } = dict else {
            return None;
        };
        let known_dict = self.known_dict_value(&name.name)?;

        let MExpr::App { head, args, .. } = body else {
            return None;
        };
        let Atom::Var { name, .. } = head else {
            return None;
        };
        if name.name != method_var.name {
            return None;
        }

        self.lower_known_dict_method_app(&known_dict, *method_index, args)
    }

    fn lower_known_dict_method_app(
        &mut self,
        known_dict: &KnownDictValue,
        method_index: usize,
        args: &[Atom],
    ) -> Option<CExpr> {
        let method = known_dict.methods.get(method_index)?;
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if params.len() != args.len() || params.iter().any(|param| !direct_param_supported(param)) {
            return None;
        }

        let dict_bindings: Vec<(String, Atom)> = known_dict
            .dict_params
            .iter()
            .cloned()
            .zip(known_dict.dict_args.iter().cloned())
            .collect();
        if !self.lambda_is_direct_subset_with_dict_bindings(&dict_bindings, params, body) {
            return None;
        }

        Some(self.lower_inline_direct_lambda_app_with_dict_bindings(
            &dict_bindings,
            params,
            body,
            args,
        ))
    }

    fn lambda_is_direct_subset_with_dict_bindings(
        &mut self,
        dict_bindings: &[(String, Atom)],
        params: &[Pat],
        body: &MExpr,
    ) -> bool {
        let known_dict_aliases = self.known_dict_aliases_for_bindings(dict_bindings);
        self.push_scope();
        for (name, _) in dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.expr_is_direct_subset(body);
        self.pop_scope();
        supported
    }

    fn lower_inline_direct_lambda_app_with_dict_bindings(
        &mut self,
        dict_bindings: &[(String, Atom)],
        params: &[Pat],
        body: &MExpr,
        args: &[Atom],
    ) -> CExpr {
        let param_names = lower_param_names(params);
        let mut known_dict_aliases = self.known_dict_aliases_for_bindings(dict_bindings);
        known_dict_aliases.extend(self.known_dict_aliases_for_params(params, args));
        let known_atom_bindings = self.known_direct_atom_pattern_bindings_for_params(params, args);
        let all_params_known = self
            .known_direct_atom_bindings_for_all_params(params, args)
            .is_some();
        let candidate_elided_dict_bindings: HashSet<String> = dict_bindings
            .iter()
            .filter_map(|(name, arg)| {
                let Atom::Var { name: arg_name, .. } = arg else {
                    return None;
                };
                self.known_dict_value(&arg_name.name)?;
                occurs::local_is_only_used_for_immediate_dict_method_calls(name, body)
                    .then(|| name.clone())
            })
            .collect();
        self.push_scope();
        for (name, _) in dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        for pat in params {
            self.bind_pat_locals(pat);
        }
        self.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let lowered_body = self.lower_expr(body);
        let lowered_body = if all_params_known {
            lowered_body
        } else {
            self.wrap_param_match(params, &param_names, lowered_body)
        };
        self.pop_scope();

        let lowered_body = param_names.into_iter().zip(args.iter()).rev().fold(
            lowered_body,
            |body, (param, arg)| {
                if core_expr_mentions_core_var(&param, &body) {
                    CExpr::Let(param, Box::new(self.lower_atom(arg)), Box::new(body))
                } else {
                    body
                }
            },
        );

        dict_bindings
            .iter()
            .rev()
            .fold(lowered_body, |body, (param, arg)| {
                if candidate_elided_dict_bindings.contains(param)
                    && !core_expr_mentions_var(param, &body)
                {
                    body
                } else {
                    CExpr::Let(
                        core_var(param),
                        Box::new(self.lower_atom(arg)),
                        Box::new(body),
                    )
                }
            })
    }

    fn lower_known_direct_lambda_value(&mut self, lambda: &KnownDirectLambda) -> CExpr {
        self.lower_partial_known_direct_lambda_value(lambda, &[])
    }

    fn lower_partial_known_direct_lambda_value(
        &mut self,
        lambda: &KnownDirectLambda,
        supplied_args: &[Atom],
    ) -> CExpr {
        if supplied_args.len() >= lambda.params.len() {
            self.unsupported("known direct lambda value with too many supplied args");
        }
        let param_names = lower_param_names(&lambda.params);
        let remaining_param_names = param_names[supplied_args.len()..].to_vec();
        let mut known_dict_aliases = self.known_dict_aliases_for_bindings(&lambda.dict_bindings);
        known_dict_aliases.extend(
            self.known_dict_aliases_for_params(
                &lambda.params[..supplied_args.len()],
                supplied_args,
            ),
        );
        let known_atom_bindings = self.known_direct_atom_pattern_bindings_for_params(
            &lambda.params[..supplied_args.len()],
            supplied_args,
        );
        self.push_scope();
        for (name, _) in &lambda.dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        for pat in &lambda.params {
            self.bind_pat_locals(pat);
        }
        self.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let lowered_body = self.lower_expr(&lambda.body);
        let lowered_body = self.wrap_param_match(&lambda.params, &param_names, lowered_body);
        self.pop_scope();

        let lowered_body = param_names
            .iter()
            .take(supplied_args.len())
            .cloned()
            .zip(supplied_args.iter())
            .rev()
            .fold(lowered_body, |body, (param, arg)| {
                if core_expr_mentions_core_var(&param, &body) {
                    CExpr::Let(param, Box::new(self.lower_atom(arg)), Box::new(body))
                } else {
                    body
                }
            });

        let lowered_body =
            lambda
                .dict_bindings
                .iter()
                .rev()
                .fold(lowered_body, |body, (param, arg)| {
                    CExpr::Let(
                        core_var(param),
                        Box::new(self.lower_atom(arg)),
                        Box::new(body),
                    )
                });
        CExpr::Fun(remaining_param_names, Box::new(lowered_body))
    }

    pub(super) fn lower_app(&mut self, head: &Atom, args: &[Atom]) -> CExpr {
        if self.is_panic_or_todo_call(head, args) {
            let Atom::Var { name, .. } = head else {
                unreachable!("is_panic_or_todo_call only matches variable heads");
            };
            return self.lower_panic_or_todo(&name.name, &args[0]);
        }
        if let Some(lambda) = self.known_direct_lambda_for_atom(head)
            && lambda.params.len() == args.len()
            && self.lambda_is_direct_subset_with_dict_bindings(
                &lambda.dict_bindings,
                &lambda.params,
                &lambda.body,
            )
        {
            return self.lower_inline_direct_lambda_app_with_dict_bindings(
                &lambda.dict_bindings,
                &lambda.params,
                &lambda.body,
                args,
            );
        }
        if let Some(lambda) = self.known_direct_lambda_for_atom(head)
            && args.len() < lambda.params.len()
            && self.lambda_is_direct_subset_with_dict_bindings(
                &lambda.dict_bindings,
                &lambda.params,
                &lambda.body,
            )
        {
            return self.lower_partial_known_direct_lambda_value(&lambda, args);
        }
        if let Some(call) = self.lower_direct_external_app(head, args) {
            return call;
        }
        if let Some((module, specialization)) =
            self.hof_direct_specialization_for_cps_call(head, args)
        {
            return self.lower_hof_direct_specialized_call(module, &specialization, args);
        }

        match self.call_shape(head) {
            Some(CallShape::Intrinsic(intrinsic)) => self.lower_intrinsic_app(intrinsic, args),
            Some(CallShape::Direct(callable)) => {
                if args.len() < callable.arity {
                    self.lower_partial_direct_callable(callable, head, args)
                } else {
                    self.assert_app_arity(&callable.name, args.len(), callable.arity);
                    self.apply_direct_callable(callable, head, args)
                }
            }
            Some(CallShape::LocalCallable { name, arity }) => {
                if args.len() < arity {
                    self.lower_partial_local_callable(&name, arity, head, args)
                } else {
                    self.assert_app_arity(&name, args.len(), arity);
                    CExpr::Apply(
                        Box::new(CExpr::Var(core_var(&name))),
                        self.lower_direct_call_args(head, args),
                    )
                }
            }
            Some(CallShape::LocalCpsCallable { name, .. }) => self.unsupported(&format!(
                "CPS callable local '{}' used in direct call position",
                name
            )),
            Some(CallShape::Cps {
                module,
                name,
                source_arity,
                adapter_arity,
                effects,
                ..
            }) if effects.is_empty()
                && source_arity == args.len()
                && adapter_arity == args.len() + 2 =>
            {
                self.lower_direct_cps_entry_call(
                    module,
                    &name,
                    source_arity,
                    adapter_arity,
                    head,
                    args,
                )
            }
            Some(CallShape::Cps {
                name,
                source_arity,
                adapter_arity,
                effects,
                ..
            }) => self.unsupported(&format!(
                "CPS-shaped call to '{}' with source arity {}, adapter arity {}, and effects {:?}",
                name, source_arity, adapter_arity, effects
            )),
            None => self.unsupported_expr(&MExpr::App {
                head: head.clone(),
                args: args.to_vec(),
                source: NodeId::fresh(),
            }),
        }
    }

    fn lower_direct_external_app(&mut self, head: &Atom, args: &[Atom]) -> Option<CExpr> {
        if let Some(callable) = self.local_external_callable_by_name(head) {
            if args.len() != callable.arity {
                return None;
            }
            let module = callable.module?;
            let call_args = args
                .iter()
                .filter(|arg| {
                    !matches!(
                        arg,
                        Atom::Lit {
                            value: Lit::Unit,
                            ..
                        }
                    )
                })
                .map(|arg| self.lower_atom(arg))
                .collect();
            return Some(CExpr::Call(module, callable.name, call_args));
        }

        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::ExternalFunction {
            target_erlang_mod,
            target_name,
            arity,
            effects,
            ..
        } = &resolved.kind
        else {
            return None;
        };
        if !effects.is_empty() {
            return None;
        }
        if args.len() != *arity {
            return None;
        }
        self.assert_app_arity(target_name, args.len(), *arity);
        let call_args = args
            .iter()
            .filter(|arg| {
                !matches!(
                    arg,
                    Atom::Lit {
                        value: Lit::Unit,
                        ..
                    }
                )
            })
            .map(|arg| self.lower_atom(arg))
            .collect();
        Some(CExpr::Call(
            target_erlang_mod.clone(),
            target_name.clone(),
            call_args,
        ))
    }

    pub(super) fn assert_app_arity(&self, name: &str, actual: usize, expected: usize) {
        if actual != expected {
            self.unsupported(&format!(
                "call to '{}' with {} args; expected {}",
                name, actual, expected
            ));
        }
    }

    fn apply_direct_callable(
        &mut self,
        callable: DirectCallable,
        head: &Atom,
        args: &[Atom],
    ) -> CExpr {
        let lowered_args = self.lower_direct_call_args(head, args);
        match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        }
    }

    fn lower_partial_direct_callable(
        &mut self,
        callable: DirectCallable,
        head: &Atom,
        args: &[Atom],
    ) -> CExpr {
        let missing = callable.arity.saturating_sub(args.len());
        let params: Vec<String> = (0..missing)
            .map(|index| self.fresh_cps_temp(&format!("_PartialArg{index}")))
            .collect();
        let mut lowered_args = self.lower_direct_call_args(head, args);
        lowered_args.extend(params.iter().cloned().map(CExpr::Var));
        let body = match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        };
        CExpr::Fun(params, Box::new(body))
    }

    fn lower_partial_local_callable(
        &mut self,
        name: &str,
        arity: usize,
        head: &Atom,
        args: &[Atom],
    ) -> CExpr {
        let missing = arity.saturating_sub(args.len());
        let params: Vec<String> = (0..missing)
            .map(|index| self.fresh_cps_temp(&format!("_PartialArg{index}")))
            .collect();
        let mut lowered_args = self.lower_direct_call_args(head, args);
        lowered_args.extend(params.iter().cloned().map(CExpr::Var));
        CExpr::Fun(
            params,
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(core_var(name))),
                lowered_args,
            )),
        )
    }

    fn lower_direct_call_args(&mut self, head: &Atom, args: &[Atom]) -> Vec<CExpr> {
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        args.iter()
            .enumerate()
            .map(
                |(index, arg)| match expected_arg_shapes.get(index).copied().flatten() {
                    Some((source_arity, adapter_arity))
                        if !matches!(
                            arg,
                            Atom::Lambda { params, body, .. }
                                if self.lambda_is_direct_subset(params, body)
                        ) =>
                    {
                        self.lower_cps_runtime_value_atom(arg, source_arity, adapter_arity)
                    }
                    None => self.lower_atom(arg),
                    Some(_) => self.lower_atom(arg),
                },
            )
            .collect()
    }

    fn lower_direct_cps_entry_call(
        &mut self,
        module: Option<String>,
        name: &str,
        source_arity: usize,
        adapter_arity: usize,
        head: &Atom,
        args: &[Atom],
    ) -> CExpr {
        self.assert_app_arity(name, args.len(), source_arity);
        self.assert_app_arity(name, args.len() + 2, adapter_arity);
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        let mut lowered_args: Vec<CExpr> = args
            .iter()
            .enumerate()
            .map(
                |(index, arg)| match expected_arg_shapes.get(index).copied().flatten() {
                    Some((source_arity, adapter_arity)) => {
                        self.lower_cps_runtime_value_atom(arg, source_arity, adapter_arity)
                    }
                    None => self.lower_atom(arg),
                },
            )
            .collect();
        lowered_args.push(CExpr::Tuple(vec![]));
        lowered_args.push(self.identity_cps_continuation());
        match module {
            Some(module) => CExpr::Call(module, name.to_string(), lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(name.to_string(), adapter_arity)),
                lowered_args,
            ),
        }
    }

    fn lower_intrinsic_app(&mut self, intrinsic: IntrinsicId, args: &[Atom]) -> CExpr {
        match intrinsic {
            IntrinsicId::PrintStdout => self.lower_print_intrinsic(args, false),
            IntrinsicId::PrintStderr => self.lower_print_intrinsic(args, true),
            IntrinsicId::Dbg => self.lower_dbg_intrinsic(args),
            IntrinsicId::CatchPanic => self.lower_catch_panic_intrinsic(args),
        }
    }

    fn lower_print_intrinsic(&mut self, args: &[Atom], stderr: bool) -> CExpr {
        if args.len() != 1 {
            self.unsupported(&format!(
                "print intrinsic with {} args; expected 1",
                args.len()
            ));
        }
        let mut fmt_args = vec![
            CExpr::Lit(CLit::Str("~ts".to_string())),
            CExpr::Cons(Box::new(self.lower_atom(&args[0])), Box::new(CExpr::Nil)),
        ];
        if stderr {
            fmt_args.insert(0, CExpr::Lit(CLit::Atom("standard_error".to_string())));
        }
        CExpr::Let(
            "_PrintResult".to_string(),
            Box::new(CExpr::Call(
                "io".to_string(),
                "format".to_string(),
                fmt_args,
            )),
            Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
        )
    }

    fn lower_dbg_intrinsic(&mut self, args: &[Atom]) -> CExpr {
        if args.len() != 2 {
            self.unsupported(&format!(
                "dbg intrinsic with {} args; expected 2",
                args.len()
            ));
        }
        let debug_fn_var = "_DebugFn".to_string();
        let str_var = "_DebugStr".to_string();
        let print_result_var = "_DebugPrintResult".to_string();
        let extract = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(1)), self.lower_atom(&args[0])],
        );
        let debug_call = CExpr::Apply(
            Box::new(CExpr::Var(debug_fn_var.clone())),
            vec![self.lower_atom(&args[1])],
        );
        let print = CExpr::Call(
            "io".to_string(),
            "format".to_string(),
            vec![
                CExpr::Lit(CLit::Atom("standard_error".to_string())),
                CExpr::Lit(CLit::Str("~ts~n".to_string())),
                CExpr::Cons(Box::new(CExpr::Var(str_var.clone())), Box::new(CExpr::Nil)),
            ],
        );
        CExpr::Let(
            debug_fn_var,
            Box::new(extract),
            Box::new(CExpr::Let(
                str_var,
                Box::new(debug_call),
                Box::new(CExpr::Let(
                    print_result_var,
                    Box::new(print),
                    Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
                )),
            )),
        )
    }

    fn lower_catch_panic_intrinsic(&mut self, args: &[Atom]) -> CExpr {
        if args.len() != 1 {
            self.unsupported(&format!(
                "catch_panic intrinsic with {} args; expected 1",
                args.len()
            ));
        }

        let f_var = self.fresh_cps_temp("_CatchPanicF");
        let result_var = self.fresh_cps_temp("_CatchPanicResult");
        let ok_var = self.fresh_cps_temp("_CatchPanicOk");
        let class_var = self.fresh_cps_temp("_CatchPanicClass");
        let reason_var = self.fresh_cps_temp("_CatchPanicReason");
        let trace_var = self.fresh_cps_temp("_CatchPanicTrace");
        let msg_var = self.fresh_cps_temp("_CatchPanicMsg");

        let apply_thunk = CExpr::Apply(
            Box::new(CExpr::Var(f_var.clone())),
            vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
        );
        let ok_body = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("ok".to_string())),
            CExpr::Var(ok_var.clone()),
        ]);
        let catch_body = CExpr::Case(
            Box::new(CExpr::Var(reason_var.clone())),
            vec![
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Lit(CLit::Atom("saga_error".to_string())),
                        CPat::Wildcard,
                        CPat::Var(msg_var.clone()),
                        CPat::Wildcard,
                        CPat::Wildcard,
                        CPat::Wildcard,
                        CPat::Wildcard,
                    ]),
                    guard: None,
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom("error".to_string())),
                        CExpr::Var(msg_var),
                    ]),
                },
                CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom("error".to_string())),
                        CExpr::Call(
                            "saga_runtime".to_string(),
                            "format_caught_panic".to_string(),
                            vec![
                                CExpr::Var(class_var.clone()),
                                CExpr::Var(reason_var.clone()),
                            ],
                        ),
                    ]),
                },
            ],
        );
        let try_expr = CExpr::Try {
            expr: Box::new(apply_thunk),
            ok_var,
            ok_body: Box::new(ok_body),
            catch_vars: (class_var, reason_var, trace_var),
            catch_body: Box::new(catch_body),
        };

        CExpr::Let(
            f_var,
            Box::new(self.lower_atom(&args[0])),
            Box::new(CExpr::Let(
                result_var.clone(),
                Box::new(try_expr),
                Box::new(CExpr::Var(result_var)),
            )),
        )
    }

    fn lower_panic_or_todo(&mut self, name: &str, msg_atom: &Atom) -> CExpr {
        let kind_atom = if name == "todo" { "todo" } else { "panic" };
        let msg = if name == "todo" {
            crate::codegen::lower::util::lower_string_to_binary("not implemented")
        } else {
            self.lower_atom(msg_atom)
        };
        let msg_var = self.fresh_cps_temp("_PanicMsg");
        let err_term = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("saga_error".to_string())),
            CExpr::Lit(CLit::Atom(kind_atom.to_string())),
            CExpr::Var(msg_var.clone()),
            crate::codegen::lower::util::lower_string_to_binary(""),
            crate::codegen::lower::util::lower_string_to_binary(""),
            crate::codegen::lower::util::lower_string_to_binary(""),
            CExpr::Lit(CLit::Int(0)),
        ]);
        CExpr::Let(
            msg_var,
            Box::new(msg),
            Box::new(CExpr::Call(
                "erlang".to_string(),
                "error".to_string(),
                vec![err_term],
            )),
        )
    }

    pub(super) fn lower_atom(&mut self, atom: &Atom) -> CExpr {
        match atom {
            Atom::Var { name, .. } => {
                if let Some(atom) = self.known_direct_atom(&name.name) {
                    return self.lower_atom(&atom);
                }
                if self.is_local(&name.name) {
                    if matches!(
                        self.local_shape(&name.name),
                        Some(
                            LocalValueShape::CpsCallable { .. }
                                | LocalValueShape::RuntimeCpsCallable { .. }
                        )
                    ) {
                        return self.lower_cps_value_atom(atom);
                    }
                    CExpr::Var(core_var(&name.name))
                } else if self.cps_value_atom_shape(atom).is_some() {
                    self.lower_cps_value_atom(atom)
                } else if let Some(value_ref) = self.direct_function_value_ref(atom) {
                    value_ref
                } else if self.direct_values.contains(&name.name) {
                    CExpr::Apply(Box::new(CExpr::FunRef(name.name.clone(), 0)), vec![])
                } else {
                    self.unsupported(&format!("non-local atom '{}'", name.name))
                }
            }
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Ctor { name, args, .. } => self.lower_ctor_atom(name, args),
            Atom::Tuple { elements, .. } => {
                CExpr::Tuple(elements.iter().map(|arg| self.lower_atom(arg)).collect())
            }
            Atom::AnonRecord { fields, .. } => self.lower_anon_record_atom(fields),
            Atom::Record { name, fields, .. } => self.lower_record_atom(name, fields),
            Atom::Lambda { params, body, .. } => {
                if self.lambda_is_direct_subset(params, body) {
                    self.lower_lambda_atom(params, body)
                } else if self.cps_value_atom_shape(atom).is_some() {
                    self.lower_cps_value_atom(atom)
                } else if self.lambda_is_direct_cps_island_subset(params, body) {
                    self.lower_direct_cps_island_lambda_atom(params, body)
                } else {
                    self.lower_lambda_atom(params, body)
                }
            }
            Atom::Symbol { symbol, .. } => {
                crate::codegen::lower::util::lower_string_to_binary(symbol)
            }
            Atom::QualifiedRef { .. } => {
                if self.cps_value_atom_shape(atom).is_some() {
                    self.lower_cps_value_atom(atom)
                } else {
                    self.direct_function_value_ref(atom)
                        .unwrap_or_else(|| self.unsupported_atom(atom))
                }
            }
            Atom::BackendAtom { atom, .. } => CExpr::Lit(CLit::Atom(atom.clone())),
            Atom::BackendSpawnThunk { callback, source } => {
                self.lower_backend_spawn_thunk(callback, *source)
            }
            Atom::DictRef { .. } => self.unsupported_atom(atom),
        }
    }

    pub(super) fn lower_backend_spawn_thunk(&mut self, callback: &Atom, source: NodeId) -> CExpr {
        let callback_expr = self.lower_effect_protocol_arg_atom(callback);
        let k_var = format!("_SpawnK{}", source.0);
        let v_var = format!("_SpawnV{}", source.0);
        let identity_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
        let apply_callback = CExpr::Apply(
            Box::new(callback_expr),
            vec![
                CExpr::Lit(CLit::Atom("unit".to_string())),
                CExpr::Tuple(vec![]),
                CExpr::Var(k_var.clone()),
            ],
        );
        CExpr::Fun(
            vec![],
            Box::new(CExpr::Let(
                k_var,
                Box::new(identity_k),
                Box::new(apply_callback),
            )),
        )
    }

    fn lower_lambda_atom(&mut self, params: &[Pat], body: &MExpr) -> CExpr {
        if params.iter().any(|p| !direct_param_supported(p)) {
            self.unsupported("direct lambda with unsupported parameter pattern");
        }
        let param_names = lower_param_names(params);
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let lowered_body = self.lower_expr(body);
        let lowered_body = self.wrap_param_match(params, &param_names, lowered_body);
        self.pop_scope();
        CExpr::Fun(param_names, Box::new(lowered_body))
    }

    pub(super) fn lower_direct_cps_island_lambda_atom(
        &mut self,
        params: &[Pat],
        body: &MExpr,
    ) -> CExpr {
        if params.iter().any(|p| !direct_param_supported(p)) {
            self.unsupported("direct CPS-island lambda with unsupported parameter pattern");
        }
        let param_names = lower_param_names(params);
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let return_k = self.identity_cps_continuation();
        let lowered_body = self.lower_cps_expr(body, CExpr::Tuple(vec![]), return_k);
        let lowered_body = self.wrap_param_match(params, &param_names, lowered_body);
        self.pop_scope();
        CExpr::Fun(param_names, Box::new(lowered_body))
    }

    pub(super) fn lower_dict_constructor(&mut self, dc: &MDictConstructor) -> CFunDef {
        let mut methods = Vec::with_capacity(dc.methods.len());
        self.push_scope();
        for dict_param in &dc.dict_params {
            self.current_scope_mut().insert(dict_param.clone());
        }
        for (index, method) in dc.methods.iter().enumerate() {
            let effectful = dc
                .method_effects
                .get(index)
                .is_some_and(|effects| !effects.is_empty())
                || dc.method_open_rows.get(index).copied().unwrap_or(false);

            let lowered = match method {
                MExpr::Pure(Atom::Lambda { params, body, .. }) if effectful => {
                    self.lower_cps_lambda_atom(params, body)
                }
                MExpr::Pure(Atom::Lambda { params, body, .. }) => {
                    self.lower_lambda_atom(params, body)
                }
                _ if !effectful => self.lower_expr(method),
                _ => self.unsupported(&format!(
                    "dict constructor '{}' method {} is not a lowerable method value",
                    dc.name, index
                )),
            };
            methods.push(lowered);
        }
        self.pop_scope();

        CFunDef {
            name: dc.name.clone(),
            arity: dc.dict_params.len(),
            body: CExpr::Fun(
                dc.dict_params.iter().map(|param| core_var(param)).collect(),
                Box::new(CExpr::Tuple(methods)),
            ),
        }
    }

    fn lower_ctor_atom(&mut self, name: &str, args: &[Atom]) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            return CExpr::Cons(
                Box::new(self.lower_atom(&args[0])),
                Box::new(self.lower_atom(&args[1])),
            );
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(args.iter().map(|arg| self.lower_atom(arg)));
        CExpr::Tuple(elems)
    }

    pub(super) fn known_direct_atom_for_expr(&mut self, expr: &MExpr) -> Option<Atom> {
        match expr {
            MExpr::Pure(atom) => self.known_direct_atom_for_atom(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let value = self.known_direct_atom_for_expr(value)?;
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                self.current_known_direct_atom_scope_mut()
                    .insert(var.name.clone(), value);
                let body = self.known_direct_atom_for_expr(body);
                self.pop_scope();
                body
            }
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self.known_direct_field_value(record, field, record_name.as_deref(), anon_fields),
            MExpr::App { head, args, .. } => self.known_direct_atom_for_lambda_app(head, args),
            _ => None,
        }
    }

    fn known_direct_atom_for_lambda_app(&mut self, head: &Atom, args: &[Atom]) -> Option<Atom> {
        let lambda = self.known_direct_lambda_for_atom(head)?;
        if lambda.params.len() != args.len()
            || lambda
                .params
                .iter()
                .any(|param| !direct_param_supported(param))
        {
            return None;
        }

        let dict_aliases = self.known_dict_aliases_for_bindings(&lambda.dict_bindings);
        let mut atom_bindings = Vec::new();
        for (param, arg) in lambda.params.iter().zip(args) {
            let arg = self.known_direct_atom_for_atom(arg)?;
            atom_bindings.extend(self.match_known_direct_atom_pattern(&arg, param)?);
        }

        self.push_scope();
        for (name, _) in &lambda.dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        for (name, dict) in dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        for pat in &lambda.params {
            self.bind_pat_locals(pat);
        }
        self.bind_known_direct_atom_pattern_values(atom_bindings);
        let body = self.known_direct_atom_for_expr(&lambda.body);
        self.pop_scope();
        body
    }

    pub(super) fn known_direct_atom_for_case_scrutinee(&self, atom: &Atom) -> Option<Atom> {
        match atom {
            Atom::Var { name, .. } => self.known_direct_atom(&name.name),
            _ => self.known_direct_atom_for_atom(atom),
        }
    }

    pub(super) fn known_direct_atom_for_atom(&self, atom: &Atom) -> Option<Atom> {
        match atom {
            Atom::Lit { .. } => Some(atom.clone()),
            Atom::Ctor { name, args, source } => Some(Atom::Ctor {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        self.known_direct_atom_for_atom(arg)
                            .unwrap_or_else(|| arg.clone())
                    })
                    .collect(),
                source: *source,
            }),
            Atom::Tuple { elements, source } => Some(Atom::Tuple {
                elements: elements
                    .iter()
                    .map(|arg| {
                        self.known_direct_atom_for_atom(arg)
                            .unwrap_or_else(|| arg.clone())
                    })
                    .collect(),
                source: *source,
            }),
            Atom::AnonRecord { fields, source } => Some(Atom::AnonRecord {
                fields: self.known_direct_atom_fields(fields),
                source: *source,
            }),
            Atom::Record {
                name,
                fields,
                source,
            } => Some(Atom::Record {
                name: name.clone(),
                fields: self.known_direct_atom_fields(fields),
                source: *source,
            }),
            Atom::Var { name, .. } => self.known_direct_atom(&name.name),
            _ => None,
        }
    }

    fn known_direct_atom_fields(&self, fields: &[(String, Atom)]) -> Vec<(String, Atom)> {
        fields
            .iter()
            .map(|(name, atom)| {
                (
                    name.clone(),
                    self.known_direct_atom_for_atom(atom)
                        .unwrap_or_else(|| atom.clone()),
                )
            })
            .collect()
    }

    fn known_direct_field_value(
        &self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        anon_fields: &Option<Vec<String>>,
    ) -> Option<Atom> {
        match self.known_direct_atom_for_case_scrutinee(record)? {
            Atom::Record { name, fields, .. } => {
                if let Some(expected_name) = record_name
                    && mangle_ctor_atom(&name, self.ctors)
                        != mangle_ctor_atom(expected_name, self.ctors)
                {
                    return None;
                }
                fields
                    .into_iter()
                    .find_map(|(name, atom)| (name == field).then_some(atom))
            }
            Atom::AnonRecord { fields, .. } => {
                if let Some(expected_fields) = anon_fields
                    && !same_field_set(
                        &fields
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>(),
                        expected_fields,
                    )
                {
                    return None;
                }
                fields
                    .into_iter()
                    .find_map(|(name, atom)| (name == field).then_some(atom))
            }
            _ => None,
        }
    }

    pub(super) fn bind_known_direct_atom_pattern_values(&mut self, bindings: Vec<(String, Atom)>) {
        for (name, atom) in bindings {
            if matches!(&atom, Atom::Var { name: atom_name, .. } if atom_name.name == name) {
                continue;
            }
            self.current_known_direct_atom_scope_mut()
                .insert(name, atom);
        }
    }

    pub(super) fn match_known_direct_atom_pattern(
        &self,
        atom: &Atom,
        pat: &Pat,
    ) -> Option<Vec<(String, Atom)>> {
        match pat {
            Pat::Wildcard { .. } => Some(Vec::new()),
            Pat::Var { name, .. } => Some(vec![(name.clone(), atom.clone())]),
            Pat::Lit { value, .. } => {
                let Atom::Lit {
                    value: atom_value, ..
                } = atom
                else {
                    return None;
                };
                lit_values_match(atom_value, value).then(Vec::new)
            }
            Pat::Constructor { name, args, .. } => {
                let Atom::Ctor {
                    name: atom_name,
                    args: atom_args,
                    ..
                } = atom
                else {
                    return None;
                };
                if atom_args.len() != args.len()
                    || mangle_ctor_atom(atom_name, self.ctors) != mangle_ctor_atom(name, self.ctors)
                {
                    return None;
                }
                self.match_known_direct_atom_patterns(atom_args, args)
            }
            Pat::Tuple { elements, .. } => {
                let Atom::Tuple {
                    elements: atom_elements,
                    ..
                } = atom
                else {
                    return match elements.as_slice() {
                        [only] => self.match_known_direct_atom_pattern(atom, only),
                        _ => None,
                    };
                };
                if atom_elements.len() != elements.len() {
                    return None;
                }
                self.match_known_direct_atom_patterns(atom_elements, elements)
            }
            Pat::Record {
                name,
                fields,
                as_name,
                ..
            } => {
                let Atom::Record {
                    name: atom_name,
                    fields: atom_fields,
                    ..
                } = atom
                else {
                    return None;
                };
                if mangle_ctor_atom(atom_name, self.ctors) != mangle_ctor_atom(name, self.ctors) {
                    return None;
                }
                let mut bindings = self.match_known_direct_record_fields(atom_fields, fields)?;
                if let Some(as_name) = as_name {
                    bindings.push((as_name.clone(), atom.clone()));
                }
                Some(bindings)
            }
            Pat::AnonRecord { fields, .. } => {
                let Atom::AnonRecord {
                    fields: atom_fields,
                    ..
                } = atom
                else {
                    return None;
                };
                self.match_known_direct_record_fields(atom_fields, fields)
            }
            _ => None,
        }
    }

    fn match_known_direct_atom_patterns(
        &self,
        atoms: &[Atom],
        pats: &[Pat],
    ) -> Option<Vec<(String, Atom)>> {
        let mut bindings = Vec::new();
        for (atom, pat) in atoms.iter().zip(pats) {
            bindings.extend(self.match_known_direct_atom_pattern(atom, pat)?);
        }
        Some(bindings)
    }

    fn match_known_direct_record_fields(
        &self,
        atom_fields: &[(String, Atom)],
        pat_fields: &[(String, Option<Pat>)],
    ) -> Option<Vec<(String, Atom)>> {
        let atom_field_map: HashMap<&str, &Atom> = atom_fields
            .iter()
            .map(|(name, atom)| (name.as_str(), atom))
            .collect();
        let mut bindings = Vec::new();
        for (field_name, pat) in pat_fields {
            let atom = atom_field_map.get(field_name.as_str())?;
            match pat {
                Some(pat) => bindings.extend(self.match_known_direct_atom_pattern(atom, pat)?),
                None => bindings.push((field_name.clone(), (*atom).clone())),
            }
        }
        Some(bindings)
    }

    fn lower_anon_record_atom(&mut self, fields: &[(String, Atom)]) -> CExpr {
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(sorted.into_iter().map(|(_, atom)| self.lower_atom(atom)));
        CExpr::Tuple(elems)
    }

    fn lower_record_atom(&mut self, name: &str, fields: &[(String, Atom)]) -> CExpr {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(fields.iter().map(|(_, atom)| self.lower_atom(atom)));
        CExpr::Tuple(elems)
    }

    pub(super) fn lower_bitstring_value(
        &mut self,
        segments: &[crate::codegen::monadic::ir::MBitSegment],
    ) -> CExpr {
        let mut lowered_segments: Vec<CBinSeg<CExpr>> = Vec::with_capacity(segments.len());
        for segment in segments {
            if let Atom::Lit {
                value: Lit::String(s, kind),
                ..
            } = &segment.value
            {
                let resolved = if kind.is_multiline() {
                    process_string_escapes(s)
                } else {
                    s.clone()
                };
                lowered_segments.extend(resolved.as_bytes().iter().copied().map(CBinSeg::Byte));
                continue;
            }

            let is_binary = segment.specs.contains(&crate::ast::BitSegSpec::Binary);
            let value = self.lower_atom(&segment.value);
            if is_binary && segment.size.is_none() {
                lowered_segments.push(CBinSeg::BinaryAll(value));
                continue;
            }

            let (type_name, default_size, unit) = resolve_bit_segment_meta(&segment.specs);
            let flags = resolve_bit_segment_flags(&segment.specs);
            let size = segment.size.as_ref().map(|size| self.lower_atom(size));
            let size = resolve_bit_segment_size(size, &type_name, default_size);
            lowered_segments.push(CBinSeg::Segment {
                value,
                size,
                unit,
                type_name,
                flags,
            });
        }
        CExpr::Binary(lowered_segments)
    }

    pub(super) fn lower_pat(&self, pat: &Pat) -> CPat {
        match pat {
            Pat::Wildcard { .. } => CPat::Wildcard,
            Pat::Var { name, .. } => CPat::Var(core_var(name)),
            Pat::Lit { value, .. } => match value {
                Lit::String(s, _) => CPat::Binary(
                    s.as_bytes()
                        .iter()
                        .map(|&byte| CBinSeg::Byte(byte))
                        .collect(),
                ),
                _ => CPat::Lit(lower_lit_pat(value)),
            },
            Pat::Tuple { elements, .. } => {
                CPat::Tuple(elements.iter().map(|p| self.lower_pat(p)).collect())
            }
            Pat::Constructor { name, args, .. } => self.lower_ctor_pat(name, args),
            Pat::Record {
                name,
                fields,
                as_name,
                ..
            } => self.lower_record_pat(name, fields, as_name.as_deref()),
            Pat::AnonRecord { fields, .. } => self.lower_anon_record_pat(fields),
            Pat::StringPrefix { prefix, rest, .. } => {
                let mut segs: Vec<CBinSeg<CPat>> = prefix
                    .as_bytes()
                    .iter()
                    .map(|&b| CBinSeg::Byte(b))
                    .collect();
                segs.push(CBinSeg::BinaryAll(self.lower_pat(rest)));
                CPat::Binary(segs)
            }
            Pat::BitStringPat { segments, .. } => {
                let mut segs = Vec::with_capacity(segments.len());
                for segment in segments {
                    if let Pat::Lit {
                        value: Lit::String(s, kind),
                        ..
                    } = &segment.value
                    {
                        let resolved = if kind.is_multiline() {
                            process_string_escapes(s)
                        } else {
                            s.clone()
                        };
                        segs.extend(resolved.as_bytes().iter().copied().map(CBinSeg::Byte));
                        continue;
                    }
                    segs.push(self.lower_bit_segment_pat(segment));
                }
                CPat::Binary(segs)
            }
            Pat::ListPat { .. } | Pat::ConsPat { .. } | Pat::Or { .. } => {
                unreachable!("surface syntax should be desugared before codegen")
            }
        }
    }

    fn lower_bit_segment_pat(&self, segment: &crate::ast::BitSegment<Pat>) -> CBinSeg<CPat> {
        let is_binary = segment.specs.contains(&crate::ast::BitSegSpec::Binary);
        let pat = self.lower_pat(&segment.value);

        if is_binary && segment.size.is_none() {
            return CBinSeg::BinaryAll(pat);
        }

        let (type_name, default_size, unit) = resolve_bit_segment_meta(&segment.specs);
        let flags = resolve_bit_segment_flags(&segment.specs);
        let size = segment.size.as_deref().map(lower_pat_size_expr);
        let size = resolve_bit_segment_size(size, &type_name, default_size);

        CBinSeg::Segment {
            value: pat,
            size,
            unit,
            type_name,
            flags,
        }
    }

    fn lower_record_pat(
        &self,
        name: &str,
        fields: &[(String, Option<Pat>)],
        as_name: Option<&str>,
    ) -> CPat {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
        let field_map: HashMap<&str, Option<&Pat>> = fields
            .iter()
            .map(|(field_name, pat)| (field_name.as_str(), pat.as_ref()))
            .collect();

        match self.record_pat_field_order(name) {
            Some(order) => {
                for field_name in order {
                    match field_map.get(field_name.as_str()) {
                        Some(Some(pat)) => elems.push(self.lower_pat(pat)),
                        Some(None) => elems.push(CPat::Var(core_var(&field_name))),
                        None => elems.push(CPat::Wildcard),
                    }
                }
            }
            None => {
                for (field_name, pat) in fields {
                    match pat {
                        Some(pat) => elems.push(self.lower_pat(pat)),
                        None => elems.push(CPat::Var(core_var(field_name))),
                    }
                }
            }
        }

        let tuple_pat = CPat::Tuple(elems);
        match as_name {
            Some(var) => CPat::Alias(core_var(var), Box::new(tuple_pat)),
            None => tuple_pat,
        }
    }

    fn record_pat_field_order(&self, name: &str) -> Option<Vec<String>> {
        self.effect_info
            .records
            .get(name)
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info.records.get(bare)
            })
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info
                    .records
                    .iter()
                    .find(|(candidate, _)| {
                        candidate
                            .rsplit('.')
                            .next()
                            .is_some_and(|last| last == bare)
                    })
                    .map(|(_, info)| info)
            })
            .map(|info| info.fields.iter().map(|(field, _)| field.clone()).collect())
    }

    fn lower_anon_record_pat(&self, fields: &[(String, Option<Pat>)]) -> CPat {
        let field_names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&field_names);
        let mut sorted_names = field_names;
        sorted_names.sort();
        let field_map: HashMap<&str, Option<&Pat>> = fields
            .iter()
            .map(|(field_name, pat)| (field_name.as_str(), pat.as_ref()))
            .collect();

        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
        for field_name in sorted_names {
            match field_map.get(field_name) {
                Some(Some(pat)) => elems.push(self.lower_pat(pat)),
                Some(None) => elems.push(CPat::Var(core_var(field_name))),
                None => elems.push(CPat::Wildcard),
            }
        }
        CPat::Tuple(elems)
    }

    fn lower_ctor_pat(&self, name: &str, args: &[Pat]) -> CPat {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CPat::Nil,
            "True" if args.is_empty() => return CPat::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CPat::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if bare == "Cons" && args.len() == 2 {
            return CPat::Cons(
                Box::new(self.lower_pat(&args[0])),
                Box::new(self.lower_pat(&args[1])),
            );
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
        elems.extend(args.iter().map(|pat| self.lower_pat(pat)));
        CPat::Tuple(elems)
    }
}

pub(super) fn core_expr_mentions_var(source_name: &str, expr: &CExpr) -> bool {
    let var = core_var(source_name);
    core_expr_mentions_core_var(&var, expr)
}

fn lit_values_match(left: &Lit, right: &Lit) -> bool {
    match (left, right) {
        (Lit::Int(_, left), Lit::Int(_, right)) => left == right,
        (Lit::Float(_, left), Lit::Float(_, right)) => left.to_bits() == right.to_bits(),
        (Lit::String(left, left_kind), Lit::String(right, right_kind)) => {
            left == right && left_kind == right_kind
        }
        (Lit::Bool(left), Lit::Bool(right)) => left == right,
        (Lit::Unit, Lit::Unit) => true,
        _ => false,
    }
}

fn same_field_set(left: &[String], right: &[String]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let left: HashSet<&str> = left.iter().map(String::as_str).collect();
    right.iter().all(|field| left.contains(field.as_str()))
}

pub(super) fn core_expr_mentions_core_var(var: &str, expr: &CExpr) -> bool {
    match expr {
        CExpr::Var(name) => name == var,
        CExpr::Lit(_) | CExpr::Nil | CExpr::FunRef(_, _) => false,
        CExpr::Fun(params, body) => {
            !params.iter().any(|param| param == var) && core_expr_mentions_core_var(var, body)
        }
        CExpr::Let(name, value, body) => {
            core_expr_mentions_core_var(var, value)
                || (name != var && core_expr_mentions_core_var(var, body))
        }
        CExpr::Apply(head, args) => {
            core_expr_mentions_core_var(var, head)
                || args.iter().any(|arg| core_expr_mentions_core_var(var, arg))
        }
        CExpr::Call(_, _, args) | CExpr::Tuple(args) | CExpr::Values(args) => {
            args.iter().any(|arg| core_expr_mentions_core_var(var, arg))
        }
        CExpr::Case(scrutinee, arms) => {
            core_expr_mentions_core_var(var, scrutinee)
                || arms.iter().any(|arm| core_arm_mentions_core_var(var, arm))
        }
        CExpr::Cons(head, tail) => {
            core_expr_mentions_core_var(var, head) || core_expr_mentions_core_var(var, tail)
        }
        CExpr::LetRec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, _, binding)| core_expr_mentions_core_var(var, binding))
                || core_expr_mentions_core_var(var, body)
        }
        CExpr::Receive(arms, timeout, body) => {
            arms.iter().any(|arm| core_arm_mentions_core_var(var, arm))
                || core_expr_mentions_core_var(var, timeout)
                || core_expr_mentions_core_var(var, body)
        }
        CExpr::Try {
            expr,
            ok_var,
            ok_body,
            catch_vars,
            catch_body,
        } => {
            core_expr_mentions_core_var(var, expr)
                || (ok_var != var && core_expr_mentions_core_var(var, ok_body))
                || (catch_vars.0 != var
                    && catch_vars.1 != var
                    && catch_vars.2 != var
                    && core_expr_mentions_core_var(var, catch_body))
        }
        CExpr::Binary(segments) => segments
            .iter()
            .any(|segment| core_expr_bin_segment_mentions_core_var(var, segment)),
        CExpr::Annotated { expr, .. } => core_expr_mentions_core_var(var, expr),
    }
}

fn core_arm_mentions_core_var(var: &str, arm: &CArm) -> bool {
    arm.guard
        .as_ref()
        .is_some_and(|guard| core_expr_mentions_core_var(var, guard))
        || (!core_pat_binds_core_var(var, &arm.pat) && core_expr_mentions_core_var(var, &arm.body))
}

fn core_expr_bin_segment_mentions_core_var(var: &str, segment: &CBinSeg<CExpr>) -> bool {
    match segment {
        CBinSeg::Byte(_) => false,
        CBinSeg::BinaryAll(value) => core_expr_mentions_core_var(var, value),
        CBinSeg::Segment { value, size, .. } => {
            core_expr_mentions_core_var(var, value)
                || matches!(size, BinSegSize::Expr(size) if core_expr_mentions_core_var(var, size))
        }
    }
}

fn core_pat_binds_core_var(var: &str, pat: &CPat) -> bool {
    match pat {
        CPat::Var(name) => name == var,
        CPat::Alias(name, pat) => name == var || core_pat_binds_core_var(var, pat),
        CPat::Lit(_) | CPat::Wildcard | CPat::Nil => false,
        CPat::Tuple(fields) | CPat::Values(fields) => fields
            .iter()
            .any(|field| core_pat_binds_core_var(var, field)),
        CPat::Cons(head, tail) => {
            core_pat_binds_core_var(var, head) || core_pat_binds_core_var(var, tail)
        }
        CPat::Binary(segments) => segments
            .iter()
            .any(|segment| core_pat_bin_segment_binds_core_var(var, segment)),
    }
}

fn core_pat_bin_segment_binds_core_var(var: &str, segment: &CBinSeg<CPat>) -> bool {
    match segment {
        CBinSeg::Byte(_) => false,
        CBinSeg::BinaryAll(value) => core_pat_binds_core_var(var, value),
        CBinSeg::Segment { value, size, .. } => {
            core_pat_binds_core_var(var, value)
                || matches!(size, BinSegSize::Expr(size) if core_expr_mentions_core_var(var, size))
        }
    }
}
