use super::direct_core_refs::{core_expr_mentions_core_var, core_expr_mentions_var};
use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_direct_with(&mut self, handler: &MHandler, body: &MExpr) -> CExpr {
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

    pub(super) fn lower_direct_return_clause(&mut self, value: CExpr, arm: &MHandlerArm) -> CExpr {
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

    pub(super) fn lower_direct_receive(
        &mut self,
        arms: &[MArm],
        after: Option<&(Atom, Box<MExpr>)>,
    ) -> CExpr {
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

    pub(super) fn lower_direct_receive_arm(&mut self, arm: &MArm) -> CArm {
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

    pub(super) fn lower_case_chain(&mut self, scrutinee: &Atom, arms: &[MArm]) -> CExpr {
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

    pub(super) fn lower_field_access(
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

    pub(super) fn record_field_order(
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

    pub(super) fn lower_record_update(
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

    pub(super) fn lower_foreign_call(&mut self, module: &str, func: &str, args: &[Atom]) -> CExpr {
        CExpr::Call(
            module.to_string(),
            func.to_string(),
            args.iter().map(|arg| self.lower_atom(arg)).collect(),
        )
    }

    pub(super) fn try_lower_known_dict_immediate_method_sequence(
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

    pub(super) fn try_lower_immediate_known_dict_method_bind(
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

    pub(super) fn lower_known_dict_method_app(
        &mut self,
        known_dict: &KnownDictValue,
        method_index: usize,
        args: &[Atom],
    ) -> Option<CExpr> {
        if !known_dict.methods_inlineable {
            return None;
        }
        if self.known_dict_method_is_active(known_dict, method_index) {
            return None;
        }
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
        let key = KnownDictMethodKey {
            constructor_name: known_dict.constructor_name.clone(),
            method_index,
        };
        let inserted = self.active_known_dict_methods.insert(key.clone());
        if !self.lambda_is_direct_subset_with_dict_bindings(&dict_bindings, params, body) {
            if inserted {
                self.active_known_dict_methods.remove(&key);
            }
            return None;
        }

        let lowered = self.lower_inline_direct_lambda_app_with_dict_bindings(
            &dict_bindings,
            params,
            body,
            args,
        );
        if inserted {
            self.active_known_dict_methods.remove(&key);
        }
        Some(lowered)
    }

    pub(super) fn known_dict_method_is_active(
        &self,
        known_dict: &KnownDictValue,
        method_index: usize,
    ) -> bool {
        self.active_known_dict_methods
            .contains(&KnownDictMethodKey {
                constructor_name: known_dict.constructor_name.clone(),
                method_index,
            })
    }

    pub(super) fn lambda_is_direct_subset_with_dict_bindings(
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
        self.bind_known_dict_values(known_dict_aliases);
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.expr_is_direct_subset(body);
        self.pop_scope();
        supported
    }

    pub(super) fn lower_inline_direct_lambda_app_with_dict_bindings(
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
        self.bind_known_dict_values(known_dict_aliases);
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

    pub(super) fn lower_known_direct_lambda_value(&mut self, lambda: &KnownDirectLambda) -> CExpr {
        self.lower_partial_known_direct_lambda_value(lambda, &[])
    }

    pub(super) fn lower_partial_known_direct_lambda_value(
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
        self.bind_known_dict_values(known_dict_aliases);
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
}
