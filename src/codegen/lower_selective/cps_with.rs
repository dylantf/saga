use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_with(
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
            return match handler {
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    ..
                } => self.lower_cps_with_dynamic(
                    effects,
                    op_tuple,
                    return_lambda.as_ref(),
                    body,
                    evidence,
                    return_k,
                ),
                MHandler::Native {
                    effects, handler, ..
                } => {
                    let Some(kind) = DirectHandlerKind::from_handler_name(handler) else {
                        self.unsupported("selective CPS with unsupported native handler");
                    };
                    self.direct_handler_stack.push(DirectHandlerFrame::Native {
                        effects: effects.clone(),
                        kind,
                    });
                    let lowered = self.lower_cps_expr(body, evidence, return_k);
                    self.direct_handler_stack.pop();
                    lowered
                }
                _ => self.unsupported(
                    "selective CPS with currently supports static or dynamic handlers only",
                ),
            };
        };

        if self.can_elide_static_handler_install(arms, return_clause.as_ref(), body) {
            return self.lower_cps_with_elided_static_handler(arms, body, evidence, return_k);
        }

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

        let raw_result_k = self.fresh_cps_temp("_RawResultK");
        let raw_result_k_binding = self.identity_cps_continuation();
        let abort_marker = self.fresh_abort_marker();

        let mut current_evidence = evidence.clone();
        let mut bindings = Vec::with_capacity(canonical_effects.len());
        for effect in &canonical_effects {
            let effect_arms = by_effect
                .get_mut(effect)
                .unwrap_or_else(|| self.unsupported("static handler effect without arms"));
            effect_arms.sort_by_key(|arm| arm.op.op_index);
            let op_tuple = self.lower_cps_static_handler_op_tuple(
                effect,
                effect_arms,
                &evidence,
                Some(&abort_marker),
            );
            let entry = CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(effect.clone())), op_tuple]);
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
            let closure = self.lower_cps_return_clause_closure(
                arm,
                evidence.clone(),
                CExpr::Var(raw_result_k.clone()),
            );
            (return_k_name, closure)
        });
        let inner_k = return_binding
            .as_ref()
            .map(|(name, _)| CExpr::Var(name.clone()))
            .unwrap_or_else(|| CExpr::Var(raw_result_k.clone()));
        let prompt_k = self.fresh_cps_temp("_PromptK");
        let prompt_k_binding =
            self.build_result_delimiter_k(&abort_marker, inner_k, CExpr::Var(raw_result_k.clone()));

        self.direct_handler_stack
            .push(DirectHandlerFrame::Static { arms: arms.clone() });
        self.result_delimiter_stack.push(ResultDelimiterFrame {
            effects: canonical_effects.clone(),
            abort_marker: abort_marker.clone(),
        });
        let lowered_body =
            self.lower_cps_expr(body, current_evidence, CExpr::Var(prompt_k.clone()));
        self.result_delimiter_stack.pop();
        self.direct_handler_stack.pop();
        let with_evidence = bindings
            .into_iter()
            .rev()
            .fold(lowered_body, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            });
        let with_prompt = CExpr::Let(
            prompt_k,
            Box::new(prompt_k_binding),
            Box::new(with_evidence),
        );
        let with_return = match return_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(with_prompt)),
            None => with_prompt,
        };
        let wrapped = self.wrap_with_result_delimiter_to_k(with_return, &abort_marker, return_k);
        CExpr::Let(
            raw_result_k,
            Box::new(raw_result_k_binding),
            Box::new(wrapped),
        )
    }

    pub(super) fn result_delimiter_arms(
        &mut self,
        abort_marker: &str,
        local_value_body: impl Fn(CExpr) -> CExpr,
        local_abort_body: impl Fn(CExpr) -> CExpr,
        ordinary_value_body: impl Fn(CExpr) -> CExpr,
    ) -> Vec<CArm> {
        let value_result = self.fresh_cps_temp("_ValueResult");
        let abort_value = self.fresh_cps_temp("_AbortValue");
        let other_value_marker = self.fresh_cps_temp("_OtherValueMarker");
        let other_value = self.fresh_cps_temp("_OtherValue");
        let other_abort_marker = self.fresh_cps_temp("_OtherAbortMarker");
        let other_abort_value = self.fresh_cps_temp("_OtherAbortValue");
        let ordinary = self.fresh_cps_temp("_WithValue");
        vec![
            CArm {
                pat: marked_control_pattern(
                    VALUE_RESULT_TAG,
                    CPat::Lit(CLit::Atom(abort_marker.to_string())),
                    value_result.clone(),
                ),
                guard: None,
                body: local_value_body(CExpr::Var(value_result)),
            },
            CArm {
                pat: marked_control_pattern(
                    ABORT_TAG,
                    CPat::Lit(CLit::Atom(abort_marker.to_string())),
                    abort_value.clone(),
                ),
                guard: None,
                body: local_abort_body(CExpr::Var(abort_value)),
            },
            propagate_marked_control_arm(VALUE_RESULT_TAG, other_value_marker, other_value),
            propagate_marked_control_arm(ABORT_TAG, other_abort_marker, other_abort_value),
            CArm {
                pat: CPat::Var(ordinary.clone()),
                guard: None,
                body: ordinary_value_body(CExpr::Var(ordinary)),
            },
        ]
    }

    pub(super) fn build_result_delimiter_k(
        &mut self,
        abort_marker: &str,
        success_k: CExpr,
        abort_k: CExpr,
    ) -> CExpr {
        let result = self.fresh_cps_temp("_PromptResult");
        let arms = self.result_delimiter_arms(
            abort_marker,
            |value| CExpr::Apply(Box::new(success_k.clone()), vec![value]),
            |value| CExpr::Apply(Box::new(abort_k.clone()), vec![value]),
            |value| CExpr::Apply(Box::new(success_k.clone()), vec![value]),
        );
        CExpr::Fun(
            vec![result.clone()],
            Box::new(CExpr::Case(Box::new(CExpr::Var(result)), arms)),
        )
    }

    pub(super) fn wrap_with_result_delimiter_to_k(
        &mut self,
        body: CExpr,
        abort_marker: &str,
        return_k: CExpr,
    ) -> CExpr {
        let with_result = self.fresh_cps_temp("_WithResult");
        let arms = self.result_delimiter_arms(
            abort_marker,
            |value| CExpr::Apply(Box::new(return_k.clone()), vec![value]),
            |value| CExpr::Apply(Box::new(return_k.clone()), vec![value]),
            |value| CExpr::Apply(Box::new(return_k.clone()), vec![value]),
        );
        CExpr::Let(
            with_result.clone(),
            Box::new(body),
            Box::new(CExpr::Case(Box::new(CExpr::Var(with_result)), arms)),
        )
    }

    pub(super) fn wrap_with_result_delimiter_raw(
        &mut self,
        body: CExpr,
        abort_marker: &str,
    ) -> CExpr {
        let with_result = self.fresh_cps_temp("_WithResult");
        let arms =
            self.result_delimiter_arms(abort_marker, |value| value, |value| value, |value| value);
        CExpr::Let(
            with_result.clone(),
            Box::new(body),
            Box::new(CExpr::Case(Box::new(CExpr::Var(with_result)), arms)),
        )
    }

    pub(super) fn wrap_aborting_handler_arm_result(
        &mut self,
        body: CExpr,
        abort_marker: &str,
    ) -> CExpr {
        let result = self.fresh_cps_temp("_ArmResult");
        let other_value_marker = self.fresh_cps_temp("_OtherValueMarker");
        let other_value = self.fresh_cps_temp("_OtherValue");
        let other_abort_marker = self.fresh_cps_temp("_OtherAbortMarker");
        let other_abort_value = self.fresh_cps_temp("_OtherAbortValue");
        CExpr::Let(
            result.clone(),
            Box::new(body),
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(result)),
                vec![
                    propagate_marked_control_arm(VALUE_RESULT_TAG, other_value_marker, other_value),
                    propagate_marked_control_arm(ABORT_TAG, other_abort_marker, other_abort_value),
                    CArm {
                        pat: CPat::Var("_AbortValue".to_string()),
                        guard: None,
                        body: marked_control_tuple(
                            ABORT_TAG,
                            CExpr::Lit(CLit::Atom(abort_marker.to_string())),
                            CExpr::Var("_AbortValue".to_string()),
                        ),
                    },
                ],
            )),
        )
    }

    pub(super) fn resume_direct_handler_arm_result(&mut self, body: CExpr, arm_k: CExpr) -> CExpr {
        let result = self.fresh_cps_temp("_TailResumeValue");
        CExpr::Let(
            result.clone(),
            Box::new(body),
            Box::new(CExpr::Apply(Box::new(arm_k), vec![CExpr::Var(result)])),
        )
    }

    pub(super) fn lower_cps_with_dynamic(
        &mut self,
        effects: &[String],
        handler_value: &Atom,
        return_lambda: Option<&Atom>,
        body: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        let mut sorted_effects = effects.to_vec();
        sorted_effects.sort();

        let handler_value_var = self.fresh_cps_temp("_HandlerValue");
        let ops_by_effect_var = self.fresh_cps_temp("_HandlerOpsByEffect");
        let runtime_return_var = self.fresh_cps_temp("_HandlerReturn");
        let runtime_ret_k = self.fresh_cps_temp("_HandlerReturnK");
        let runtime_ret_param = self.fresh_cps_temp("_HandlerReturnValue");
        let raw_result_k = self.fresh_cps_temp("_HandlerRawResultK");
        let raw_result_k_binding = self.identity_cps_continuation();

        let handler_value_expr = self.lower_atom(handler_value);
        let ops_by_effect_value = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![
                CExpr::Lit(CLit::Int(2)),
                CExpr::Var(handler_value_var.clone()),
            ],
        );
        let runtime_return_value = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![
                CExpr::Lit(CLit::Int(3)),
                CExpr::Var(handler_value_var.clone()),
            ],
        );

        let ret_binding: Option<(String, CExpr)> = return_lambda.map(|atom| {
            let lowered_return = self.lower_atom(atom);
            let param = self.fresh_cps_temp("_ReturnLambdaValue");
            let wrapper = CExpr::Fun(
                vec![param.clone()],
                Box::new(CExpr::Apply(
                    Box::new(lowered_return),
                    vec![
                        CExpr::Var(param),
                        evidence.clone(),
                        CExpr::Var(raw_result_k.clone()),
                    ],
                )),
            );
            (self.fresh_cps_temp("_ReturnLambdaK"), wrapper)
        });

        let runtime_ret_binding = CExpr::Fun(
            vec![runtime_ret_param.clone()],
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(runtime_return_var.clone())),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("unit".to_string())),
                        guard: None,
                        body: CExpr::Apply(
                            Box::new(CExpr::Var(raw_result_k.clone())),
                            vec![CExpr::Var(runtime_ret_param.clone())],
                        ),
                    },
                    CArm {
                        pat: CPat::Var("_RuntimeReturn".to_string()),
                        guard: None,
                        body: CExpr::Apply(
                            Box::new(CExpr::Var("_RuntimeReturn".to_string())),
                            vec![
                                CExpr::Var(runtime_ret_param),
                                evidence.clone(),
                                CExpr::Var(raw_result_k.clone()),
                            ],
                        ),
                    },
                ],
            )),
        );
        let body_return_k = ret_binding
            .as_ref()
            .map(|(name, _)| CExpr::Var(name.clone()))
            .unwrap_or_else(|| CExpr::Var(runtime_ret_k.clone()));

        let mut install_bindings = Vec::new();
        let mut current_evidence = evidence.clone();
        for (index, effect) in sorted_effects.into_iter().enumerate() {
            let pair_var = self.fresh_cps_temp("_HandlerEffectPair");
            let pair_value = CExpr::Call(
                "erlang".to_string(),
                "element".to_string(),
                vec![
                    CExpr::Lit(CLit::Int(index as i64 + 1)),
                    CExpr::Var(ops_by_effect_var.clone()),
                ],
            );
            install_bindings.push((pair_var.clone(), pair_value));

            let op_tuple_var = self.fresh_cps_temp("_HandlerOpTuple");
            let op_tuple_value = CExpr::Call(
                "erlang".to_string(),
                "element".to_string(),
                vec![CExpr::Lit(CLit::Int(2)), CExpr::Var(pair_var)],
            );
            install_bindings.push((op_tuple_var.clone(), op_tuple_value));

            let entry = CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom(effect)),
                CExpr::Var(op_tuple_var),
            ]);
            let insert = CExpr::Call(
                "std_evidence_bridge".to_string(),
                "insert_canonical".to_string(),
                vec![current_evidence, entry],
            );
            let evidence_var = self.fresh_cps_temp("_CpsEvidence");
            current_evidence = CExpr::Var(evidence_var.clone());
            install_bindings.push((evidence_var, insert));
        }

        let lowered_body = self.lower_cps_expr(body, current_evidence, body_return_k);
        let with_evidence = install_bindings
            .into_iter()
            .rev()
            .fold(lowered_body, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            });
        let with_runtime_return = CExpr::Let(
            runtime_ret_k,
            Box::new(runtime_ret_binding),
            Box::new(with_evidence),
        );
        let with_return_lambda = match ret_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(with_runtime_return)),
            None => with_runtime_return,
        };
        let with_runtime_return_value = CExpr::Let(
            runtime_return_var,
            Box::new(runtime_return_value),
            Box::new(with_return_lambda),
        );
        let with_ops_by_effect = CExpr::Let(
            ops_by_effect_var,
            Box::new(ops_by_effect_value),
            Box::new(with_runtime_return_value),
        );
        let with_handler_value = CExpr::Let(
            handler_value_var,
            Box::new(handler_value_expr),
            Box::new(with_ops_by_effect),
        );

        let with_result = self.fresh_cps_temp("_WithResult");
        let apply_outer_return = CExpr::Let(
            with_result.clone(),
            Box::new(with_handler_value),
            Box::new(CExpr::Apply(
                Box::new(return_k),
                vec![CExpr::Var(with_result)],
            )),
        );
        CExpr::Let(
            raw_result_k,
            Box::new(raw_result_k_binding),
            Box::new(apply_outer_return),
        )
    }

    pub(super) fn lower_cps_with_elided_static_handler(
        &mut self,
        arms: &[MHandlerArm],
        body: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        self.direct_handler_stack.push(DirectHandlerFrame::Static {
            arms: arms.to_vec(),
        });
        let body_return_k = self.identity_cps_continuation();
        let lowered_body = self.lower_cps_expr(body, evidence, body_return_k);
        self.direct_handler_stack.pop();

        let with_result = self.fresh_cps_temp("_WithResult");
        CExpr::Let(
            with_result.clone(),
            Box::new(lowered_body),
            Box::new(CExpr::Apply(
                Box::new(return_k),
                vec![CExpr::Var(with_result)],
            )),
        )
    }

    pub(super) fn can_elide_static_handler_install(
        &mut self,
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
        body: &MExpr,
    ) -> bool {
        let _ = (arms, return_clause, body);
        false
    }

    #[allow(dead_code)]
    pub(super) fn can_elide_static_handler_install_when_specialized(
        &mut self,
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
        body: &MExpr,
    ) -> bool {
        if return_clause.is_some() || arms.is_empty() {
            return false;
        }
        if !arms
            .iter()
            .all(|arm| self.static_handler_arm_can_direct_call(arm))
        {
            return false;
        }

        let handled_effects = self.static_handler_effects(arms);
        self.direct_handler_stack.push(DirectHandlerFrame::Static {
            arms: arms.to_vec(),
        });
        let can_elide = self.expr_can_run_with_elided_static_handler(body, &handled_effects);
        self.direct_handler_stack.pop();
        can_elide
    }

    #[allow(dead_code)]
    pub(super) fn static_handler_arm_can_direct_call(&mut self, arm: &MHandlerArm) -> bool {
        arm.finally_block.is_none()
            && self.handler_info.resumption.get(&arm.id) == Some(&ResumptionKind::TailResumptive)
            && !self.expr_contains_yield(&arm.body)
            && self.direct_call_params_supported(&arm.params)
            && self.handler_arm_expr_is_cps_island_subset(&arm.body)
    }

    #[allow(dead_code)]
    pub(super) fn static_handler_effects(&self, arms: &[MHandlerArm]) -> Vec<String> {
        let mut effects: Vec<String> = Vec::new();
        for arm in arms {
            if !effects
                .iter()
                .any(|effect| Self::effect_names_match(effect, &arm.op.effect))
            {
                effects.push(arm.op.effect.clone());
            }
        }
        effects
    }

    #[allow(dead_code)]
    pub(super) fn expr_can_run_with_elided_static_handler(
        &mut self,
        expr: &MExpr,
        handled_effects: &[String],
    ) -> bool {
        if self.expr_is_direct_subset(expr) {
            return true;
        }

        match expr {
            MExpr::Yield { op, args, .. } => {
                if self.effect_is_handled_by_elided_static_handler(&op.effect, handled_effects) {
                    self.static_direct_call_arm_for_yield(op, args).is_some()
                } else {
                    args.iter().all(|arg| self.atom_is_direct_subset(arg))
                }
            }
            MExpr::Bind {
                var, value, body, ..
            } => {
                let known_lambda = self.known_cps_lambda_for_expr(value);
                let known_dict = self.known_dict_value_for_expr(value);
                let value_supported = self
                    .expr_can_run_with_elided_static_handler(value, handled_effects)
                    || self.cps_bind_value_expr_is_supported(value);
                if !value_supported {
                    return false;
                }

                let local_shape = self
                    .direct_local_shape_for_expr(value)
                    .or_else(|| self.cps_bind_shape_for_expr(value));
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                if let Some(lambda) = known_lambda {
                    self.bind_known_cps_lambda(var.name.clone(), lambda);
                }
                if let Some(dict) = known_dict {
                    self.bind_known_dict_value(var.name.clone(), dict);
                }
                let supported = self.expr_can_run_with_elided_static_handler(body, handled_effects);
                self.pop_scope();
                supported
            }
            MExpr::App { head, args, .. } => {
                if let Atom::Var { name, .. } = head
                    && self.known_cps_lambda(&name.name).is_some()
                {
                    return args.iter().all(|arg| self.atom_is_direct_subset(arg));
                }
                if self.cps_call_effects_intersect_elided_static_handler(head, handled_effects) {
                    self.can_static_handler_specialize_local_cps_call_without_evidence(
                        head,
                        args,
                        handled_effects,
                    ) || self.can_static_handler_specialize_imported_cps_call_without_evidence(
                        head,
                        args,
                        handled_effects,
                    )
                } else {
                    self.cps_app_is_supported_without_elided_effects(head, args)
                }
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.expr_can_run_with_elided_static_handler(then_branch, handled_effects)
                    && self.expr_can_run_with_elided_static_handler(else_branch, handled_effects)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_can_run_with_elided_static_handler(&arm.body, handled_effects);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::With { .. } => false,
            _ => false,
        }
    }

    #[allow(dead_code)]
    pub(super) fn cps_app_is_supported_without_elided_effects(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> bool {
        if let Some((source_arity, adapter_arity, _effects)) = self.cps_lambda_arity_for_atom(head)
            && self.lambda_is_cps_subset(head)
        {
            return source_arity == args.len()
                && adapter_arity == args.len() + 2
                && args.iter().all(|arg| self.atom_is_cps_value_subset(arg));
        }

        let call_supported = match self.call_shape(head) {
            Some(CallShape::Cps {
                source_arity,
                adapter_arity,
                ..
            })
            | Some(CallShape::LocalCpsCallable {
                source_arity,
                adapter_arity,
                ..
            }) => source_arity == args.len() && adapter_arity == args.len() + 2,
            _ => false,
        };
        call_supported && args.iter().all(|arg| self.atom_is_cps_value_subset(arg))
    }

    #[allow(dead_code)]
    pub(super) fn cps_call_effects_intersect_elided_static_handler(
        &mut self,
        head: &Atom,
        handled_effects: &[String],
    ) -> bool {
        match self.call_shape(head) {
            Some(CallShape::Cps { effects, .. }) => effects.iter().any(|effect| {
                self.effect_is_handled_by_elided_static_handler(effect, handled_effects)
            }),
            Some(CallShape::LocalCpsCallable { effects, .. }) => effects.iter().any(|effect| {
                self.effect_is_handled_by_elided_static_handler(effect, handled_effects)
            }),
            _ => false,
        }
    }

    #[allow(dead_code)]
    pub(super) fn effect_is_handled_by_elided_static_handler(
        &self,
        effect: &str,
        handled_effects: &[String],
    ) -> bool {
        handled_effects
            .iter()
            .any(|handled| Self::effect_names_match(handled, effect))
    }

    #[allow(dead_code)]
    pub(super) fn can_static_handler_specialize_local_cps_call_without_evidence(
        &mut self,
        head: &Atom,
        args: &[Atom],
        handled_effects: &[String],
    ) -> bool {
        let local_name = match head {
            Atom::Var { name, .. } => name.name.clone(),
            _ => return false,
        };
        if self.static_handler_inline_stack.contains(&local_name) {
            return false;
        }

        let Some(CallShape::Cps {
            module: None,
            source_arity,
            adapter_arity,
            effects,
            ..
        }) = self.call_shape(head)
        else {
            return false;
        };
        if effects.is_empty()
            || source_arity != args.len()
            || adapter_arity != args.len() + 2
            || !self.active_static_handlers_cover_effects(&effects)
            || !args.iter().all(|arg| self.atom_is_direct_subset(arg))
        {
            return false;
        }

        let Some(fb) = self.local_fun_bindings.get(&local_name).cloned() else {
            return false;
        };
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        let known_dict_aliases = self.known_dict_aliases_for_params(&fb.params, args);
        let known_atom_bindings =
            self.known_direct_atom_pattern_bindings_for_params(&fb.params, args);

        self.static_handler_inline_stack.push(local_name);
        self.push_scope();
        self.bind_fun_param_locals_with_arg_shapes(&fb, args);
        self.bind_known_dict_values(known_dict_aliases);
        self.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let supported = self.expr_can_run_with_elided_static_handler(&fb.body, handled_effects);
        self.pop_scope();
        self.static_handler_inline_stack.pop();
        supported
    }

    #[allow(dead_code)]
    pub(super) fn can_static_handler_specialize_imported_cps_call_without_evidence(
        &mut self,
        head: &Atom,
        args: &[Atom],
        handled_effects: &[String],
    ) -> bool {
        let Some(ImportedStaticHandlerCall {
            source_module_name,
            erlang_module,
            function_name,
            program,
        }) = self.imported_static_handler_call_candidate(head, args)
        else {
            return false;
        };
        let key = format!("{erlang_module}:{function_name}");
        if self.static_handler_inline_stack.contains(&key) {
            return false;
        }

        let Some(fb) = program.iter().find_map(|decl| match decl {
            MDecl::FunBinding(fb) if fb.name == function_name => Some(fb.clone()),
            _ => None,
        }) else {
            return false;
        };
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        let known_dict_aliases = self.known_dict_aliases_for_params(&fb.params, args);
        let known_atom_bindings =
            self.known_direct_atom_pattern_bindings_for_params(&fb.params, args);

        let Some(compiled) = self.module_ctx.modules.get(&source_module_name) else {
            return false;
        };
        let mut imported = DirectLowerer::new(
            &compiled.resolution,
            self.ctors,
            self.module_ctx,
            self.handler_info,
            self.effect_info,
            self.handler_value_map,
            self.imported_dict_constructors.clone(),
            self.options,
        );
        imported.current_module = source_module_name.clone();
        imported.classify_program(&program);
        imported.apply_codegen_info_function_shapes(&compiled.codegen_info);
        imported.compute_function_lowering_plans(&program);
        imported.compute_local_function_entries(&program);
        for (name, constructor) in &self.local_dict_constructors {
            imported
                .local_dict_constructors
                .entry(name.clone())
                .or_insert_with(|| constructor.clone());
        }
        imported.current_module = self.current_module.clone();
        imported.imported_clone_source_module = Some(source_module_name);
        imported.locals = self.locals.clone();
        imported.local_shapes = self.local_shapes.clone();
        imported.direct_handler_stack = self.direct_handler_stack.clone();
        imported.result_delimiter_stack = self.result_delimiter_stack.clone();
        imported.static_handler_inline_stack = self.static_handler_inline_stack.clone();
        imported.static_handler_inline_stack.push(key);

        imported.push_scope();
        imported.bind_fun_param_locals(&fb);
        imported.bind_known_dict_values(known_dict_aliases);
        imported.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let supported = imported.expr_can_run_with_elided_static_handler(&fb.body, handled_effects);
        imported.pop_scope();
        supported
    }
}
