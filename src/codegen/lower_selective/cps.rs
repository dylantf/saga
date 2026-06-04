use super::*;

struct ImportedStaticHandlerCall {
    source_module_name: String,
    erlang_module: String,
    function_name: String,
    program: MProgram,
}

enum CpsCallDecision {
    HofDirect {
        module: Option<String>,
        specialization: HofDirectSpecialization,
    },
    StaticHandlerLocal {
        function_name: String,
    },
    StaticHandlerImported(ImportedStaticHandlerCall),
    KnownLocalLambda {
        name: String,
    },
    Lambda,
    Normal(CallShape),
    Direct,
    Unsupported,
}

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_expr(
        &mut self,
        expr: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        match expr {
            MExpr::Yield { op, args, .. } => self.lower_cps_yield(op, args, evidence, return_k),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
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
            } => self.lower_cps_case_chain(scrutinee, arms, evidence, return_k),
            MExpr::Receive { arms, after, .. } => {
                self.lower_cps_receive(arms, after.as_ref(), evidence, return_k)
            }
            MExpr::App { head, args, .. } if self.expr_is_direct_subset(expr) => {
                CExpr::Apply(Box::new(return_k), vec![self.lower_app(head, args)])
            }
            MExpr::App { head, args, .. } => self.lower_cps_app(head, args, evidence, return_k),
            MExpr::With { handler, body, .. } => {
                self.lower_cps_with(handler, body, evidence, return_k)
            }
            MExpr::BinOp {
                op, left, right, ..
            } => CExpr::Apply(
                Box::new(return_k),
                vec![binop_atoms(
                    op,
                    self.lower_atom(left),
                    self.lower_atom(right),
                )],
            ),
            MExpr::UnaryMinus { value, .. } => CExpr::Apply(
                Box::new(return_k),
                vec![CExpr::Call(
                    "erlang".to_string(),
                    "-".to_string(),
                    vec![CExpr::Lit(CLit::Int(0)), self.lower_atom(value)],
                )],
            ),
            MExpr::BitString { segments, .. } => CExpr::Apply(
                Box::new(return_k),
                vec![self.lower_bitstring_value(segments)],
            ),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => CExpr::Apply(
                Box::new(return_k),
                vec![self.lower_cps_handler_value(arms, return_clause.as_deref(), evidence)],
            ),
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

        if let Some(known_lambda) = self.known_cps_lambda_for_expr(value)
            && let Some(local_shape) = self.cps_bind_shape_for_expr(value)
        {
            let needs_value = self.known_cps_lambda_value_needed_in_expr(&var.name, body);
            let lowered_value =
                needs_value.then(|| self.lower_known_cps_lambda_value(&known_lambda));
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            self.current_shape_scope_mut()
                .insert(var.name.clone(), local_shape);
            self.current_known_cps_lambda_scope_mut()
                .insert(var.name.clone(), known_lambda);
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

        if self.expr_is_direct_subset(value) {
            let local_shape = self.direct_local_shape_for_expr(value);
            let known_dict = self.known_dict_value_for_expr(value);
            let lowered_value = self.lower_expr(value);
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            if let Some(shape) = local_shape {
                self.current_shape_scope_mut()
                    .insert(var.name.clone(), shape);
            }
            if let Some(dict) = known_dict {
                self.current_known_dict_value_scope_mut()
                    .insert(var.name.clone(), dict);
            }
            let lowered_body = self.lower_cps_expr(body, evidence, return_k);
            self.pop_scope();
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

    fn lower_cps_yield(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        if let Some(lowered) =
            self.lower_native_direct_call_yield(op, args, evidence.clone(), return_k.clone())
        {
            return lowered;
        }

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

        let mut apply_args: Vec<CExpr> = args
            .iter()
            .map(|arg| self.lower_effect_protocol_arg_atom(arg))
            .collect();
        apply_args.push(evidence);
        apply_args.push(self.delimited_perform_k(&op.effect, return_k));
        CExpr::Apply(Box::new(op_closure), apply_args)
    }

    fn lower_native_direct_call_yield(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let result = self.lower_native_direct_call_yield_result(op, args, evidence)?;
        Some(CExpr::Apply(Box::new(return_k), vec![result]))
    }

    pub(super) fn lower_native_direct_call_yield_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
    ) -> Option<CExpr> {
        let kind = self.native_direct_handler_kind_for_yield(op)?;
        match kind {
            DirectHandlerKind::BeamActor | DirectHandlerKind::BeamSignal => {
                self.lower_native_table_direct_call_result(op, args)
            }
            DirectHandlerKind::BeamRef => {
                self.lower_beam_ref_direct_call_result(op, args, evidence)
            }
            DirectHandlerKind::EtsRef => self.lower_ets_ref_direct_call_result(op, args, evidence),
            DirectHandlerKind::BeamVec => None,
        }
    }

    pub(super) fn native_direct_handler_kind_for_yield(
        &self,
        op: &EffectOpRef,
    ) -> Option<DirectHandlerKind> {
        for frame in self.direct_handler_stack.iter().rev() {
            if !frame.handles_effect(&op.effect) {
                continue;
            }
            return match frame {
                DirectHandlerFrame::Native { kind, .. } => Some(*kind),
                DirectHandlerFrame::Static { .. } => None,
            };
        }
        None
    }

    fn lower_native_table_direct_call_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
    ) -> Option<CExpr> {
        let spec = native_op(&op.effect, &op.op)?;
        if spec.erl_module.is_empty() || args.len() != spec.param_count {
            return None;
        }
        let args = self.lower_native_table_args(spec.arg_transform, args)?;
        Some(CExpr::Call(
            spec.erl_module.to_string(),
            spec.erl_func.to_string(),
            args,
        ))
    }

    fn lower_native_table_args(
        &mut self,
        transform: NativeArgTransform,
        args: &[Atom],
    ) -> Option<Vec<CExpr>> {
        match transform {
            NativeArgTransform::Identity => {
                Some(args.iter().map(|arg| self.lower_atom(arg)).collect())
            }
            NativeArgTransform::NoArgs => Some(Vec::new()),
            NativeArgTransform::PrependAtom(atom) => {
                let mut lowered = Vec::with_capacity(args.len() + 1);
                lowered.push(CExpr::Lit(CLit::Atom(atom.to_string())));
                lowered.extend(args.iter().map(|arg| self.lower_atom(arg)));
                Some(lowered)
            }
            NativeArgTransform::Reorder(indices) => {
                let mut lowered = Vec::with_capacity(indices.len());
                for &idx in indices {
                    lowered.push(self.lower_atom(args.get(idx)?));
                }
                Some(lowered)
            }
            NativeArgTransform::WrapThunk(idx) => {
                let mut lowered = Vec::with_capacity(args.len());
                for (arg_idx, arg) in args.iter().enumerate() {
                    if arg_idx == idx {
                        lowered.push(self.lower_backend_spawn_thunk(arg, NodeId(0)));
                    } else {
                        lowered.push(self.lower_atom(arg));
                    }
                }
                Some(lowered)
            }
        }
    }

    fn lower_beam_ref_direct_call_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
    ) -> Option<CExpr> {
        if op.effect != "Std.Ref.Ref" {
            return None;
        }
        match op.op.as_str() {
            "get" if args.len() == 1 => Some(CExpr::Call(
                "erlang".to_string(),
                "get".to_string(),
                vec![self.lower_atom(&args[0])],
            )),
            "set" if args.len() == 2 => {
                let discard = self.fresh_cps_temp("_NativeRefPut");
                Some(CExpr::Let(
                    discard,
                    Box::new(CExpr::Call(
                        "erlang".to_string(),
                        "put".to_string(),
                        vec![self.lower_atom(&args[0]), self.lower_atom(&args[1])],
                    )),
                    Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
                ))
            }
            "new" if args.len() == 1 => {
                let key = self.fresh_cps_temp("_NativeRefKey");
                let discard = self.fresh_cps_temp("_NativeRefPut");
                Some(CExpr::Let(
                    key.clone(),
                    Box::new(CExpr::Call(
                        "erlang".to_string(),
                        "make_ref".to_string(),
                        Vec::new(),
                    )),
                    Box::new(CExpr::Let(
                        discard,
                        Box::new(CExpr::Call(
                            "erlang".to_string(),
                            "put".to_string(),
                            vec![CExpr::Var(key.clone()), self.lower_atom(&args[0])],
                        )),
                        Box::new(CExpr::Var(key)),
                    )),
                ))
            }
            "modify" if args.len() == 2 => {
                let key = self.lower_atom(&args[0]);
                let callback = self.lower_effect_protocol_arg_atom(&args[1]);
                self.lower_ref_modify_direct_call_result(
                    key,
                    callback,
                    evidence,
                    RefDirectBackend::ProcessDictionary,
                )
            }
            _ => None,
        }
    }

    fn lower_ets_ref_direct_call_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
    ) -> Option<CExpr> {
        if op.effect != "Std.Ref.Ref" {
            return None;
        }
        let table = CExpr::Lit(CLit::Atom("saga_ref_store".to_string()));
        match op.op.as_str() {
            "get" if args.len() == 1 => {
                let lookup = self.fresh_cps_temp("_NativeRefLookup");
                let value = self.fresh_cps_temp("_NativeRefValue");
                Some(CExpr::Let(
                    lookup.clone(),
                    Box::new(CExpr::Call(
                        "ets".to_string(),
                        "lookup".to_string(),
                        vec![table, self.lower_atom(&args[0])],
                    )),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(lookup)),
                        vec![CArm {
                            pat: CPat::Cons(
                                Box::new(CPat::Tuple(vec![
                                    CPat::Wildcard,
                                    CPat::Var(value.clone()),
                                ])),
                                Box::new(CPat::Nil),
                            ),
                            guard: None,
                            body: CExpr::Var(value),
                        }],
                    )),
                ))
            }
            "set" if args.len() == 2 => {
                let discard = self.fresh_cps_temp("_NativeRefInsert");
                Some(CExpr::Let(
                    discard,
                    Box::new(CExpr::Call(
                        "ets".to_string(),
                        "insert".to_string(),
                        vec![
                            table,
                            CExpr::Tuple(vec![
                                self.lower_atom(&args[0]),
                                self.lower_atom(&args[1]),
                            ]),
                        ],
                    )),
                    Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
                ))
            }
            "new" if args.len() == 1 => {
                let key = self.fresh_cps_temp("_NativeRefKey");
                let discard = self.fresh_cps_temp("_NativeRefInsert");
                Some(CExpr::Let(
                    key.clone(),
                    Box::new(CExpr::Call(
                        "erlang".to_string(),
                        "make_ref".to_string(),
                        Vec::new(),
                    )),
                    Box::new(CExpr::Let(
                        discard,
                        Box::new(CExpr::Call(
                            "ets".to_string(),
                            "insert".to_string(),
                            vec![
                                table,
                                CExpr::Tuple(vec![
                                    CExpr::Var(key.clone()),
                                    self.lower_atom(&args[0]),
                                ]),
                            ],
                        )),
                        Box::new(CExpr::Var(key)),
                    )),
                ))
            }
            "modify" if args.len() == 2 => {
                let key = self.lower_atom(&args[0]);
                let callback = self.lower_effect_protocol_arg_atom(&args[1]);
                self.lower_ref_modify_direct_call_result(
                    key,
                    callback,
                    evidence,
                    RefDirectBackend::Ets,
                )
            }
            _ => None,
        }
    }

    fn lower_ref_modify_direct_call_result(
        &mut self,
        key: CExpr,
        callback: CExpr,
        evidence: CExpr,
        backend: RefDirectBackend,
    ) -> Option<CExpr> {
        let old = self.fresh_cps_temp("_NativeRefOld");
        let new_value = self.fresh_cps_temp("_NativeRefNew");
        let discard = self.fresh_cps_temp("_NativeRefPut");
        let k_var = self.fresh_cps_temp("_NativeRefK");
        let v_var = self.fresh_cps_temp("_NativeRefV");
        let identity_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
        let get_old = match backend {
            RefDirectBackend::ProcessDictionary => {
                CExpr::Call("erlang".to_string(), "get".to_string(), vec![key.clone()])
            }
            RefDirectBackend::Ets => {
                let lookup = self.fresh_cps_temp("_NativeRefLookup");
                let value = self.fresh_cps_temp("_NativeRefLookupValue");
                CExpr::Let(
                    lookup.clone(),
                    Box::new(CExpr::Call(
                        "ets".to_string(),
                        "lookup".to_string(),
                        vec![
                            CExpr::Lit(CLit::Atom("saga_ref_store".to_string())),
                            key.clone(),
                        ],
                    )),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(lookup)),
                        vec![CArm {
                            pat: CPat::Cons(
                                Box::new(CPat::Tuple(vec![
                                    CPat::Wildcard,
                                    CPat::Var(value.clone()),
                                ])),
                                Box::new(CPat::Nil),
                            ),
                            guard: None,
                            body: CExpr::Var(value),
                        }],
                    )),
                )
            }
        };
        let put_new = match backend {
            RefDirectBackend::ProcessDictionary => CExpr::Call(
                "erlang".to_string(),
                "put".to_string(),
                vec![key, CExpr::Var(new_value.clone())],
            ),
            RefDirectBackend::Ets => CExpr::Call(
                "ets".to_string(),
                "insert".to_string(),
                vec![
                    CExpr::Lit(CLit::Atom("saga_ref_store".to_string())),
                    CExpr::Tuple(vec![key, CExpr::Var(new_value.clone())]),
                ],
            ),
        };
        Some(CExpr::Let(
            old.clone(),
            Box::new(get_old),
            Box::new(CExpr::Let(
                k_var.clone(),
                Box::new(identity_k),
                Box::new(CExpr::Let(
                    new_value.clone(),
                    Box::new(CExpr::Apply(
                        Box::new(callback),
                        vec![CExpr::Var(old), evidence, CExpr::Var(k_var)],
                    )),
                    Box::new(CExpr::Let(
                        discard,
                        Box::new(put_new),
                        Box::new(CExpr::Var(new_value)),
                    )),
                )),
            )),
        ))
    }

    fn delimited_perform_k(&mut self, effect: &str, return_k: CExpr) -> CExpr {
        if !self
            .result_delimiter_stack
            .iter()
            .any(|frame| frame.handles_effect(effect))
        {
            return return_k;
        }

        let arg = self.fresh_cps_temp("_DelimitedKArg");
        let applied = CExpr::Apply(Box::new(return_k), vec![CExpr::Var(arg.clone())]);
        let body = self.wrap_result_delimiter_stack_until(applied, effect);
        CExpr::Fun(vec![arg], Box::new(body))
    }

    fn wrap_result_delimiter_stack_until(&mut self, mut body: CExpr, effect: &str) -> CExpr {
        let frames = self.result_delimiter_stack.clone();
        for frame in frames.iter().rev() {
            body = self.wrap_with_result_delimiter_raw(body, &frame.abort_marker);
            if frame.handles_effect(effect) {
                break;
            }
        }
        body
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

    fn lower_static_direct_call_yield_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
    ) -> Option<CExpr> {
        let arm = self.static_direct_call_arm_for_yield(op, args)?;
        let bindings = self.direct_call_param_bindings(&arm.params, args)?;
        let MExpr::Resume { value, .. } = &*arm.body else {
            return None;
        };

        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let lowered_value = self.lower_atom(value);
        self.pop_scope();

        Some(
            bindings
                .into_iter()
                .rev()
                .fold(lowered_value, |body, (name, value)| {
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
        for frame in self.direct_handler_stack.iter().rev() {
            if !frame.handles_effect(&op.effect) {
                continue;
            }
            let DirectHandlerFrame::Static { arms: frame } = frame else {
                return None;
            };

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

    fn classify_cps_call(&mut self, head: &Atom, args: &[Atom]) -> CpsCallDecision {
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

    fn lower_cps_lambda_app(
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

    fn known_cps_lambda_value_needed_in_expr(&self, name: &str, expr: &MExpr) -> bool {
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

    fn known_cps_lambda_value_needed_in_atom(&self, name: &str, atom: &Atom) -> bool {
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

    fn known_cps_lambda_value_needed_in_arm(&self, name: &str, arm: &MArm) -> bool {
        arm.guard
            .as_ref()
            .is_some_and(|guard| self.known_cps_lambda_value_needed_in_expr(name, guard))
            || (!pat_binds_name(&arm.pattern, name)
                && self.known_cps_lambda_value_needed_in_expr(name, &arm.body))
    }

    fn known_cps_lambda_value_needed_in_handler(&self, name: &str, handler: &MHandler) -> bool {
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

    fn known_cps_lambda_value_needed_in_handler_arm(&self, name: &str, arm: &MHandlerArm) -> bool {
        let params_bind_name = arm.params.iter().any(|param| pat_binds_name(param, name));
        (!params_bind_name && self.known_cps_lambda_value_needed_in_expr(name, &arm.body))
            || arm
                .finally_block
                .as_ref()
                .is_some_and(|block| self.known_cps_lambda_value_needed_in_expr(name, block))
    }

    fn lower_known_local_cps_lambda_call(
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

        self.push_scope();
        for (name, _) in &dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        for pat in &params {
            self.bind_pat_locals(pat);
        }
        let lowered_body = self.lower_cps_expr(&body, evidence, return_k);
        let lowered_body = self.wrap_param_match(&params, &arg_names, lowered_body);
        self.pop_scope();

        let lowered_body = arg_names
            .into_iter()
            .zip(lowered_args)
            .rev()
            .fold(lowered_body, |body, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(body))
            });
        Some(
            dict_bindings
                .into_iter()
                .rev()
                .fold(lowered_body, |body, (name, value)| {
                    CExpr::Let(core_var(&name), Box::new(value), Box::new(body))
                }),
        )
    }

    fn lower_known_cps_lambda_value(&mut self, known_lambda: &KnownCpsLambda) -> CExpr {
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
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
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

    fn lower_known_cps_lambda_dict_bindings(
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

    fn known_dict_aliases_for_bindings(
        &self,
        dict_bindings: &[(String, Atom)],
    ) -> Vec<(String, KnownDictValue)> {
        dict_bindings
            .iter()
            .filter_map(|(binding_name, value)| {
                let Atom::Var { name, .. } = value else {
                    return None;
                };
                self.known_dict_value(&name.name)
                    .map(|dict| (binding_name.clone(), dict))
            })
            .collect()
    }

    fn known_dict_aliases_for_params(
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
                self.known_dict_value(&arg_name.name)
                    .map(|dict| (param_name.clone(), dict))
            })
            .collect()
    }

    fn lower_normal_cps_call(
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

    fn lower_static_handler_specialized_local_cps_call(
        &mut self,
        function_name: &str,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let fb = self.local_fun_bindings.get(function_name)?.clone();
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        let bindings = self.direct_call_param_bindings(&fb.params, args)?;
        let known_dict_aliases = self.known_dict_aliases_for_params(&fb.params, args);

        self.static_handler_inline_stack
            .push(function_name.to_string());
        self.push_scope();
        self.bind_fun_param_locals_with_arg_shapes(&fb, args);
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        let supported = self.expr_is_cps_island_subset(&fb.body);
        let lowered_body = supported.then(|| self.lower_cps_expr(&fb.body, evidence, return_k));
        self.pop_scope();
        self.static_handler_inline_stack.pop();

        lowered_body.map(|body| {
            bindings
                .into_iter()
                .rev()
                .fold(body, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                })
        })
    }

    fn static_handler_specialized_local_cps_call_candidate(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<String> {
        if !self
            .direct_handler_stack
            .iter()
            .any(|frame| matches!(frame, DirectHandlerFrame::Static { .. }))
        {
            return None;
        }

        let local_name = match head {
            Atom::Var { name, .. } => name.name.clone(),
            _ => return None,
        };
        if self.static_handler_inline_stack.contains(&local_name) {
            return None;
        }

        let CallShape::Cps {
            module: None,
            source_arity,
            adapter_arity,
            effects,
            ..
        } = self.call_shape(head)?
        else {
            return None;
        };
        if effects.is_empty()
            || source_arity != args.len()
            || adapter_arity != args.len() + 2
            || !self.active_static_handlers_cover_effects(&effects)
            || !args.iter().all(|arg| self.atom_is_direct_subset(arg))
        {
            return None;
        }

        let fb = self.local_fun_bindings.get(&local_name)?;
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        Some(local_name)
    }

    fn lower_static_handler_specialized_imported_cps_call(
        &mut self,
        candidate: ImportedStaticHandlerCall,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let ImportedStaticHandlerCall {
            source_module_name,
            erlang_module,
            function_name,
            program,
        } = candidate;
        let key = format!("{erlang_module}:{function_name}");
        if self.static_handler_inline_stack.contains(&key) {
            return None;
        }

        let fb = program.iter().find_map(|decl| match decl {
            MDecl::FunBinding(fb) if fb.name == function_name => Some(fb.clone()),
            _ => None,
        })?;
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        let bindings = self.direct_call_param_bindings(&fb.params, args)?;

        let compiled = self.module_ctx.modules.get(&source_module_name)?;
        let mut imported = DirectLowerer::new(
            &compiled.resolution,
            self.ctors,
            self.module_ctx,
            self.handler_info,
            self.effect_info,
            self.handler_value_map,
            self.options,
        );
        imported.current_module = source_module_name;
        imported.classify_program(&program);
        imported.apply_codegen_info_function_shapes(&compiled.codegen_info);
        imported.compute_function_lowering_plans(&program);
        imported.compute_local_function_entries(&program);
        imported.locals = self.locals.clone();
        imported.local_shapes = self.local_shapes.clone();
        imported.direct_handler_stack = self.direct_handler_stack.clone();
        imported.result_delimiter_stack = self.result_delimiter_stack.clone();
        imported.static_handler_inline_stack = self.static_handler_inline_stack.clone();
        imported.static_handler_inline_stack.push(key);
        imported.cps_temp_counter = self.cps_temp_counter;

        imported.push_scope();
        imported.bind_fun_param_locals(&fb);
        let lowered_body = imported
            .expr_is_cps_island_subset(&fb.body)
            .then(|| imported.lower_cps_expr(&fb.body, evidence, return_k));
        imported.pop_scope();

        self.cps_temp_counter = imported.cps_temp_counter;
        lowered_body.map(|body| {
            bindings
                .into_iter()
                .rev()
                .fold(body, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                })
        })
    }

    fn imported_static_handler_call_candidate(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<ImportedStaticHandlerCall> {
        if !self
            .direct_handler_stack
            .iter()
            .any(|frame| matches!(frame, DirectHandlerFrame::Static { .. }))
        {
            return None;
        }
        let CallShape::Cps {
            module: Some(erlang_module),
            name,
            source_arity,
            adapter_arity,
            effects,
        } = self.call_shape(head)?
        else {
            return None;
        };
        if effects.is_empty()
            || source_arity != args.len()
            || adapter_arity != args.len() + 2
            || !self.active_static_handlers_cover_effects(&effects)
            || !args.iter().all(|arg| self.atom_is_direct_subset(arg))
        {
            return None;
        }

        let (source_module_name, compiled) =
            self.compiled_module_for_erlang_module(&erlang_module)?;
        let program = self.monadic_program_for_compiled_module(compiled);
        if !program
            .iter()
            .any(|decl| matches!(decl, MDecl::FunBinding(fb) if fb.name == name))
        {
            return None;
        }
        Some(ImportedStaticHandlerCall {
            source_module_name,
            erlang_module,
            function_name: name,
            program,
        })
    }

    fn compiled_module_for_erlang_module(
        &self,
        erlang_module: &str,
    ) -> Option<(String, &crate::codegen::CompiledModule)> {
        self.module_ctx
            .modules
            .iter()
            .find_map(|(module_name, compiled)| {
                (erlang_module_name(module_name) == erlang_module)
                    .then(|| (module_name.clone(), compiled))
            })
    }

    fn monadic_program_for_compiled_module(
        &self,
        compiled: &crate::codegen::CompiledModule,
    ) -> MProgram {
        let anf_imported =
            crate::codegen::anf::normalize(compiled.elaborated.clone(), Some(&compiled.resolution));
        let imported_handler_decls = HashMap::new();
        let (program, _) = crate::codegen::monadic::translate::translate_with_imports(
            &anf_imported,
            &compiled.resolution,
            self.effect_info,
            &imported_handler_decls,
        );
        program
    }

    fn active_static_handlers_cover_effects(&self, effects: &[String]) -> bool {
        effects
            .iter()
            .all(|effect| self.active_static_handler_handles_effect(effect))
    }

    fn active_static_handler_handles_effect(&self, effect: &str) -> bool {
        self.direct_handler_stack.iter().rev().any(|frame| {
            let DirectHandlerFrame::Static { arms } = frame else {
                return false;
            };
            arms.iter()
                .any(|arm| Self::effect_names_match(&arm.op.effect, effect))
        })
    }

    pub(super) fn hof_direct_specialization_for_cps_call(
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

    pub(super) fn lower_hof_direct_specialized_call(
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

    fn result_delimiter_arms(
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

    fn build_result_delimiter_k(
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

    fn wrap_with_result_delimiter_to_k(
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

    fn wrap_with_result_delimiter_raw(&mut self, body: CExpr, abort_marker: &str) -> CExpr {
        let with_result = self.fresh_cps_temp("_WithResult");
        let arms =
            self.result_delimiter_arms(abort_marker, |value| value, |value| value, |value| value);
        CExpr::Let(
            with_result.clone(),
            Box::new(body),
            Box::new(CExpr::Case(Box::new(CExpr::Var(with_result)), arms)),
        )
    }

    fn wrap_aborting_handler_arm_result(&mut self, body: CExpr, abort_marker: &str) -> CExpr {
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

    fn resume_direct_handler_arm_result(&mut self, body: CExpr, arm_k: CExpr) -> CExpr {
        let result = self.fresh_cps_temp("_TailResumeValue");
        CExpr::Let(
            result.clone(),
            Box::new(body),
            Box::new(CExpr::Apply(Box::new(arm_k), vec![CExpr::Var(result)])),
        )
    }

    fn lower_cps_with_dynamic(
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

    fn lower_cps_with_elided_static_handler(
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

    fn can_elide_static_handler_install(
        &mut self,
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
        body: &MExpr,
    ) -> bool {
        let _ = (arms, return_clause, body);
        false
    }

    #[allow(dead_code)]
    fn can_elide_static_handler_install_when_specialized(
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
    fn static_handler_arm_can_direct_call(&mut self, arm: &MHandlerArm) -> bool {
        arm.finally_block.is_none()
            && self.handler_info.resumption.get(&arm.id) == Some(&ResumptionKind::TailResumptive)
            && !self.expr_contains_yield(&arm.body)
            && self.direct_call_params_supported(&arm.params)
            && self.handler_arm_expr_is_cps_island_subset(&arm.body)
    }

    #[allow(dead_code)]
    fn static_handler_effects(&self, arms: &[MHandlerArm]) -> Vec<String> {
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
    fn expr_can_run_with_elided_static_handler(
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
                    self.current_known_cps_lambda_scope_mut()
                        .insert(var.name.clone(), lambda);
                }
                if let Some(dict) = known_dict {
                    self.current_known_dict_value_scope_mut()
                        .insert(var.name.clone(), dict);
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
                    false
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
    fn cps_app_is_supported_without_elided_effects(&mut self, head: &Atom, args: &[Atom]) -> bool {
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
    fn cps_call_effects_intersect_elided_static_handler(
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
    fn effect_is_handled_by_elided_static_handler(
        &self,
        effect: &str,
        handled_effects: &[String],
    ) -> bool {
        handled_effects
            .iter()
            .any(|handled| Self::effect_names_match(handled, effect))
    }

    #[allow(dead_code)]
    fn can_static_handler_specialize_local_cps_call_without_evidence(
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

        self.static_handler_inline_stack.push(local_name);
        self.push_scope();
        self.bind_fun_param_locals_with_arg_shapes(&fb, args);
        for (name, dict) in known_dict_aliases {
            self.current_known_dict_value_scope_mut().insert(name, dict);
        }
        let supported = self.expr_can_run_with_elided_static_handler(&fb.body, handled_effects);
        self.pop_scope();
        self.static_handler_inline_stack.pop();
        supported
    }

    #[allow(dead_code)]
    fn can_static_handler_specialize_imported_cps_call_without_evidence(
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
            self.options,
        );
        imported.current_module = source_module_name;
        imported.classify_program(&program);
        imported.apply_codegen_info_function_shapes(&compiled.codegen_info);
        imported.compute_function_lowering_plans(&program);
        imported.compute_local_function_entries(&program);
        imported.locals = self.locals.clone();
        imported.local_shapes = self.local_shapes.clone();
        imported.direct_handler_stack = self.direct_handler_stack.clone();
        imported.result_delimiter_stack = self.result_delimiter_stack.clone();
        imported.static_handler_inline_stack = self.static_handler_inline_stack.clone();
        imported.static_handler_inline_stack.push(key);

        imported.push_scope();
        imported.bind_fun_param_locals(&fb);
        let supported = imported.expr_can_run_with_elided_static_handler(&fb.body, handled_effects);
        imported.pop_scope();
        supported
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

    fn lower_cps_handler_value(
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

    fn lower_cps_handler_value_expr(&mut self, expr: &MExpr, outer_evidence: CExpr) -> CExpr {
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

    fn lower_cps_handler_value_ops_by_effect(
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

    fn lower_cps_handler_value_return_lambda(&mut self, arm: &MHandlerArm) -> CExpr {
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

    fn lower_cps_static_handler_arm_group(
        &mut self,
        arms: &[&MHandlerArm],
        outer_evidence: CExpr,
        abort_marker: Option<&str>,
    ) -> CExpr {
        match arms {
            [] => self.unsupported("static handler operation group has no arms"),
            [arm] => self.lower_cps_static_handler_arm(arm, outer_evidence, abort_marker),
            [first, rest @ ..] => {
                let source_params = lower_param_names(&first.params);
                let perform_evidence = self.fresh_cps_temp("_ArmEvidence");
                let arm_k = self.fresh_cps_temp("_ArmK");
                let mut params = source_params.clone();
                params.push(perform_evidence);
                params.push(arm_k.clone());

                for arm in rest {
                    if arm.params.len() != first.params.len() {
                        self.unsupported(
                            "static handler operation arms have inconsistent parameter counts",
                        );
                    }
                }

                let scrutinee = CExpr::Tuple(
                    source_params
                        .iter()
                        .map(|param| CExpr::Var(param.clone()))
                        .collect(),
                );
                let case_arms = arms
                    .iter()
                    .map(|arm| {
                        self.push_scope();
                        self.bind_cps_handler_arm_param_locals(arm);
                        let body = self.lower_cps_handler_arm_expr(
                            &arm.body,
                            outer_evidence.clone(),
                            CExpr::Var(arm_k.clone()),
                            arm.finally_block.as_deref(),
                        );
                        let body = if self.handler_arm_is_optimized_tail_resume(arm) {
                            self.resume_direct_handler_arm_result(body, CExpr::Var(arm_k.clone()))
                        } else {
                            body
                        };
                        let body = if let Some(marker) = abort_marker
                            && self.handler_arm_semantically_aborts(arm)
                        {
                            self.wrap_aborting_handler_arm_result(body, marker)
                        } else {
                            body
                        };
                        let pat =
                            CPat::Tuple(arm.params.iter().map(|pat| self.lower_pat(pat)).collect());
                        self.pop_scope();
                        CArm {
                            pat,
                            guard: None,
                            body,
                        }
                    })
                    .collect();

                CExpr::Fun(
                    params,
                    Box::new(CExpr::Case(Box::new(scrutinee), case_arms)),
                )
            }
        }
    }

    fn lower_cps_static_handler_arm(
        &mut self,
        arm: &MHandlerArm,
        outer_evidence: CExpr,
        abort_marker: Option<&str>,
    ) -> CExpr {
        let source_params = lower_param_names(&arm.params);
        let perform_evidence = self.fresh_cps_temp("_ArmEvidence");
        let arm_k = self.fresh_cps_temp("_ArmK");
        let mut params = source_params.clone();
        params.push(perform_evidence);
        params.push(arm_k.clone());

        self.push_scope();
        self.bind_cps_handler_arm_param_locals(arm);
        let body = self.lower_cps_handler_arm_expr(
            &arm.body,
            outer_evidence,
            CExpr::Var(arm_k.clone()),
            arm.finally_block.as_deref(),
        );
        let body = if self.handler_arm_is_optimized_tail_resume(arm) {
            self.resume_direct_handler_arm_result(body, CExpr::Var(arm_k.clone()))
        } else {
            body
        };
        let body = if let Some(marker) = abort_marker
            && self.handler_arm_semantically_aborts(arm)
        {
            self.wrap_aborting_handler_arm_result(body, marker)
        } else {
            body
        };
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
        if let MExpr::Pure(atom) = expr
            && self.handler_arm_atom_is_cps_island_subset(atom)
        {
            if let Some(cleanup) = finally_block
                && !self.atom_contains_resume(atom)
            {
                return self.lower_direct_handler_result_with_finally(
                    expr,
                    cleanup,
                    outer_evidence,
                );
            }
            return self.lower_cps_handler_arm_atom(atom, outer_evidence, arm_k, finally_block);
        }
        if self.expr_is_direct_subset(expr) {
            return match finally_block {
                Some(cleanup) => {
                    self.lower_direct_handler_result_with_finally(expr, cleanup, outer_evidence)
                }
                None => self.lower_expr(expr),
            };
        }
        match expr {
            MExpr::Yield { op, args, .. } => {
                if finally_block.is_some() {
                    self.unsupported_expr(expr);
                }
                self.lower_cps_yield(op, args, outer_evidence, arm_k)
            }
            MExpr::Resume { value, .. } => {
                self.lower_resume_with_finally(value, arm_k, finally_block, outer_evidence)
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if matches!(&**value, MExpr::Resume { .. }) =>
            {
                let MExpr::Resume {
                    value: resume_value,
                    ..
                } = &**value
                else {
                    unreachable!();
                };
                let local_shape = self
                    .direct_local_shape_for_expr(value)
                    .or_else(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body));
                let lowered_value = self.lower_resume_with_finally(
                    resume_value,
                    arm_k.clone(),
                    finally_block,
                    outer_evidence.clone(),
                );
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
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if self.handler_arm_expr_is_cps_callback_call_subset(value) =>
            {
                let MExpr::App { head, args, .. } = &**value else {
                    unreachable!();
                };
                let local_shape = self.direct_local_shape_for_expr(value);
                let lowered_value =
                    self.lower_cps_callback_call_result_value(head, args, outer_evidence.clone());
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
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if self.handler_arm_expr_is_cps_island_subset(value) =>
            {
                let local_shape = self.direct_local_shape_for_expr(value);
                let lowered_value = self.lower_cps_handler_arm_expr(
                    value,
                    outer_evidence.clone(),
                    arm_k.clone(),
                    None,
                );
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
            MExpr::App { head, args, .. }
                if self.handler_arm_expr_is_cps_callback_call_subset(expr) =>
            {
                self.lower_cps_app(head, args, outer_evidence, arm_k)
            }
            MExpr::App { head, args, .. } => self
                .lower_flat_map_identity_resume_handler_arm(
                    head,
                    args,
                    arm_k,
                    finally_block,
                    outer_evidence,
                )
                .unwrap_or_else(|| {
                    self.unsupported_expr(&MExpr::App {
                        head: head.clone(),
                        args: args.clone(),
                        source: NodeId::fresh(),
                    })
                }),
            _ => self.unsupported_expr(expr),
        }
    }

    fn lower_cps_handler_arm_lambda(
        &mut self,
        params: &[Pat],
        body: &MExpr,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        let param_names = lower_param_names(params);
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let lowered_body =
            self.lower_cps_handler_arm_expr(body, outer_evidence, arm_k, finally_block);
        let lowered_body = self.wrap_param_match(params, &param_names, lowered_body);
        self.pop_scope();
        CExpr::Fun(param_names, Box::new(lowered_body))
    }

    fn lower_cps_handler_arm_atom(
        &mut self,
        atom: &Atom,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        match atom {
            Atom::Lambda { params, body, .. }
                if self.handler_arm_lambda_is_cps_island_subset(params, body) =>
            {
                self.lower_cps_handler_arm_lambda(
                    params,
                    body,
                    outer_evidence,
                    arm_k,
                    finally_block,
                )
            }
            Atom::Ctor { name, args, .. } => self.lower_cps_handler_arm_ctor_atom(
                name,
                args,
                outer_evidence,
                arm_k,
                finally_block,
            ),
            Atom::Tuple { elements, .. } => CExpr::Tuple(
                elements
                    .iter()
                    .map(|arg| {
                        self.lower_cps_handler_arm_atom(
                            arg,
                            outer_evidence.clone(),
                            arm_k.clone(),
                            finally_block,
                        )
                    })
                    .collect(),
            ),
            Atom::AnonRecord { fields, .. } => {
                let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&names);
                let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                elems.extend(sorted.into_iter().map(|(_, atom)| {
                    self.lower_cps_handler_arm_atom(
                        atom,
                        outer_evidence.clone(),
                        arm_k.clone(),
                        finally_block,
                    )
                }));
                CExpr::Tuple(elems)
            }
            Atom::Record { name, fields, .. } => {
                let mut elems = vec![CExpr::Lit(CLit::Atom(mangle_ctor_atom(name, self.ctors)))];
                elems.extend(fields.iter().map(|(_, atom)| {
                    self.lower_cps_handler_arm_atom(
                        atom,
                        outer_evidence.clone(),
                        arm_k.clone(),
                        finally_block,
                    )
                }));
                CExpr::Tuple(elems)
            }
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Symbol { symbol, .. } => {
                crate::codegen::lower::util::lower_string_to_binary(symbol)
            }
            Atom::Var { .. } | Atom::QualifiedRef { .. } | Atom::DictRef { .. }
                if self.atom_is_direct_subset(atom) =>
            {
                self.lower_atom(atom)
            }
            Atom::BackendAtom { .. } | Atom::BackendSpawnThunk { .. } | Atom::DictRef { .. } => {
                self.unsupported_atom(atom)
            }
            Atom::Var { .. } | Atom::QualifiedRef { .. } => self.unsupported_atom(atom),
            Atom::Lambda { .. } => self.unsupported_atom(atom),
        }
    }

    fn lower_cps_handler_arm_ctor_atom(
        &mut self,
        name: &str,
        args: &[Atom],
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            return CExpr::Cons(
                Box::new(self.lower_cps_handler_arm_atom(
                    &args[0],
                    outer_evidence.clone(),
                    arm_k.clone(),
                    finally_block,
                )),
                Box::new(self.lower_cps_handler_arm_atom(
                    &args[1],
                    outer_evidence,
                    arm_k,
                    finally_block,
                )),
            );
        }
        let mut elems = vec![CExpr::Lit(CLit::Atom(mangle_ctor_atom(name, self.ctors)))];
        elems.extend(args.iter().map(|arg| {
            self.lower_cps_handler_arm_atom(
                arg,
                outer_evidence.clone(),
                arm_k.clone(),
                finally_block,
            )
        }));
        CExpr::Tuple(elems)
    }

    fn lower_flat_map_identity_resume_handler_arm(
        &mut self,
        head: &Atom,
        args: &[Atom],
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
        outer_evidence: CExpr,
    ) -> Option<CExpr> {
        if !self.is_flat_map_identity_resume_app(head, args) {
            return None;
        }
        let CallShape::Direct(callable) = self.call_shape(head)? else {
            return None;
        };
        let Atom::Lambda { params, body, .. } = &args[0] else {
            return None;
        };
        let MExpr::Resume { value, .. } = &**body else {
            return None;
        };

        let callback_params = lower_param_names(params);
        self.push_scope();
        for param in params {
            self.bind_pat_locals(param);
        }
        let callback_body =
            self.lower_resume_with_finally(value, arm_k, finally_block, outer_evidence);
        let callback_body = self.wrap_param_match(params, &callback_params, callback_body);
        self.pop_scope();

        let lowered_args = vec![
            CExpr::Fun(callback_params, Box::new(callback_body)),
            self.lower_atom(&args[1]),
        ];
        Some(match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        })
    }

    fn lower_resume_with_finally(
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

    fn lower_direct_handler_result_with_finally(
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

    fn lower_direct_handler_result_case_arm_with_finally(
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

    fn lower_handler_finally_expr(
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

    fn lower_cps_callback_call_result_value(
        &mut self,
        head: &Atom,
        args: &[Atom],
        outer_evidence: CExpr,
    ) -> CExpr {
        let result_var = self.fresh_cps_temp("_CpsCallbackValue");
        let return_k = CExpr::Fun(vec![result_var.clone()], Box::new(CExpr::Var(result_var)));
        self.lower_cps_app(head, args, outer_evidence, return_k)
    }

    fn sequence_direct_finally_then(
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

    fn lower_cps_case_chain(
        &mut self,
        scrutinee: &Atom,
        arms: &[MArm],
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        let scrutinee = self.lower_atom(scrutinee);
        let scrut_var = self.fresh_cps_temp("_CpsCaseScrut");
        let mut rest = self.case_clause_error();

        for arm in arms.iter().rev() {
            let rest_var = self.fresh_cps_temp("_CpsCaseRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_pat_locals(&arm.pattern);
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

    fn lower_cps_receive(
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

    fn lower_cps_receive_arm(&mut self, arm: &MArm, evidence: CExpr, return_k: CExpr) -> CArm {
        self.push_scope();
        self.bind_pat_locals(&arm.pattern);
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

    pub(super) fn lower_receive_pat(&mut self, pat: &Pat) -> (CPat, Option<(String, String)>) {
        match pat {
            Pat::Constructor { name, args, .. } if is_system_msg(name) && args.len() == 2 => {
                let pid_pat = self.lower_pat(&args[0]);
                let (reason_pat, wrapper) = match &args[1] {
                    Pat::Var { name, .. } => {
                        let raw = self.fresh_cps_temp("_RawExitReason");
                        (CPat::Var(raw.clone()), Some((core_var(name), raw)))
                    }
                    other => (self.lower_pat(other), None),
                };
                (system_msg_pattern(name, pid_pat, reason_pat), wrapper)
            }
            _ => (self.lower_pat(pat), None),
        }
    }

    pub(super) fn exit_reason_from_erlang(&mut self, raw_var: &str) -> CExpr {
        let normal = mangle_ctor_atom("Normal", self.ctors);
        let shutdown = mangle_ctor_atom("Shutdown", self.ctors);
        let killed = mangle_ctor_atom("Killed", self.ctors);
        let noproc = mangle_ctor_atom("Noproc", self.ctors);
        let error = mangle_ctor_atom("Error", self.ctors);
        let other = mangle_ctor_atom("Other", self.ctors);

        let error_msg_var = self.fresh_cps_temp("_ErrorMsg");
        let error_msg_var2 = self.fresh_cps_temp("_ErrorMsg");
        let other_var = self.fresh_cps_temp("_OtherReason");
        let fmt_var = self.fresh_cps_temp("_FormattedReason");
        let stringify = CExpr::Call(
            "unicode".to_string(),
            "characters_to_binary".to_string(),
            vec![CExpr::Call(
                "io_lib".to_string(),
                "format".to_string(),
                vec![
                    crate::codegen::lower::util::lower_string_to_binary("~p"),
                    CExpr::Cons(
                        Box::new(CExpr::Var(other_var.clone())),
                        Box::new(CExpr::Nil),
                    ),
                ],
            )],
        );

        CExpr::Case(
            Box::new(CExpr::Var(raw_var.to_string())),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("normal".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(normal)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("shutdown".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(shutdown)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("killed".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(killed)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("noproc".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(noproc)),
                },
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Tuple(vec![
                            CPat::Lit(CLit::Atom("saga_error".to_string())),
                            CPat::Wildcard,
                            CPat::Var(error_msg_var.clone()),
                            CPat::Wildcard,
                            CPat::Wildcard,
                            CPat::Wildcard,
                            CPat::Wildcard,
                        ]),
                        CPat::Wildcard,
                    ]),
                    guard: None,
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom(error.clone())),
                        CExpr::Var(error_msg_var),
                    ]),
                },
                CArm {
                    pat: CPat::Tuple(vec![CPat::Var(error_msg_var2.clone()), CPat::Wildcard]),
                    guard: Some(CExpr::Call(
                        "erlang".to_string(),
                        "is_binary".to_string(),
                        vec![CExpr::Var(error_msg_var2.clone())],
                    )),
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom(error)),
                        CExpr::Var(error_msg_var2),
                    ]),
                },
                CArm {
                    pat: CPat::Var(other_var.clone()),
                    guard: None,
                    body: CExpr::Let(
                        fmt_var.clone(),
                        Box::new(stringify),
                        Box::new(CExpr::Tuple(vec![
                            CExpr::Lit(CLit::Atom(other)),
                            CExpr::Var(fmt_var),
                        ])),
                    ),
                },
            ],
        )
    }
}

fn is_system_msg(ctor_name: &str) -> bool {
    let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
    matches!(bare, "Down" | "Exit")
}

fn system_msg_pattern(ctor_name: &str, pid_pat: CPat, reason_pat: CPat) -> CPat {
    let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
    match bare {
        "Down" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("DOWN".to_string())),
            CPat::Wildcard,
            CPat::Lit(CLit::Atom("process".to_string())),
            pid_pat,
            reason_pat,
        ]),
        "Exit" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("EXIT".to_string())),
            pid_pat,
            reason_pat,
        ]),
        _ => unreachable!("not a system message: {ctor_name}"),
    }
}
