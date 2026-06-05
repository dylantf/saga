use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_yield(
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

    pub(super) fn lower_native_direct_call_yield(
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

    pub(super) fn lower_native_table_direct_call_result(
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

    pub(super) fn lower_native_table_args(
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

    pub(super) fn lower_beam_ref_direct_call_result(
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

    pub(super) fn lower_ets_ref_direct_call_result(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
        evidence: CExpr,
    ) -> Option<CExpr> {
        if op.effect != "Std.Ref.Ref" {
            return None;
        }
        let table = crate::codegen::ets_tables::ets_table_atom_core(
            crate::codegen::ets_tables::ETS_REF_TABLE,
        );
        let result = match op.op.as_str() {
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
        };
        result.map(|body| {
            crate::codegen::ets_tables::wrap_ets_table_init_core(
                body,
                crate::codegen::ets_tables::ETS_REF_TABLE,
                &self.fresh_cps_temp("_EtsRefInit"),
            )
        })
    }

    pub(super) fn lower_ref_modify_direct_call_result(
        &mut self,
        key: CExpr,
        callback: CExpr,
        _evidence: CExpr,
        backend: RefDirectBackend,
    ) -> Option<CExpr> {
        let old = self.fresh_cps_temp("_NativeRefOld");
        let new_value = self.fresh_cps_temp("_NativeRefNew");
        let discard = self.fresh_cps_temp("_NativeRefPut");
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
                            crate::codegen::ets_tables::ets_table_atom_core(
                                crate::codegen::ets_tables::ETS_REF_TABLE,
                            ),
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
                    crate::codegen::ets_tables::ets_table_atom_core(
                        crate::codegen::ets_tables::ETS_REF_TABLE,
                    ),
                    CExpr::Tuple(vec![key, CExpr::Var(new_value.clone())]),
                ],
            ),
        };
        Some(CExpr::Let(
            old.clone(),
            Box::new(get_old),
            Box::new(CExpr::Let(
                new_value.clone(),
                Box::new(CExpr::Apply(Box::new(callback), vec![CExpr::Var(old)])),
                Box::new(CExpr::Let(
                    discard,
                    Box::new(put_new),
                    Box::new(CExpr::Var(new_value)),
                )),
            )),
        ))
    }
}
