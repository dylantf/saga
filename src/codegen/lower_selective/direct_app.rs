use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_app(&mut self, head: &Atom, args: &[Atom]) -> CExpr {
        if self.is_panic_or_todo_call(head, args) {
            let Atom::Var { name, .. } = head else {
                unreachable!("is_panic_or_todo_call only matches variable heads");
            };
            return self.lower_panic_or_todo(&name.name, &args[0]);
        }
        if let Some(known_head) = self.known_direct_atom_for_atom(head)
            && matches!(
                known_head,
                Atom::Var { .. } | Atom::QualifiedRef { .. } | Atom::DictRef { .. }
            )
        {
            return self.lower_app(&known_head, args);
        }
        if let Some(lambda) = self.known_direct_lambda_for_atom(head)
            && lambda.params.len() == args.len()
        {
            let method_key = lambda.method_key.clone();
            let inserted = if let Some(key) = method_key.clone() {
                self.active_known_dict_methods.insert(key)
            } else {
                false
            };
            let supported = method_key.is_none() || inserted;
            let supported = supported
                && self.lambda_app_is_direct_subset_with_dict_aliases(
                    &lambda.dict_bindings,
                    lambda.known_dict_aliases.clone(),
                    &lambda.params,
                    &lambda.body,
                    args,
                );
            if supported {
                let mut known_dict_aliases = lambda.known_dict_aliases.clone();
                known_dict_aliases
                    .extend(self.known_dict_aliases_for_bindings(&lambda.dict_bindings));
                let lowered = self.lower_inline_direct_lambda_app_with_dict_bindings(
                    &lambda.dict_bindings,
                    known_dict_aliases,
                    &lambda.params,
                    &lambda.body,
                    args,
                );
                if inserted && let Some(key) = method_key {
                    self.active_known_dict_methods.remove(&key);
                }
                return lowered;
            }
            if inserted && let Some(key) = method_key {
                self.active_known_dict_methods.remove(&key);
            }
        }
        if let Some(lambda) = self.known_direct_lambda_for_atom(head)
            && args.len() < lambda.params.len()
        {
            let method_key = lambda.method_key.clone();
            let inserted = if let Some(key) = method_key.clone() {
                self.active_known_dict_methods.insert(key)
            } else {
                false
            };
            let supported = method_key.is_none() || inserted;
            let supported = supported
                && self.lambda_is_direct_subset_with_dict_aliases(
                    &lambda.dict_bindings,
                    lambda.known_dict_aliases.clone(),
                    &lambda.params,
                    &lambda.body,
                );
            if supported {
                let lowered = self.lower_partial_known_direct_lambda_value(&lambda, args);
                if inserted && let Some(key) = method_key {
                    self.active_known_dict_methods.remove(&key);
                }
                return lowered;
            }
            if inserted && let Some(key) = method_key {
                self.active_known_dict_methods.remove(&key);
            }
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
                    let (lowered_args, bindings) =
                        self.lower_direct_call_args_with_bindings(head, args);
                    let body = CExpr::Apply(Box::new(CExpr::Var(core_var(&name))), lowered_args);
                    self.wrap_core_value_bindings(body, bindings)
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

    pub(super) fn lower_direct_external_app(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<CExpr> {
        if let Some(callable) = self.local_external_callable_by_name(head) {
            if args.len() != callable.arity {
                return None;
            }
            let module = callable.module?;
            let filtered_args: Vec<Atom> = args
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
                .cloned()
                .collect();
            let (call_args, bindings) = self.lower_atoms_as_core_values(&filtered_args);
            return Some(self.wrap_core_value_bindings(
                CExpr::Call(module, callable.name, call_args),
                bindings,
            ));
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
        let filtered_args: Vec<Atom> = args
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
            .cloned()
            .collect();
        let (call_args, bindings) = self.lower_atoms_as_core_values(&filtered_args);
        Some(self.wrap_core_value_bindings(
            CExpr::Call(target_erlang_mod.clone(), target_name.clone(), call_args),
            bindings,
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

    pub(super) fn apply_direct_callable(
        &mut self,
        callable: DirectCallable,
        head: &Atom,
        args: &[Atom],
    ) -> CExpr {
        let (lowered_args, bindings) = self.lower_direct_call_args_with_bindings(head, args);
        let body = match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        };
        self.wrap_core_value_bindings(body, bindings)
    }

    pub(super) fn lower_partial_direct_callable(
        &mut self,
        callable: DirectCallable,
        head: &Atom,
        args: &[Atom],
    ) -> CExpr {
        let missing = callable.arity.saturating_sub(args.len());
        let params: Vec<String> = (0..missing)
            .map(|index| self.fresh_cps_temp(&format!("_PartialArg{index}")))
            .collect();
        let (mut lowered_args, bindings) = self.lower_direct_call_args_with_bindings(head, args);
        lowered_args.extend(params.iter().cloned().map(CExpr::Var));
        let body = match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        };
        CExpr::Fun(
            params,
            Box::new(self.wrap_core_value_bindings(body, bindings)),
        )
    }

    pub(super) fn lower_partial_local_callable(
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
        let (mut lowered_args, bindings) = self.lower_direct_call_args_with_bindings(head, args);
        lowered_args.extend(params.iter().cloned().map(CExpr::Var));
        let body = CExpr::Apply(Box::new(CExpr::Var(core_var(name))), lowered_args);
        CExpr::Fun(
            params,
            Box::new(self.wrap_core_value_bindings(body, bindings)),
        )
    }

    pub(super) fn lower_direct_call_args_with_bindings(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> (Vec<CExpr>, Vec<(String, CExpr)>) {
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        let mut lowered = Vec::with_capacity(args.len());
        let mut bindings = Vec::new();
        for (index, arg) in args.iter().enumerate() {
            let arg = match expected_arg_shapes.get(index).copied().flatten() {
                Some((source_arity, adapter_arity)) if self
                    .expected_cps_arg_needs_runtime_cps_shape(arg) =>
                    self.lower_cps_runtime_value_atom(arg, source_arity, adapter_arity),
                None | Some(_) => {
                    let (arg, binding) = self.lower_atom_as_core_value(arg, "_CallArg");
                    lowered.push(arg);
                    bindings.extend(binding);
                    continue;
                }
            };
            if core_expr_is_simple_value(&arg) {
                lowered.push(arg);
            } else {
                let temp = self.fresh_cps_temp("_CallArg");
                lowered.push(CExpr::Var(temp.clone()));
                bindings.push((temp, arg));
            }
        }
        (lowered, bindings)
    }

    fn expected_cps_arg_needs_runtime_cps_shape(&mut self, arg: &Atom) -> bool {
        if self.cps_lambda_type_arity_for_atom(arg).is_some() {
            return true;
        }
        !matches!(
            arg,
            Atom::Lambda { params, body, .. } if self.lambda_is_direct_subset(params, body)
        )
    }

    pub(super) fn lower_direct_cps_entry_call(
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
        let mut lowered_args = Vec::with_capacity(args.len() + 2);
        let mut bindings = Vec::new();
        for (index, arg) in args.iter().enumerate() {
            let expr = match expected_arg_shapes.get(index).copied().flatten() {
                Some((source_arity, adapter_arity)) => {
                    self.lower_cps_runtime_value_atom(arg, source_arity, adapter_arity)
                }
                None => {
                    let (arg, binding) = self.lower_atom_as_core_value(arg, "_CallArg");
                    lowered_args.push(arg);
                    bindings.extend(binding);
                    continue;
                }
            };
            if core_expr_is_simple_value(&expr) {
                lowered_args.push(expr);
            } else {
                let temp = self.fresh_cps_temp("_CallArg");
                lowered_args.push(CExpr::Var(temp.clone()));
                bindings.push((temp, expr));
            }
        }
        lowered_args.push(CExpr::Tuple(vec![]));
        lowered_args.push(self.identity_cps_continuation());
        let body = match module {
            Some(module) => CExpr::Call(module, name.to_string(), lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(name.to_string(), adapter_arity)),
                lowered_args,
            ),
        };
        self.wrap_core_value_bindings(body, bindings)
    }

    pub(super) fn lower_intrinsic_app(&mut self, intrinsic: IntrinsicId, args: &[Atom]) -> CExpr {
        match intrinsic {
            IntrinsicId::PrintStdout => self.lower_print_intrinsic(args, false),
            IntrinsicId::PrintStderr => self.lower_print_intrinsic(args, true),
            IntrinsicId::Dbg => self.lower_dbg_intrinsic(args),
            IntrinsicId::CatchPanic => self.lower_catch_panic_intrinsic(args),
        }
    }

    pub(super) fn lower_print_intrinsic(&mut self, args: &[Atom], stderr: bool) -> CExpr {
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

    pub(super) fn lower_dbg_intrinsic(&mut self, args: &[Atom]) -> CExpr {
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

    pub(super) fn lower_catch_panic_intrinsic(&mut self, args: &[Atom]) -> CExpr {
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

    pub(super) fn lower_panic_or_todo(&mut self, name: &str, msg_atom: &Atom) -> CExpr {
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
}
