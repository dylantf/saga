use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_expr(&mut self, expr: &MExpr) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_atom(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let local_shape = self.direct_local_shape_for_expr(value);
                let value = self.lower_expr(value);
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let body = self.lower_expr(body);
                self.pop_scope();
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
            MExpr::Yield { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => self.unsupported_expr(expr),
        }
    }

    fn lower_case_chain(&mut self, scrutinee: &Atom, arms: &[MArm]) -> CExpr {
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

    pub(super) fn lower_app(&mut self, head: &Atom, args: &[Atom]) -> CExpr {
        if self.is_panic_or_todo_call(head, args) {
            let Atom::Var { name, .. } = head else {
                unreachable!("is_panic_or_todo_call only matches variable heads");
            };
            return self.lower_panic_or_todo(&name.name, &args[0]);
        }
        if let Some(call) = self.lower_direct_external_app(head, args) {
            return call;
        }

        match self.call_shape(head) {
            Some(CallShape::Intrinsic(intrinsic)) => self.lower_intrinsic_app(intrinsic, args),
            Some(CallShape::Direct(callable)) => {
                self.assert_app_arity(&callable.name, args.len(), callable.arity);
                self.apply_direct_callable(callable, args)
            }
            Some(CallShape::LocalCallable { name, arity }) => {
                self.assert_app_arity(&name, args.len(), arity);
                CExpr::Apply(
                    Box::new(CExpr::Var(core_var(&name))),
                    args.iter().map(|arg| self.lower_atom(arg)).collect(),
                )
            }
            Some(CallShape::LocalCpsCallable { name, .. }) => self.unsupported(&format!(
                "CPS callable local '{}' used in direct call position",
                name
            )),
            Some(CallShape::Cps {
                module: _,
                name,
                source_arity,
                adapter_arity,
                effects,
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

    fn apply_direct_callable(&mut self, callable: DirectCallable, args: &[Atom]) -> CExpr {
        let lowered_args = args.iter().map(|arg| self.lower_atom(arg)).collect();
        match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
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
                if self.cps_value_atom_shape(atom).is_some() {
                    return self.lower_cps_value_atom(atom);
                }
                if self.lambda_is_direct_cps_island_subset(params, body) {
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
            Atom::DictRef { .. } | Atom::BackendAtom { .. } | Atom::BackendSpawnThunk { .. } => {
                self.unsupported_atom(atom)
            }
        }
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
            _ => self.unsupported("patterns beyond var/lit/tuple/constructor/record/string-prefix"),
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
