use crate::ast::{self, BitSegment, Expr, ExprKind, Lit, Pat};
use crate::codegen::cerl::{CArm, CBinSeg, CExpr, CLit, CPat};
use std::collections::{HashMap};
use crate::codegen::lower::util::*;
use crate::codegen::lower::pats::*;
use crate::codegen::lower::*;

impl<'a> Lowerer<'a> {
    /// Lower a `<<seg1, seg2, ...>>` bitstring expression to `CExpr::Binary`.
    pub(crate) fn lower_bitstring_expr(&mut self, segments: &[BitSegment<Expr>]) -> CExpr {
        use crate::codegen::lower::util::{
            resolve_bit_segment_flags, resolve_bit_segment_meta, resolve_bit_segment_size,
        };

        let mut segs = Vec::new();
        for seg in segments {
            // String literal sugar: expand to byte segments
            if let ExprKind::Lit {
                value: Lit::String(s, kind),
                ..
            } = &seg.value.kind
            {
                let resolved = if kind.is_multiline() {
                    crate::codegen::lower::util::process_string_escapes(s)
                } else {
                    s.clone()
                };
                for b in resolved.as_bytes() {
                    segs.push(CBinSeg::Byte(*b));
                }
                continue;
            }

            let is_binary = seg.specs.contains(&ast::BitSegSpec::Binary);
            let value = self.lower_expr_value(&seg.value);

            if is_binary && seg.size.is_none() {
                segs.push(CBinSeg::BinaryAll(value));
                continue;
            }

            let (type_name, default_size, unit) = resolve_bit_segment_meta(&seg.specs);
            let flags = resolve_bit_segment_flags(&seg.specs);
            let size = seg.size.as_ref().map(|s| self.lower_expr_value(s));
            let size_expr = resolve_bit_segment_size(size, &type_name, default_size);

            segs.push(CBinSeg::Segment {
                value,
                size: size_expr,
                unit,
                type_name,
                flags,
            });
        }
        CExpr::Binary(segs)
    }

    pub(crate) fn lower_expr(&mut self, expr: &Expr) -> CExpr {
        match &expr.kind {
            ExprKind::Lit { value, .. } => match value {
                Lit::String(s, kind) => {
                    let resolved = if kind.is_multiline() {
                        process_string_escapes(s)
                    } else {
                        s.clone()
                    };
                    lower_string_to_binary(&resolved)
                }
                _ => CExpr::Lit(lower_lit(value)),
            },

            ExprKind::Var { name, .. } => {
                match self.resolved.get(&expr.id).cloned() {
                    Some(resolved) => self.lower_resolved_value_ref(expr.id, resolved),
                    _ => {
                        // Not in resolution map: this is a local variable
                        // (function param, let binding, lambda param, case binding, etc.).
                        // The resolver is authoritative — if it didn't resolve the name,
                        // it's not a module-level or imported function.
                        if let Some(tuple) = self.lower_handler_def_to_tuple(name) {
                            // Handler used as a value (e.g. returned from a function,
                            // passed as argument): convert to tuple-of-lambdas.
                            tuple
                        } else {
                            CExpr::Var(core_var(name))
                        }
                    }
                }
            }

            ExprKind::App { .. } => self.lower_app_expr(expr),

            ExprKind::Constructor { name, .. } => {
                let origin = self
                    .constructor_origin_module_for(expr.id, name)
                    .map(str::to_string);
                self.lower_ctor_with_origin(name, vec![], origin.as_deref())
            }

            ExprKind::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right, Some(&expr.span)),

            ExprKind::UnaryMinus { expr, .. } => {
                let v = self.fresh();
                let ce = self.lower_expr_value(expr);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(cerl_call(
                        "erlang",
                        "-",
                        vec![CExpr::Lit(CLit::Int(0)), CExpr::Var(v)],
                    )),
                )
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_var = self.fresh();
                let cond_ce = self.lower_expr_value(cond);
                let then_ce = self.lower_expr(then_branch);
                let else_ce = self.lower_expr(else_branch);
                CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: then_ce,
                            },
                            CArm {
                                pat: CPat::Lit(CLit::Atom("false".to_string())),
                                guard: None,
                                body: else_ce,
                            },
                        ],
                    )),
                )
            }

            ExprKind::Block { stmts, .. } => {
                let stmts: Vec<_> = stmts.iter().map(|a| a.node.clone()).collect();
                self.lower_block_with_return_k(&stmts, None)
            }

            ExprKind::Lambda { params, body, .. } => {
                let all_simple = params.iter().all(|p| {
                    matches!(
                        p,
                        Pat::Var { .. }
                            | Pat::Wildcard { .. }
                            | Pat::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                    )
                });
                let mut param_vars = lower_params(params);
                let mut is_effectful_lambda = false;
                let shape = self.lambda_effect_context.take();
                let saved_evidence = self.current_evidence.clone();
                if let Some(shape) = shape {
                    // Effectful lambdas take `_Evidence` and `_ReturnK`; the
                    // body reads per-op handlers out of the evidence vector.
                    param_vars.push("_Evidence".to_string());
                    param_vars.push("_ReturnK".to_string());
                    self.current_evidence = Some(EvidenceCtx {
                        var: "_Evidence".to_string(),
                        layout: evidence::EvidenceLayout::new(shape.static_effects.iter().cloned()),
                        is_open: shape.is_open_row,
                    });
                    is_effectful_lambda = true;
                }
                let effect_return_k =
                    is_effectful_lambda.then(|| CExpr::Var("_ReturnK".to_string()));
                let body_ce = if is_effectful_lambda && !matches!(body.kind, ExprKind::Block { .. })
                {
                    self.lower_terminal_effectful_expr_with_return_k(body, effect_return_k.clone())
                } else {
                    self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                };
                self.current_evidence = saved_evidence;
                // If lambda has complex params (tuples, constructors), wrap
                // the body in a case expression for destructuring. The
                // scrutinee covers user params only — `_Evidence`/`_ReturnK`
                // (when present for effectful lambdas) stay outside the
                // destructure pattern.
                let body_ce = if !all_simple {
                    let user_param_vars: &[String] = &param_vars[..params.len()];
                    let scrutinee = if user_param_vars.len() == 1 {
                        CExpr::Var(user_param_vars[0].clone())
                    } else {
                        CExpr::Tuple(
                            user_param_vars
                                .iter()
                                .map(|v| CExpr::Var(v.clone()))
                                .collect(),
                        )
                    };
                    let pat = if params.len() == 1 {
                        self.lower_pat(
                            &params[0],
                            &self.constructor_atoms,
                            self.handler_origin_module(),
                        )
                    } else {
                        CPat::Tuple(
                            params
                                .iter()
                                .map(|p| {
                                    self.lower_pat(
                                        p,
                                        &self.constructor_atoms,
                                        self.handler_origin_module(),
                                    )
                                })
                                .collect(),
                        )
                    };
                    CExpr::Case(
                        Box::new(scrutinee),
                        vec![CArm {
                            pat,
                            guard: None,
                            body: body_ce,
                        }],
                    )
                } else {
                    body_ce
                };
                CExpr::Fun(param_vars, Box::new(body_ce))
            }

            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_var = self.fresh();
                let scrut_ce = self.lower_expr_value(scrutinee);
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                CExpr::Let(
                    scrut_var.clone(),
                    Box::new(scrut_ce),
                    Box::new(self.lower_case_expr(&scrut_var, &arms)),
                )
            }

            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                // Lower arms: same pattern/guard/body as case, but for receive
                // there is no scrutinee variable to fall through to.
                let lowered_arms: Vec<CArm> = arms
                    .iter()
                    .map(|annotated| {
                        let arm = &annotated.node;
                        // System message patterns (Down/Exit): match raw Erlang
                        // tuple shapes and convert the reason field.
                        let (pat, reason_wrapper) = if let Pat::Constructor { name, args, .. } =
                            &arm.pattern
                        {
                            if beam_interop::is_system_msg(name) && args.len() == 2 {
                                let (reason_pat, wrapper) =
                                    if let Pat::Var { name: var_name, .. } = &args[1] {
                                        let raw = self.fresh();
                                        (CPat::Var(raw.clone()), Some((core_var(var_name), raw)))
                                    } else {
                                        (
                                            self.lower_pat(
                                                &args[1],
                                                &self.constructor_atoms,
                                                self.handler_origin_module(),
                                            ),
                                            None,
                                        )
                                    };
                                let pid_pat = self.lower_pat(
                                    &args[0],
                                    &self.constructor_atoms,
                                    self.handler_origin_module(),
                                );
                                let tuple_pat = beam_interop::build_system_msg_pattern(
                                    name, pid_pat, reason_pat,
                                );
                                (tuple_pat, wrapper)
                            } else {
                                (
                                    self.lower_pat(
                                        &arm.pattern,
                                        &self.constructor_atoms,
                                        self.handler_origin_module(),
                                    ),
                                    None,
                                )
                            }
                        } else {
                            (
                                self.lower_pat(
                                    &arm.pattern,
                                    &self.constructor_atoms,
                                    self.handler_origin_module(),
                                ),
                                None,
                            )
                        };

                        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
                        let raw_body = self.lower_expr(&arm.body);
                        let body = if let Some((user_var, raw_var)) = reason_wrapper {
                            let ctor_atoms = self.constructor_atoms.clone();
                            let conversion = beam_interop::build_exit_reason_from_erlang(
                                &raw_var,
                                &ctor_atoms,
                                &mut || self.fresh(),
                            );
                            CExpr::Let(user_var, Box::new(conversion), Box::new(raw_body))
                        } else {
                            raw_body
                        };
                        CArm { pat, guard, body }
                    })
                    .collect();

                let (timeout, timeout_body) = if let Some((t, b)) = after_clause {
                    (self.lower_expr_value(t), self.lower_expr(b))
                } else {
                    (
                        CExpr::Lit(CLit::Atom("infinity".into())),
                        CExpr::Lit(CLit::Atom("true".into())),
                    )
                };

                CExpr::Receive(lowered_arms, Box::new(timeout), Box::new(timeout_body))
            }

            ExprKind::Tuple { elements, .. } => self.lower_tuple_elems(elements),

            ExprKind::QualifiedName { module, name, .. } => {
                // Check if this is a qualified constructor with no args (e.g. M.Nothing)
                let qualified = format!("{}.{}", module, name);
                if self.is_known_constructor(&qualified) || self.is_known_constructor(name) {
                    let origin = self
                        .constructor_origin_module_for(expr.id, name)
                        .map(str::to_string);
                    return self.lower_ctor_with_origin(name, vec![], origin.as_deref());
                }
                if let Some(resolved) = self.resolved.get(&expr.id).cloned() {
                    self.lower_resolved_value_ref(expr.id, resolved)
                } else {
                    CExpr::Var(core_var(name))
                }
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                let order = self
                    .resolved_record_fields(expr.id, name)
                    .cloned()
                    .unwrap_or_default();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &order {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in RecordCreate");
                    let ce = self.lower_expr_value(e);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                let atom = util::mangle_ctor_atom(
                    name,
                    &self.constructor_atoms,
                    self.handler_origin_module(),
                );
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::AnonRecordCreate { fields, .. } => {
                let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&names);
                let mut sorted_names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                sorted_names.sort();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &sorted_names {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in AnonRecordCreate");
                    let ce = self.lower_expr_value(e);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::FieldAccess {
                expr,
                field,
                record_name: resolved_name,
            } => {
                let idx = resolved_name
                    .as_deref()
                    .and_then(|rname| self.record_fields.get(rname))
                    .and_then(|fields| fields.iter().position(|f| f == field))
                    .map(|pos| pos + 2) // +1 for tag, +1 for 1-based
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for field access '.{}' at node {:?} (record_name={:?})",
                            field, expr.id, resolved_name
                        )
                    }) as i64;
                let v = self.fresh();
                let ce = self.lower_expr_value(expr);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(cerl_call(
                        "erlang",
                        "element",
                        vec![CExpr::Lit(CLit::Int(idx)), CExpr::Var(v)],
                    )),
                )
            }

            ExprKind::RecordUpdate {
                record,
                fields,
                record_name: resolved_name,
            } => {
                let rec_var = self.fresh();
                let rec_ce = self.lower_expr_value(record);
                let order = resolved_name
                    .as_deref()
                    .and_then(|rname| self.record_fields.get(rname))
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for record update at node {:?} (record_name={:?})",
                            expr.id, resolved_name
                        )
                    });
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();

                // Destructure the base record with a single tuple pattern so
                // untouched fields read via `get_tuple_element` (arity proven
                // locally) rather than the guarded `erlang:element/2` BIF. See
                // `record_destructure_case` for why this matters across module
                // boundaries.
                let tag_var = self.fresh();
                let mut pat_vars: Vec<Option<String>> = Vec::with_capacity(order.len());
                let mut vars: Vec<String> = Vec::with_capacity(order.len());
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in order.iter() {
                    let v = self.fresh();
                    if let Some(new_expr) = field_map.get(field_name.as_str()) {
                        pat_vars.push(None);
                        let ce = self.lower_expr_value(new_expr);
                        bindings.push((v.clone(), ce));
                    } else {
                        // Untouched field: bound directly by the destructure.
                        pat_vars.push(Some(v.clone()));
                    }
                    vars.push(v);
                }
                let mut elems = vec![CExpr::Var(tag_var.clone())];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                let inner = bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                });
                let destructured =
                    Self::record_destructure_case(&rec_var, &tag_var, &pat_vars, inner);
                CExpr::Let(rec_var, Box::new(rec_ce), Box::new(destructured))
            }

            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                let else_arms: Vec<_> = else_arms.iter().map(|a| a.node.clone()).collect();
                self.lower_do(bindings, success, &else_arms)
            }

            // --- Elaboration-only constructs ---
            ExprKind::DictMethodAccess {
                dict,
                method_index,
                trait_name,
            } => {
                // Lower to: let D = <dict> in element(idx+1, D)
                let dict_var = self.fresh();
                let dict_ce = self.lower_expr_value(dict);
                let tuple_index = self.trait_method_tuple_index(trait_name, *method_index);
                let extract_method = cerl_call(
                    "erlang",
                    "element",
                    vec![
                        CExpr::Lit(CLit::Int(tuple_index as i64 + 1)),
                        CExpr::Var(dict_var.clone()),
                    ],
                );
                // A nullary trait method (`fun default : a`) is stored in the dict
                // as a zero-arity thunk (`fun () -> 0`) and is never the head of an
                // `App`, so nothing else applies it. Apply it here so the call
                // yields the value, not the closure.
                let body = if self.trait_method_is_nullary(trait_name, *method_index) {
                    CExpr::Apply(Box::new(extract_method), vec![])
                } else {
                    extract_method
                };
                CExpr::Let(dict_var, Box::new(dict_ce), Box::new(body))
            }

            ExprKind::DictSuperAccess {
                dict,
                supertrait_index,
                ..
            } => {
                let dict_var = self.fresh();
                let dict_ce = self.lower_expr_value(dict);
                let body = cerl_call(
                    "erlang",
                    "element",
                    vec![
                        CExpr::Lit(CLit::Int(*supertrait_index as i64 + 1)),
                        CExpr::Var(dict_var.clone()),
                    ],
                );
                CExpr::Let(dict_var, Box::new(dict_ce), Box::new(body))
            }

            ExprKind::ForeignCall {
                module, func, args, ..
            } => {
                let mut vars = Vec::new();
                let mut bindings = Vec::new();
                for arg in args {
                    let v = self.fresh();
                    let ce = self.lower_expr_value(arg);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                // erlang:monitor/1 -> erlang:monitor/2 with 'process' atom
                let call = if module == "erlang" && func == "monitor" && vars.len() == 1 {
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vec![
                            CExpr::Lit(CLit::Atom("process".into())),
                            CExpr::Var(vars[0].clone()),
                        ],
                    )
                // float_to_list/1 -> float_to_list/2 with [short] option
                } else if module == "erlang" && func == "float_to_list" && vars.len() == 1 {
                    let opts = CExpr::Cons(
                        Box::new(CExpr::Lit(CLit::Atom("short".into()))),
                        Box::new(CExpr::Nil),
                    );
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vec![CExpr::Var(vars[0].clone()), opts],
                    )
                } else {
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                    )
                };
                bindings.into_iter().rev().fold(call, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::DictRef { name, .. } => {
                if let Some(resolved) = self.resolved.get(&expr.id).cloned() {
                    match &resolved.kind {
                        crate::codegen::resolve::ResolvedCodegenKind::BeamFunction { .. }
                        | crate::codegen::resolve::ResolvedCodegenKind::ExternalFunction { .. } => {
                            self.lower_resolved_value_ref(expr.id, resolved)
                        }
                        crate::codegen::resolve::ResolvedCodegenKind::Intrinsic { .. } => {
                            panic!(
                                "dict ref resolved to non-dictionary codegen kind: {}",
                                resolved.canonical_name
                            )
                        }
                    }
                } else if let Some(arity) = self.fun_arity(name) {
                    if arity == 0 {
                        CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), 0)), vec![])
                    } else {
                        CExpr::FunRef(name.clone(), arity)
                    }
                } else {
                    // Dict param variable (passed as function argument)
                    CExpr::Var(core_var(name))
                }
            }

            // --- Effect system (CPS transform) ---

            // `log! "hello"` -- standalone effect call (not in a block).
            // When an effect call appears as a bare expression (not in a block where
            // we can capture the continuation), we call the handler with an identity
            // continuation that just returns the value.
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
                ..
            } => self
                .lower_eta_reduced_effect_op_ref(expr.id, name, qualifier.as_deref())
                .unwrap_or_else(|| {
                    self.lower_effect_call(expr.id, name, qualifier.as_deref(), args, None)
                }),

            // `expr with handler` -- attaches handler(s) to a computation
            ExprKind::With { expr, handler, .. } => self.lower_with(expr, handler),

            // `resume value` -- inside a handler arm, calls the continuation K.
            // When a `finally` block is active, the K call is wrapped in try/catch
            // so cleanup runs after K completes or panics. The cleanup is lowered
            // once into a lambda (at the resume site, where arm body variables are
            // in scope) and called in both the ok and catch branches.
            ExprKind::Resume { value, .. } => {
                let k_name = self
                    .current_handler_k
                    .clone()
                    .expect("resume used outside handler");
                let v = self.fresh();
                let ce = self.lower_expr_value(value);
                let k_call =
                    CExpr::Apply(Box::new(CExpr::Var(k_name)), vec![CExpr::Var(v.clone())]);
                let k_or_wrapped = if let Some(ref finally_expr) =
                    self.current_handler_finally.clone()
                {
                    // let Cleanup = fun() -> finally_body in
                    // try apply K(V)
                    // of OkVar -> let _ = apply Cleanup() in OkVar
                    // catch <C, R, T> -> let _ = apply Cleanup() in raise(C, R, T)
                    let cleanup_var = self.fresh();
                    let cleanup_body = self.lower_expr(finally_expr);
                    let cleanup_lambda = CExpr::Fun(vec![], Box::new(cleanup_body));
                    let cleanup_call_ok =
                        CExpr::Apply(Box::new(CExpr::Var(cleanup_var.clone())), vec![]);
                    let cleanup_call_catch =
                        CExpr::Apply(Box::new(CExpr::Var(cleanup_var.clone())), vec![]);
                    let ok_var = self.fresh();
                    let class_var = self.fresh();
                    let reason_var = self.fresh();
                    let trace_var = self.fresh();
                    CExpr::Let(
                        cleanup_var,
                        Box::new(cleanup_lambda),
                        Box::new(CExpr::Try {
                            expr: Box::new(k_call),
                            ok_var: ok_var.clone(),
                            ok_body: Box::new(CExpr::Let(
                                "_".to_string(),
                                Box::new(cleanup_call_ok),
                                Box::new(CExpr::Var(ok_var)),
                            )),
                            catch_vars: (class_var.clone(), reason_var.clone(), trace_var.clone()),
                            catch_body: Box::new(CExpr::Let(
                                "_".to_string(),
                                Box::new(cleanup_call_catch),
                                Box::new(CExpr::Call(
                                    "erlang".to_string(),
                                    "raise".to_string(),
                                    vec![
                                        CExpr::Var(class_var),
                                        CExpr::Var(reason_var),
                                        CExpr::Var(trace_var),
                                    ],
                                )),
                            )),
                        }),
                    )
                } else {
                    k_call
                };
                CExpr::Let(v, Box::new(ce), Box::new(k_or_wrapped))
            }

            // Handler expression as a value (e.g. returned from a function).
            // Produce a tuple of per-op handler lambdas for runtime use.
            ExprKind::HandlerExpr { body } => self.lower_handler_expr_to_tuple(body),

            ExprKind::BitString { segments } => self.lower_bitstring_expr(segments),

            ExprKind::SymbolIntrinsic { symbol } => lower_string_to_binary(symbol),

            // StringInterpolation should be desugared before reaching the lowerer,
            // but keep a fallback just in case.
            #[allow(unreachable_patterns)]
            other => CExpr::Lit(CLit::Atom(format!(
                "todo_{:?}",
                std::mem::discriminant(other)
            ))),
        }
    }
}
