use crate::ast::{Expr, ExprKind, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;
use std::collections::HashMap;

impl<'a> Lowerer<'a> {
    pub(crate) fn lower_block_with_return_k(
        &mut self,
        stmts: &[Stmt],
        return_k: Option<CExpr>,
    ) -> CExpr {
        match stmts {
            [] => self.apply_return_k_with(return_k, CExpr::Tuple(vec![])), // unit
            [Stmt::Expr(e)] => self.lower_block_terminal_expr_with_return_k(e, return_k),
            [Stmt::Let { pattern, value, .. }] => {
                let var = pat_binding_var(pattern).unwrap_or_else(|| self.fresh());
                let val_ce = self.lower_expr_value(value);
                let body = self.apply_return_k_with(return_k, CExpr::Var(var.clone()));
                CExpr::Let(var, Box::new(val_ce), Box::new(body))
            }
            [Stmt::LetFun { .. }, ..] => {
                // Group consecutive LetFun clauses with the same name
                let (fun_name, fun_id) = match &stmts[0] {
                    Stmt::LetFun { id, name, .. } => (name.clone(), *id),
                    _ => unreachable!(),
                };
                let mut clauses: Vec<crate::codegen::lower::Clause> = Vec::new();
                let mut consumed = 0;
                for stmt in stmts {
                    if let Stmt::LetFun {
                        name,
                        params,
                        guard,
                        body,
                        ..
                    } = stmt
                    {
                        if *name != fun_name {
                            break;
                        }
                        clauses.push((params, guard, body));
                        consumed += 1;
                    } else {
                        break;
                    }
                }
                let rest = &stmts[consumed..];

                // Build the function body (same logic as top-level multi-clause funs)
                let source_arity = pats::lower_params(clauses[0].0).len();
                let callable_abi = self
                    .planned_declaration(fun_id)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "internal ABI planning error: missing local declaration ABI for {fun_id:?}"
                        )
                    });
                debug_assert_eq!(callable_abi.user_arity, source_arity);
                let (param_absorbed_effects, param_types) = self
                    .check_result
                    .resolved_type_for_node(fun_id)
                    .map(|ty| {
                        let param_absorbed_effects = param_absorbed_effects_from_type(&ty)
                            .into_iter()
                            .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                            .collect::<HashMap<usize, Vec<String>>>();
                        let param_types = param_types_from_type(&ty);
                        (param_absorbed_effects, param_types)
                    })
                    .unwrap_or_else(|| (HashMap::new(), Vec::new()));
                let arity = callable_abi.expanded_arity();
                let param_names: Vec<String> = (0..arity).map(|i| format!("_LF{}", i)).collect();

                // Register in fun_info BEFORE lowering body so recursive
                // calls are recognized as saturated apply
                let fun_info =
                    FunInfo::from_abi(callable_abi.clone(), param_absorbed_effects, param_types, 0);
                self.fun_info.insert(fun_name.clone(), fun_info);

                let has_effects = callable_abi.evidence.is_some();
                let base_arity = callable_abi.user_arity;
                let effect_return_k = has_effects.then(|| CExpr::Var("_ReturnK".to_string()));

                // Install the evidence context for the body of effectful
                // local functions. Op-call emission inside the body reads
                // handler closures out of `current_evidence`.
                let saved_evidence = self.current_evidence.clone();
                if let Some(evidence_abi) = callable_abi.evidence.clone() {
                    self.current_evidence = Some(EvidenceFrame::new("_Evidence", evidence_abi));
                }

                let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() {
                    // Single clause, no guard
                    let mut params_ce = pats::lower_params(clauses[0].0);
                    if has_effects {
                        params_ce.push("_Evidence".to_string());
                        params_ce.push("_ReturnK".to_string());
                    }
                    let body = clauses[0].2;
                    let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                        self.lower_terminal_effectful_expr_with_return_k(
                            body,
                            effect_return_k.clone(),
                        )
                    } else {
                        self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                    };
                    CExpr::Fun(params_ce, Box::new(body_ce))
                } else {
                    // Multi-clause: build case expression over params
                    let scrutinee = if base_arity == 1 {
                        CExpr::Var(param_names[0].clone())
                    } else if base_arity == 0 {
                        CExpr::Lit(CLit::Atom("unit".to_string()))
                    } else {
                        CExpr::Values(
                            param_names[..base_arity]
                                .iter()
                                .map(|n| CExpr::Var(n.clone()))
                                .collect(),
                        )
                    };
                    let arms: Vec<CArm> = clauses
                        .iter()
                        .map(|(params, guard, body)| {
                            let pat = if base_arity == 1 {
                                self.lower_pat(&params[0], &self.constructor_atoms, None)
                            } else if base_arity == 0 {
                                CPat::Wildcard
                            } else {
                                CPat::Values(
                                    params
                                        .iter()
                                        .map(|p| self.lower_pat(p, &self.constructor_atoms, None))
                                        .collect(),
                                )
                            };
                            let guard_ce = guard.as_ref().map(|g| self.lower_expr(g));
                            let body_ce =
                                if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                                    self.lower_terminal_effectful_expr_with_return_k(
                                        body,
                                        effect_return_k.clone(),
                                    )
                                } else {
                                    self.lower_expr_with_installed_return_k(
                                        body,
                                        effect_return_k.clone(),
                                    )
                                };
                            CArm {
                                pat,
                                guard: guard_ce,
                                body: body_ce,
                            }
                        })
                        .collect();
                    CExpr::Fun(
                        {
                            let mut params = param_names[..base_arity].to_vec();
                            if has_effects {
                                params.push("_Evidence".to_string());
                                params.push("_ReturnK".to_string());
                            }
                            params
                        },
                        Box::new(CExpr::Case(Box::new(scrutinee), arms)),
                    )
                };
                self.current_evidence = saved_evidence;

                let rest_ce = if rest.is_empty() {
                    self.apply_return_k_with(return_k, CExpr::Tuple(vec![]))
                } else {
                    self.lower_block_with_return_k(rest, return_k)
                };

                CExpr::LetRec(vec![(fun_name, arity, fun_body)], Box::new(rest_ce))
            }
            [first, rest @ ..] => {
                // Handle binding: register as a handler alias so `with name`
                // resolves correctly. For static references, this is purely a
                // compile-time alias. For conditionals, we lower the condition
                // and register a synthetic handler that dispatches at runtime.
                // Dynamic handlers lower the RHS and bind it to a variable.
                // Let bindings with handler values: detect and register the
                // handler so `with name` resolves correctly.
                if let Stmt::Let { pattern, value, .. } = first
                    && let Pat::Var {
                        name, id: pat_id, ..
                    } = pattern
                    && self.is_handler_value(value)
                {
                    self.lower_handle_binding(name, Some(*pat_id), value);
                    if let Some((var, _effects, _has_return)) =
                        self.handle_dynamic_vars.get(name.as_str()).cloned()
                    {
                        // Handler factories may themselves be effectful. Their
                        // result must be bound by the call continuation just
                        // like any other CPS let; lowering with an identity K
                        // leaves later first-class uses of the handler outside
                        // the result's scope and loses abort semantics.
                        if self.expr_is_effectful_call(value) {
                            let rest_k = self.lower_rest_block_k_with_return_k(
                                Some(pattern),
                                rest,
                                return_k,
                            );
                            return self.lower_expr_with_call_return_k(value, Some(rest_k));
                        }
                        let rhs_ce = self.lower_expr_value(value);
                        let rest_ce = self.lower_block_with_return_k(rest, return_k);
                        return CExpr::Let(var, Box::new(rhs_ce), Box::new(rest_ce));
                    }
                    return self.lower_block_with_return_k(rest, return_k);
                }

                // Check if the value is a call to an effectful function. If so,
                // capture the rest of the block as _ReturnK so abort-style handlers
                // skip subsequent statements (same CPS treatment as `with`).
                {
                    let value_expr = match first {
                        Stmt::Let { value, .. } => value,
                        Stmt::Expr(e) => e,
                        Stmt::LetFun { .. } => unreachable!(),
                    };
                    if self.expr_is_effectful_call(value_expr) {
                        let (pat_opt, value_expr) = match first {
                            Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                            Stmt::Expr(e) => (None, e),
                            Stmt::LetFun { .. } => unreachable!(),
                        };
                        let rest_k = self.lower_rest_block_k_with_return_k(pat_opt, rest, return_k);
                        return self.lower_expr_with_call_return_k(value_expr, Some(rest_k));
                    }
                }

                // Check if the first statement contains an effect call -- if so, CPS transform:
                // everything in `rest` becomes the continuation closure K.
                // Effect calls may be bare (EffectCall) or wrapped in App nodes
                // (App(EffectCall, arg1), arg2, ...).
                let effect_info = match first {
                    Stmt::Expr(e) => collect_effect_call_expr(e)
                        .map(|(head, name, qual, args)| (None, head.id, name, qual, args)),
                    Stmt::Let { pattern, value, .. } => collect_effect_call_expr(value)
                        .map(|(head, name, qual, args)| (Some(pattern), head.id, name, qual, args)),
                    Stmt::LetFun { .. } => None,
                };

                if let Some((pat, effect_call_id, op_name, qualifier, args)) = effect_info {
                    let k = self.lower_rest_block_k_with_return_k(pat, rest, return_k);
                    // We need to own the args for lower_effect_call
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(effect_call_id, op_name, qualifier, &args_owned, Some(k))
                } else {
                    // Check if value expression has effect calls nested in branches.
                    // If so, build a continuation K from the remaining statements and
                    // thread it through branches so abort-style handlers skip the rest.
                    let value_has_nested = match first {
                        Stmt::Expr(e) => self.has_nested_effectful_expr(e),
                        Stmt::Let { value, .. } => self.has_nested_effectful_expr(value),
                        Stmt::LetFun { .. } => false,
                    };

                    if value_has_nested {
                        let (pat_opt, value_expr) = match first {
                            Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                            Stmt::Expr(e) => (None, e),
                            Stmt::LetFun { .. } => unreachable!(),
                        };
                        let k = self.lower_rest_block_k_with_return_k(pat_opt, rest, return_k);
                        let k_var = self.fresh();
                        let body = self.lower_expr_with_k(value_expr, &k_var);
                        CExpr::Let(k_var, Box::new(k), Box::new(body))
                    } else {
                        // Normal (non-effect) statement
                        let (pat_opt, is_assert, let_span, val_ce) = match first {
                            Stmt::Let {
                                pattern,
                                value,
                                assert,
                                span,
                                ..
                            } => {
                                let val_ce = self.lower_expr_value(value);
                                (Some(pattern), *assert, *span, val_ce)
                            }
                            Stmt::Expr(e) => (None, false, e.span, self.lower_expr_value(e)),
                            Stmt::LetFun { .. } => unreachable!(),
                        };
                        let hof_binding = match first {
                            Stmt::Let {
                                pattern: Pat::Var { name, .. },
                                value,
                                ..
                            } => self
                                .hof_direct_binding_for_value_expr(value)
                                .map(|binding| (name.clone(), binding)),
                            _ => None,
                        };
                        let saved_hof_binding =
                            hof_binding.as_ref().and_then(|(name, specialization)| {
                                self.direct_hof_value_bindings
                                    .insert(name.clone(), specialization.clone())
                            });
                        let saved_handler_vars = pat_opt
                            .map(|pat| self.register_dynamic_handler_pattern_vars(pat))
                            .unwrap_or_default();
                        let rest_ce = self.lower_block_with_return_k(rest, return_k);
                        self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
                        if let Some((name, _)) = hof_binding {
                            if let Some(saved) = saved_hof_binding {
                                self.direct_hof_value_bindings.insert(name, saved);
                            } else {
                                self.direct_hof_value_bindings.remove(&name);
                            }
                        }
                        let (var, rest_ce) = match pat_opt {
                            Some(p) if is_assert => {
                                self.destructure_pat_assert(p, rest_ce, let_span)
                            }
                            Some(p) => self.destructure_pat(p, rest_ce),
                            None => (self.fresh(), rest_ce),
                        };
                        CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
                    }
                }
            }
        }
    }

    // --- Outer-K threading for nested effect calls in branches ---
    //
    // When an if/case/block has effect calls inside its branches and there is
    // an outer continuation (more statements after it in the enclosing block),
    // these methods thread K through the branches. Abort-style handlers that
    // don't call K will skip the rest of the enclosing block, matching the
    // interpreter's semantics.

    /// Lower an expression with an outer continuation K threaded through branches.
    pub(crate) fn lower_expr_with_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        self.lower_expr_tail(expr, CExpr::Var(k_var.to_string()))
    }

    pub(crate) fn lower_expr_with_k_inner(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        match &expr.kind {
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_var = self.fresh();
                let then_ce = self.lower_branch_with_k(then_branch, k_var);
                let else_ce = self.lower_branch_with_k(else_branch, k_var);
                let case = CExpr::Case(
                    Box::new(CExpr::Var(cond_var.clone())),
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
                );
                let cond_ce = self.lower_operand(cond, "if");
                CExpr::Let(cond_var, Box::new(cond_ce), Box::new(case))
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_var = self.fresh();
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                let arms_ce: Vec<CArm> = arms
                    .iter()
                    .map(|arm| {
                        let saved_handler_vars =
                            self.register_dynamic_handler_pattern_vars(&arm.pattern);
                        let pat = self.lower_pat(
                            &arm.pattern,
                            &self.constructor_atoms,
                            self.handler_origin_module(),
                        );
                        let guard_ce = arm.guard.as_ref().map(|g| self.lower_expr_value(g));
                        let body_ce = self.lower_branch_with_k(&arm.body, k_var);
                        self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
                        CArm {
                            pat,
                            guard: guard_ce,
                            body: body_ce,
                        }
                    })
                    .collect();
                let case = CExpr::Case(Box::new(CExpr::Var(scrut_var.clone())), arms_ce);
                let scrut_ce = self.lower_operand(scrutinee, "case");
                CExpr::Let(scrut_var, Box::new(scrut_ce), Box::new(case))
            }
            ExprKind::Block { stmts, .. } => {
                let stmts: Vec<_> = stmts.iter().map(|a| a.node.clone()).collect();
                self.lower_block_in(&stmts, LowerMode::Tail(CExpr::Var(k_var.to_string())))
            }
            ExprKind::With { expr, handler, .. } => self.lower_with_inherited_return_k(
                expr,
                handler,
                Some(CExpr::Var(k_var.to_string())),
            ),
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                let else_arms: Vec<_> = else_arms.iter().map(|a| a.node.clone()).collect();
                self.lower_do(bindings, success, &else_arms, Some(k_var))
            }
            ExprKind::Receive {
                arms, after_clause, ..
            } => self.lower_receive(arms, after_clause.as_ref(), Some(k_var)),
            ExprKind::Resume { value } if self.branch_is_effectful(value) => {
                let v = self.fresh();
                let result = self.fresh();
                let resumed = self.lower_resume_of_var(&v);
                let body = CExpr::Let(
                    result.clone(),
                    Box::new(resumed),
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(k_var.to_string())),
                        vec![CExpr::Var(result)],
                    )),
                );
                self.lower_bind_effectful_expr(value, v, body)
            }
            // Everything else is evaluated to a value: effect normalization
            // has left nothing in its operands that needs a continuation.
            _ => self.lower_value_to_k(expr, k_var),
        }
    }

    /// Lower a branch expression with an outer continuation K.
    /// Dispatches based on whether the branch is a direct effect call,
    /// contains nested effects, or is a plain expression.
    pub(crate) fn lower_branch_with_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        self.lower_terminal_effectful_expr_to_k(expr, k_var)
    }

    /// Lower a block with an outer continuation K threaded to the terminal.
    /// Like `lower_block` but applies K at terminal positions instead of return_k.
    pub(crate) fn lower_block_with_k(&mut self, stmts: &[Stmt], k_var: &str) -> CExpr {
        match stmts {
            [] => CExpr::Apply(
                Box::new(CExpr::Var(k_var.to_string())),
                vec![CExpr::Tuple(vec![])],
            ),
            [Stmt::Expr(e)] => self.lower_branch_with_k(e, k_var),
            [Stmt::Let { value, .. }] => self.lower_branch_with_k(value, k_var),
            [first, rest @ ..] => {
                // Handler-value let binding: register so `with name` resolves.
                // Mirrors the same detection in `lower_block_with_return_k`.
                if let Stmt::Let { pattern, value, .. } = first
                    && let Pat::Var {
                        name, id: pat_id, ..
                    } = pattern
                    && self.is_handler_value(value)
                {
                    self.lower_handle_binding(name, Some(*pat_id), value);
                    if let Some((var, _effects, _has_return)) =
                        self.handle_dynamic_vars.get(name.as_str()).cloned()
                    {
                        if self.expr_is_effectful_call(value) {
                            let rest_k = self.lower_rest_block_with_k_k(Some(pattern), rest, k_var);
                            return self.lower_expr_with_call_return_k(value, Some(rest_k));
                        }
                        let rhs_ce = self.lower_expr_value(value);
                        let rest_ce = self.lower_block_with_k(rest, k_var);
                        return CExpr::Let(var, Box::new(rhs_ce), Box::new(rest_ce));
                    }
                    return self.lower_block_with_k(rest, k_var);
                }

                let effect_info = match first {
                    Stmt::Expr(e) => collect_effect_call_expr(e)
                        .map(|(head, name, qual, args)| (None, head.id, name, qual, args)),
                    Stmt::Let { pattern, value, .. } => collect_effect_call_expr(value)
                        .map(|(head, name, qual, args)| (Some(pattern), head.id, name, qual, args)),
                    Stmt::LetFun { .. } => None,
                };

                if let Some((pat, effect_call_id, op_name, qualifier, args)) = effect_info {
                    // Direct effect call at statement level: CPS with rest -> K-threaded
                    let inner_k = self.lower_rest_block_with_k_k(pat, rest, k_var);
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(
                        effect_call_id,
                        op_name,
                        qualifier,
                        &args_owned,
                        Some(inner_k),
                    )
                } else {
                    let (pat_opt, value_expr) = match first {
                        Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                        Stmt::Expr(e) => (None, e),
                        Stmt::LetFun { .. } => unreachable!(),
                    };

                    // Check for call to an effectful function. Capture the
                    // rest of the block as _ReturnK so CPS chains correctly
                    // (e.g. state-threading handlers need real continuations).
                    if self.expr_is_effectful_call(value_expr) {
                        let rest_k = self.lower_rest_block_with_k_k(pat_opt, rest, k_var);
                        return self.lower_expr_with_call_return_k(value_expr, Some(rest_k));
                    }

                    if self.has_nested_effectful_expr(value_expr) {
                        // Value has nested effects: build inner K and thread through
                        let inner_k = self.lower_rest_block_with_k_k(pat_opt, rest, k_var);
                        let inner_k_var = self.fresh();
                        let body = self.lower_expr_with_k_inner(value_expr, &inner_k_var);
                        CExpr::Let(inner_k_var, Box::new(inner_k), Box::new(body))
                    } else {
                        // Normal statement: evaluate, bind, then rest with K
                        let val_ce = self.lower_expr(value_expr);
                        let saved_handler_vars = pat_opt
                            .map(|pat| self.register_dynamic_handler_pattern_vars(pat))
                            .unwrap_or_default();
                        let rest_ce = self.lower_block_with_k(rest, k_var);
                        self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
                        let (var, rest_ce) = match pat_opt {
                            Some(p) => self.destructure_pat(p, rest_ce),
                            None => (self.fresh(), rest_ce),
                        };
                        CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
                    }
                }
            }
        }
    }
}
