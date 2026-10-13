use crate::ast::{Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;
use std::collections::HashMap;

impl<'a> Lowerer<'a> {
    /// The one block lowerer. With `k`, the value of the block is passed to
    /// that continuation; without, it is returned.
    ///
    /// A statement that performs effects is lowered in tail position with
    /// the rest of the block as its continuation (`lower_statement`).
    pub(crate) fn lower_block(&mut self, stmts: &[Stmt], k: Option<CExpr>) -> CExpr {
        match stmts {
            [] => self.apply_return_k_with(k, CExpr::Tuple(vec![])), // unit
            [Stmt::Expr(e)] => self.lower_tail(e, k),
            // A block that ends in a `let` has the bound value as its value.
            [first @ Stmt::Let { pattern, .. }] => {
                let value = match pat_binding_var(pattern) {
                    Some(var) => CExpr::Var(var),
                    None => CExpr::Tuple(vec![]),
                };
                self.lower_statement(first, |this| this.apply_return_k_with(k, value))
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
                let param_absorbed_effects = self
                    .check_result
                    .resolved_type_for_node(fun_id)
                    .map(|ty| {
                        param_absorbed_effects_from_type(&ty)
                            .into_iter()
                            .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                            .collect::<HashMap<usize, Vec<String>>>()
                    })
                    .unwrap_or_default();
                let arity = callable_abi.expanded_arity();
                let param_names: Vec<String> = (0..arity).map(|i| format!("_LF{}", i)).collect();

                // Register in fun_info BEFORE lowering body so recursive
                // calls are recognized as saturated apply
                let fun_info =
                    FunInfo::from_abi(callable_abi.clone(), param_absorbed_effects, 0);
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
                    let body_ce = self.lower_tail(body, effect_return_k.clone());
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
                            let body_ce = self.lower_tail(body, effect_return_k.clone());
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

                let rest_ce = self.lower_block(rest, k);

                CExpr::LetRec(vec![(fun_name, arity, fun_body)], Box::new(rest_ce))
            }
            [first, rest @ ..] => self.lower_statement(first, |this| this.lower_block(rest, k)),
        }
    }

    /// Lower one `let` or expression statement followed by `rest`.
    ///
    /// If its value performs effects, the value is lowered in tail position
    /// with `fun pattern -> rest` as its continuation, so a handler that
    /// does not resume skips the rest. Otherwise the value is bound and
    /// `rest` follows.
    fn lower_statement(&mut self, stmt: &Stmt, rest: impl FnOnce(&mut Self) -> CExpr) -> CExpr {
        let (pat_opt, value, is_assert, span) = match stmt {
            Stmt::Let {
                pattern,
                value,
                assert,
                span,
                ..
            } => (Some(pattern), value, *assert, *span),
            Stmt::Expr(e) => (None, e, false, e.span),
            Stmt::LetFun { .. } => unreachable!("local functions are lowered by lower_block"),
        };

        // A `let` of a handler value registers the handler so `with name`
        // resolves: a compile-time alias for a static reference, a synthetic
        // dispatching handler for a conditional, a bound tuple otherwise.
        if let Some(Pat::Var {
            name, id: pat_id, ..
        }) = pat_opt
            && self.is_handler_value(value)
        {
            self.lower_handle_binding(name, Some(*pat_id), value);
            let Some((var, _, _)) = self.handle_dynamic_vars.get(name.as_str()).cloned() else {
                return rest(self);
            };
            if !self.takes_continuation(value) {
                let rhs_ce = self.lower_expr(value);
                let rest_ce = rest(self);
                return CExpr::Let(var, Box::new(rhs_ce), Box::new(rest_ce));
            }
        }

        if self.takes_continuation(value) {
            let saved_handler_vars = pat_opt
                .map(|pat| self.register_dynamic_handler_pattern_vars(pat))
                .unwrap_or_default();
            let rest_ce = rest(self);
            self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
            let (param, rest_ce) = match pat_opt {
                Some(p) if is_assert => self.destructure_pat_assert(p, rest_ce, span),
                Some(p) => self.destructure_pat(p, rest_ce),
                None => (self.fresh(), rest_ce),
            };
            let rest_k = CExpr::Fun(vec![param], Box::new(rest_ce));
            return self.lower_tail(value, Some(rest_k));
        }

        let val_ce = self.lower_expr(value);
        let hof_binding = match stmt {
            Stmt::Let {
                pattern: Pat::Var { name, .. },
                value,
                ..
            } => self
                .hof_direct_binding_for_value_expr(value)
                .map(|binding| (name.clone(), binding)),
            _ => None,
        };
        let saved_hof_binding = hof_binding.as_ref().and_then(|(name, specialization)| {
            self.direct_hof_value_bindings
                .insert(name.clone(), specialization.clone())
        });
        let saved_handler_vars = pat_opt
            .map(|pat| self.register_dynamic_handler_pattern_vars(pat))
            .unwrap_or_default();
        let rest_ce = rest(self);
        self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
        if let Some((name, _)) = hof_binding {
            if let Some(saved) = saved_hof_binding {
                self.direct_hof_value_bindings.insert(name, saved);
            } else {
                self.direct_hof_value_bindings.remove(&name);
            }
        }
        let (var, rest_ce) = match pat_opt {
            Some(p) if is_assert => self.destructure_pat_assert(p, rest_ce, span),
            Some(p) => self.destructure_pat(p, rest_ce),
            None => (self.fresh(), rest_ce),
        };
        CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
    }
}
