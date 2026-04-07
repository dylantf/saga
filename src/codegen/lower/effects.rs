/// Effect system lowering: CPS transform, handler building, BEAM-native ops.
///
/// This module handles:
/// - `lower_effect_call`: lowering `op! args` to handler application
/// - `lower_with`: lowering `expr with handler` blocks
/// - `build_op_handler_fun`: building per-op CPS handler functions
/// - `build_beam_native_op_fun`: synthesizing handlers for BEAM-native ops
/// - `resolve_handler`: resolving named/inline handlers to arms
use std::collections::HashSet;

use crate::ast::{Expr, ExprKind, Handler, HandlerArm};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::Lowerer;
use super::util::{cerl_call, collect_fun_call};

impl<'a> Lowerer<'a> {
    fn lower_handler_owned_expr(&mut self, expr: &Expr) -> CExpr {
        // Handler-local computations produce the handled result itself, so they
        // must not inherit an enclosing function/handler return continuation.
        self.lower_expr_value(expr)
    }

    fn lower_handled_expr_with_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        let inner_ce = self.lower_expr_with_installed_return_k(expr, return_k.clone());
        if matches!(expr.kind, ExprKind::Block { .. }) {
            inner_ce
        } else {
            self.apply_return_k_with(return_k, inner_ce)
        }
    }

    fn lower_handled_inner_expr(
        &mut self,
        expr: &Expr,
        handled_return_k: Option<CExpr>,
        inherited_return_k: Option<CExpr>,
    ) -> CExpr {
        let is_direct_effectful_call = collect_fun_call(expr)
            .map(|(name, _, _)| {
                self.is_effectful(name) || self.current_effectful_vars.contains_key(name)
            })
            .unwrap_or(false);

        if is_direct_effectful_call {
            if let Some(rk) = handled_return_k {
                self.lower_expr_with_call_return_k(expr, Some(rk))
            } else if let Some(inherited_rk) = inherited_return_k {
                self.lower_expr_with_call_return_k(expr, Some(inherited_rk))
            } else {
                self.lower_expr(expr)
            }
        } else {
            self.lower_handled_expr_with_return_k(expr, handled_return_k)
        }
    }

    fn dynamic_return_lambda(&mut self, tuple_var: &str, op_count: usize) -> CExpr {
        let param = self.fresh();
        let identity = CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)));
        let tuple_size = cerl_call(
            "erlang",
            "tuple_size",
            vec![CExpr::Var(tuple_var.to_string())],
        );
        let return_index = op_count as i64 + 1;
        let return_lambda = cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(return_index)),
                CExpr::Var(tuple_var.to_string()),
            ],
        );
        CExpr::Case(
            Box::new(tuple_size),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Int(return_index)),
                    guard: None,
                    body: return_lambda,
                },
                CArm {
                    pat: CPat::Var("_".to_string()),
                    guard: None,
                    body: identity,
                },
            ],
        )
    }

    fn build_return_lambda(&mut self, ret: &HandlerArm) -> CExpr {
        let ret_body = self.lower_handler_owned_expr(&ret.body);
        let (param, body) = if ret.params.is_empty() {
            (self.fresh(), ret_body)
        } else {
            self.destructure_pat(&ret.params[0], ret_body)
        };
        CExpr::Fun(vec![param], Box::new(body))
    }

    fn compose_return_lambdas(&mut self, lambdas: Vec<CExpr>) -> Option<CExpr> {
        let mut iter = lambdas.into_iter();
        let first = iter.next()?;
        Some(iter.fold(first, |inner, outer| {
            let param = self.fresh();
            let applied_inner = CExpr::Apply(Box::new(inner), vec![CExpr::Var(param.clone())]);
            let applied_outer = CExpr::Apply(Box::new(outer), vec![applied_inner]);
            CExpr::Fun(vec![param], Box::new(applied_outer))
        }))
    }

    /// Lower an effect call: `op! args`.
    ///
    /// Emits: `apply _Handle_Effect_op(arg1, ..., argN, K)`
    ///
    /// If `continuation` is Some, it's the pre-built K closure. If None
    /// (standalone effect call not in a block), we use an identity continuation.
    pub(super) fn lower_effect_call(
        &mut self,
        op_name: &str,
        qualifier: Option<&str>,
        args: &[Expr],
        continuation: Option<CExpr>,
    ) -> CExpr {
        // Resolve the effect name (canonical form).
        let effect_name = if let Some(q) = qualifier {
            self.canonicalize_effect(q)
        } else {
            self.op_to_effect
                .get(op_name)
                .unwrap_or_else(|| panic!("unknown effect operation: {}", op_name))
                .clone()
        };
        let effect_key = format!("{}.{}", effect_name, op_name);

        // Find the per-op handler param variable.
        let handler_var = self
            .current_handler_params
            .get(&effect_key)
            .unwrap_or_else(|| {
                panic!(
                    "no handler param for op '{}.{}', handler_params: {:?}",
                    effect_name, op_name, self.current_handler_params
                )
            })
            .clone();

        // Build: apply Handler(arg1, ..., argN, K)
        // Per-op handlers have natural arity -- no atom dispatch, no padding.
        let runtime_param_count = self
            .effect_defs
            .get(&effect_name)
            .and_then(|effect| effect.ops.get(op_name))
            .copied()
            .unwrap_or(args.len());
        let mut unit_args_to_erase = args.len().saturating_sub(runtime_param_count);
        let mut call_args = Vec::new();
        let mut bindings = Vec::new();
        for arg in args {
            let is_unit_literal = matches!(
                arg.kind,
                ExprKind::Lit {
                    value: crate::ast::Lit::Unit,
                    ..
                }
            );
            if is_unit_literal && unit_args_to_erase > 0 {
                unit_args_to_erase -= 1;
                continue;
            }
            let v = self.fresh();
            let ce = self.lower_expr_value(arg);
            bindings.push((v.clone(), ce));
            call_args.push(CExpr::Var(v));
        }

        // Append continuation. If the handler arm never calls resume, pass a cheap atom
        // instead of a real closure so Erlang doesn't warn about a constructed-but-unused term.
        let k = if self.no_resume_ops.contains(effect_key.as_str()) {
            CExpr::Lit(CLit::Atom("no_resume".to_string()))
        } else {
            continuation.unwrap_or_else(|| {
                // Identity continuation for standalone effect calls
                let param = self.fresh();
                CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)))
            })
        };
        call_args.push(k);

        let apply = CExpr::Apply(Box::new(CExpr::Var(handler_var)), call_args);

        // Wrap with let-bindings for args
        bindings.into_iter().rev().fold(apply, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    /// Build a per-op handler function for a single BEAM-native operation.
    /// Synthesizes: `fun (Arg0, ..., ArgN, K) -> let R = <native call> in K(R)`
    ///
    /// `handler_canonical` identifies which handler is providing this op,
    /// used to dispatch handler-specific lowerings (e.g. beam_ref vs ets_ref).
    fn build_beam_native_op_fun(
        &mut self,
        op_name: &str,
        handler_canonical: &str,
    ) -> CExpr {
        let (_, _, param_count) = super::beam_interop::lookup_native_op(op_name)
            .unwrap_or_else(|| panic!("unknown BEAM-native op: {}", op_name));

        let k_var = self.fresh();
        let param_vars: Vec<String> = (0..param_count).map(|i| format!("_HArg{}", i)).collect();

        let mut fun_params: Vec<String> = param_vars.clone();
        fun_params.push(k_var.clone());

        let call = if super::beam_interop::is_ref_op(op_name) {
            super::beam_interop::build_ref_native_call(
                handler_canonical,
                op_name,
                &param_vars,
                &mut || self.fresh(),
            )
        } else {
            let ctor_atoms = self.constructor_atoms.clone();
            super::beam_interop::build_native_call(
                op_name,
                &param_vars,
                &ctor_atoms,
                &mut || self.fresh(),
            )
        };

        let result_var = self.fresh();
        let body = CExpr::Let(
            result_var.clone(),
            Box::new(call),
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(k_var.clone())),
                vec![CExpr::Var(result_var)],
            )),
        );

        CExpr::Fun(fun_params, Box::new(body))
    }

    /// Lower a `with` expression: `expr with handler`.
    ///
    /// Builds handler function(s) from the handler definition and passes them
    /// as extra parameters to the effectful computation.
    pub(super) fn lower_with(&mut self, expr: &Expr, handler: &Handler) -> CExpr {
        // Check for dynamic handler (tuple-of-lambdas) before static resolution.
        // Dynamic handlers are variables bound via `handle name = some_func()`.
        if let Some(dynamic_info) = self.check_dynamic_handler(handler) {
            return self.lower_with_dynamic(expr, dynamic_info);
        }

        // Collect effects from BEAM-native handlers in this `with` block.
        // Maps effect name -> handler canonical name, so handler-specific ops
        // (e.g. beam_ref vs ets_ref) can dispatch on the handler identity.
        let beam_native_effects: std::collections::HashMap<String, String> = match handler {
            Handler::Named(name, _) if self.is_beam_native_handler(name) => {
                let canonical = self.resolve_handler_name(name);
                self.handler_defs[&canonical]
                    .effects
                    .iter()
                    .map(|eff| (eff.clone(), canonical.clone()))
                    .collect()
            }
            Handler::Inline { named, .. } => named
                .iter()
                .filter(|a| self.is_beam_native_handler(&a.node.name))
                .flat_map(|a| {
                    let canonical = self.resolve_handler_name(&a.node.name);
                    self.handler_defs[&canonical]
                        .effects
                        .iter()
                        .map(move |eff| (eff.clone(), canonical.clone()))
                })
                .collect(),
            _ => std::collections::HashMap::new(),
        };

        // Check for conditional handle bindings and extract the handler name
        let handle_name = match handler {
            Handler::Named(name, _) => Some(name.clone()),
            Handler::Inline { named, .. } if named.len() == 1 && !named[0].node.name.is_empty() => {
                Some(named[0].node.name.clone())
            }
            _ => None,
        };
        let cond_info = handle_name
            .as_ref()
            .and_then(|name| self.handle_cond_vars.get(name).cloned());

        // Resolve all handler arms, return clause, and which effects are handled
        let (all_arms, return_clause, handled_effects) = self.resolve_handler(handler);

        // Index handler arms by (effect.op or bare op) for quick lookup.
        // Qualified arms use "EffectName.op" as key, unqualified use bare "op".
        let mut arms_by_op: std::collections::HashMap<String, &HandlerArm> =
            std::collections::HashMap::new();
        for arm in &all_arms {
            if let Some(ref q) = arm.qualifier {
                let canonical = self.canonicalize_effect(q);
                arms_by_op.insert(format!("{}.{}", canonical, arm.op_name), arm);
            } else {
                arms_by_op.insert(arm.op_name.clone(), arm);
            }
        }

        // Collect all (effect, op) pairs for handled effects
        let handler_ops = self.effect_handler_ops(&handled_effects);

        // For each op, build a handler function and bind it.
        // Two passes: first register all param names (so handler arm bodies
        // can reference sibling handlers via closure capture),
        // then build the handler functions.
        let saved_handler_params = self.current_handler_params.clone();
        let saved_no_resume_ops = self.no_resume_ops.clone();

        // Pass 1: register all handler param variables (one per op)
        let mut op_vars: Vec<(String, String, String)> = Vec::new(); // (effect, op, var_name)
        for (eff, op) in &handler_ops {
            let var_name = Self::handler_param_name(eff, op);
            let key = format!("{}.{}", eff, op);
            self.current_handler_params
                .insert(key.clone(), var_name.clone());
            // Track arms that never call resume so call sites can skip building a real continuation.
            let qualified_key = format!("{}.{}", eff, op);
            if let Some(arm) = arms_by_op
                .get(&qualified_key)
                .or_else(|| arms_by_op.get(op.as_str()))
                && !arm.body.contains_resume()
            {
                self.no_resume_ops.insert(key);
            }
            op_vars.push((eff.clone(), op.clone(), var_name));
        }

        // Pass 2: build ALL handler functions unconditionally.
        // We'll prune unreachable ones after lowering the body.
        // BEAM-native ops are emitted first since they're self-contained
        // (direct BEAM calls, no closures). CPS handlers may reference them
        // (e.g. async_handler's body calls spawn!/send!), so they must come after.
        let mut handler_bindings: Vec<(String, CExpr)> = Vec::new();
        for (eff, op, var_name) in &op_vars {
            if let Some(handler_canonical) = beam_native_effects.get(eff) {
                let handler_fun = self.build_beam_native_op_fun(op, handler_canonical);
                handler_bindings.push((var_name.clone(), handler_fun));
            }
        }
        // For conditional handle bindings, resolve the else-branch handler arms too
        let else_arms_by_op: Option<std::collections::HashMap<String, HandlerArm>> =
            cond_info.as_ref().and_then(|(_, _, _, else_canonical)| {
                self.handler_defs.get(else_canonical).map(|info| {
                    let mut map = std::collections::HashMap::new();
                    for arm in &info.arms {
                        if let Some(ref q) = arm.qualifier {
                            let canonical = self.canonicalize_effect(q);
                            map.insert(format!("{}.{}", canonical, arm.op_name), arm.clone());
                        } else {
                            map.insert(arm.op_name.clone(), arm.clone());
                        }
                    }
                    map
                })
            });

        for (eff, op, var_name) in &op_vars {
            if !beam_native_effects.contains_key(eff) {
                let qualified_key = format!("{}.{}", eff, op);
                if let Some(arm) = arms_by_op
                    .get(&qualified_key)
                    .or_else(|| arms_by_op.get(op.as_str()))
                {
                    // Check if this is a conditional handle binding
                    if let Some(ref else_map) = else_arms_by_op {
                        let else_arm = else_map
                            .get(&qualified_key)
                            .or_else(|| else_map.get(op.as_str()))
                            .cloned();
                        if let Some(else_arm) = &else_arm {
                            let cond_var = &cond_info.as_ref().unwrap().0;
                            let then_fun = self.build_op_handler_fun(arm);
                            let else_fun = self.build_op_handler_fun(else_arm);
                            // Build a wrapper that dispatches based on condition:
                            // fun(Args..., K) -> case CondVar of true -> then_fun(Args, K); _ -> else_fun(Args, K)
                            let n_params = arm.params.len() + 1; // +1 for K
                            let wrapper_params: Vec<String> =
                                (0..n_params).map(|i| format!("_HW{}", i)).collect();
                            let args_ce: Vec<CExpr> = wrapper_params
                                .iter()
                                .map(|p| CExpr::Var(p.clone()))
                                .collect();
                            let then_call = CExpr::Apply(Box::new(then_fun), args_ce.clone());
                            let else_call = CExpr::Apply(Box::new(else_fun), args_ce);
                            let case_expr = CExpr::Case(
                                Box::new(CExpr::Var(cond_var.to_string())),
                                vec![
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                                        guard: None,
                                        body: then_call,
                                    },
                                    CArm {
                                        pat: CPat::Var("_".to_string()),
                                        guard: None,
                                        body: else_call,
                                    },
                                ],
                            );
                            handler_bindings.push((
                                var_name.clone(),
                                CExpr::Fun(wrapper_params, Box::new(case_expr)),
                            ));
                            continue;
                        }
                    }
                    let handler_fun = self.build_op_handler_fun(arm);
                    handler_bindings.push((var_name.clone(), handler_fun));
                } else {
                    // No handler arm for this op -- passthrough (call K with unit).
                    let k_param = self.fresh();
                    handler_bindings.push((
                        var_name.clone(),
                        CExpr::Fun(
                            vec![k_param.clone()],
                            Box::new(CExpr::Apply(
                                Box::new(CExpr::Var(k_param)),
                                vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
                            )),
                        ),
                    ));
                }
            }
        }

        // Build the return clause lambda (if present).
        let saved_return_k = None;
        let mut return_lambdas: Vec<CExpr> = Vec::new();
        if let Some(ret) = &return_clause {
            return_lambdas.push(self.build_return_lambda(ret));
        }
        let return_k_lambda = self.compose_return_lambdas(return_lambdas);

        // Direct effectful calls receive the handled return-k as `_ReturnK`.
        // When there is no return clause, the inherited outer return-k still
        // needs to flow through so abort-style handlers skip subsequent code.
        let result = self.lower_handled_inner_expr(expr, return_k_lambda, saved_return_k);

        self.current_handler_params = saved_handler_params;
        self.no_resume_ops = saved_no_resume_ops;
        // Post-hoc reachability: scan the lowered body for _Handle_* references,
        // then transitively close through handler binding values.
        let mut needed: HashSet<String> = HashSet::new();
        result.collect_handle_refs(&mut needed);
        // Transitive closure: handler arms can reference other handler vars
        let mut changed = true;
        while changed {
            changed = false;
            for (var, val) in &handler_bindings {
                if needed.contains(var) {
                    let mut refs = HashSet::new();
                    val.collect_handle_refs(&mut refs);
                    for r in refs {
                        if needed.insert(r) {
                            changed = true;
                        }
                    }
                }
            }
        }

        // Only emit bindings that are actually referenced
        handler_bindings.retain(|(var, _)| needed.contains(var));

        // Wrap handler bindings around the result
        let mut output = handler_bindings
            .into_iter()
            .rev()
            .fold(result, |body, (var, val)| {
                CExpr::Let(var, Box::new(val), Box::new(body))
            });

        // For conditional handle bindings, wrap the condition variable binding
        // around everything so handler arms can reference it.
        if let Some((cond_var, cond_ce, _, _)) = cond_info {
            output = CExpr::Let(cond_var, Box::new(cond_ce), Box::new(output));
        }

        output
    }

    /// Build a per-op handler function from a single handler arm.
    ///
    /// Produces: `fun (Arg0, ..., ArgN, K) -> body`
    /// Each op gets its own function with natural arity.
    ///
    /// When the arm has a `finally` block, `current_handler_finally` is set so
    /// that each `resume` site inlines try/catch around the K call. This ensures
    /// the cleanup code is lowered in the correct lexical scope (where arm body
    /// variables like `conn` are bound). For abort handlers (no resume), cleanup
    /// is appended after the arm body.
    fn build_op_handler_fun(&mut self, arm: &HandlerArm) -> CExpr {
        let has_resume = arm.body.contains_resume();

        // If resume is never called, use `_` (Core Erlang wildcard) so the compiler
        // doesn't warn about the unused continuation parameter. Safe because
        // `contains_resume()` being false guarantees no Resume node exists in the arm
        // body, so `current_handler_k` ("<_>") is never read during lowering.
        let k_var = if has_resume {
            self.fresh()
        } else {
            "_".to_string()
        };
        let param_vars: Vec<String> = (0..arm.params.len())
            .map(|i| format!("_HArg{}", i))
            .collect();

        let mut fun_params: Vec<String> = param_vars.clone();
        fun_params.push(k_var.clone());

        // Set up K for resume references in the body.
        // The handler arm body is owned by the handler: it produces the
        // handled computation's result itself rather than flowing into an
        // enclosing function-level return continuation.
        let prev_handler_k = self.current_handler_k.replace(k_var);

        // Set current_handler_finally so Resume lowering wraps K calls in try/catch.
        let saved_finally = self.current_handler_finally.take();
        if let Some(ref fb) = arm.finally_block {
            self.current_handler_finally = Some(fb.as_ref().clone());
        }

        let mut body_ce = self.lower_handler_owned_expr(&arm.body);

        self.current_handler_finally = saved_finally;

        // Bind arm's params (possibly patterns) to the positional handler args
        for (i, pat) in arm.params.iter().enumerate().rev() {
            let (var, wrapped_body) = self.destructure_pat(pat, body_ce);
            body_ce = CExpr::Let(
                var,
                Box::new(CExpr::Var(param_vars[i].clone())),
                Box::new(wrapped_body),
            );
        }

        // For abort handlers (no resume) with finally: append cleanup after body.
        // The cleanup is lowered here because the arm body's let-bindings are not
        // in scope — but for abort handlers, the typical pattern is that the resource
        // was never acquired (the handler failed early), so cleanup referencing
        // body-local variables is unlikely. If it does reference arm params, those
        // are in scope via the param bindings above.
        if let (Some(fb), false) = (&arm.finally_block, has_resume) {
            let cleanup_ce = self.lower_expr(fb);
            let result_var = self.fresh();
            body_ce = CExpr::Let(
                result_var.clone(),
                Box::new(body_ce),
                Box::new(CExpr::Let(
                    "_".to_string(),
                    Box::new(cleanup_ce),
                    Box::new(CExpr::Var(result_var)),
                )),
            );
        }

        self.current_handler_k = prev_handler_k;
        CExpr::Fun(fun_params, Box::new(body_ce))
    }

    /// Resolve a Handler into a flat list of arms, optional return clause,
    /// and the set of handled effects.
    fn resolve_handler(
        &self,
        handler: &Handler,
    ) -> (Vec<HandlerArm>, Option<Box<HandlerArm>>, Vec<String>) {
        match handler {
            Handler::Named(name, _) => {
                let canonical = self.resolve_handler_name(name);
                let info = self.handler_defs.get(&canonical).unwrap_or_else(|| {
                    panic!("unknown handler: {} (canonical: {})", name, canonical)
                });
                (
                    info.arms.clone(),
                    info.return_clause.clone(),
                    info.effects.clone(),
                )
            }
            Handler::Inline {
                named,
                arms,
                return_clause,
                ..
            } => {
                let mut all_arms = Vec::new();
                let mut resolved_return = return_clause.clone();
                let mut handled_effects = Vec::new();

                for ann in named {
                    let name = &ann.node.name;
                    let canonical = self.resolve_handler_name(name);
                    let info = self.handler_defs.get(&canonical).unwrap_or_else(|| {
                        panic!("unknown handler: {} (canonical: {})", name, canonical)
                    });
                    all_arms.extend(info.arms.iter().cloned());
                    handled_effects.extend(info.effects.iter().cloned());
                    if resolved_return.is_none() {
                        resolved_return = info.return_clause.clone();
                    }
                }

                all_arms.extend(arms.iter().map(|a| a.node.clone()));

                // Determine effects from inline arms
                for arm in arms {
                    let eff = if let Some(ref q) = arm.node.qualifier {
                        Some(self.canonicalize_effect(q))
                    } else {
                        self.op_to_effect.get(&arm.node.op_name).cloned()
                    };
                    if let Some(eff) = eff
                        && !handled_effects.contains(&eff)
                    {
                        handled_effects.push(eff);
                    }
                }

                (all_arms, resolved_return, handled_effects)
            }
        }
    }

    /// Check if a handler reference is a dynamic handler (tuple-of-lambdas).
    /// Returns Some((tuple_var, effects)) if so.
    fn check_dynamic_handler(&self, handler: &Handler) -> Option<(String, Vec<String>, bool)> {
        let name = match handler {
            Handler::Named(name, _) => name,
            Handler::Inline { named, .. } if named.len() == 1 && !named[0].node.name.is_empty() => {
                &named[0].node.name
            }
            _ => return None,
        };
        self.handle_dynamic_vars.get(name).cloned()
    }

    /// Lower a `with` expression for a dynamic handler (tuple-of-lambdas).
    /// Destructures the handler tuple to extract per-op handler functions.
    fn lower_with_dynamic(
        &mut self,
        expr: &Expr,
        dynamic_info: (String, Vec<String>, bool),
    ) -> CExpr {
        let (tuple_var, handled_effects, _has_return) = dynamic_info;
        let handler_ops = self.effect_handler_ops(&handled_effects);

        // Save handler params and set up per-op params from tuple elements
        let saved_handler_params = self.current_handler_params.clone();
        let saved_no_resume_ops = self.no_resume_ops.clone();

        let mut handler_bindings: Vec<(String, CExpr)> = Vec::new();
        for (i, (eff, op)) in handler_ops.iter().enumerate() {
            let var_name = Self::handler_param_name(eff, op);
            let key = format!("{}.{}", eff, op);
            self.current_handler_params.insert(key, var_name.clone());
            // Extract from tuple: erlang:element(I+1, TupleVar)
            let element_call = super::util::cerl_call(
                "erlang",
                "element",
                vec![
                    CExpr::Lit(CLit::Int(i as i64 + 1)),
                    CExpr::Var(tuple_var.clone()),
                ],
            );
            handler_bindings.push((var_name, element_call));
        }

        // Lower the inner expression
        let return_k_lambda = Some(self.dynamic_return_lambda(&tuple_var, handler_ops.len()));
        let inherited_return_k = None;
        let result = self.lower_handled_inner_expr(expr, return_k_lambda, inherited_return_k);

        self.current_handler_params = saved_handler_params;
        self.no_resume_ops = saved_no_resume_ops;

        // Wrap handler bindings around the result
        handler_bindings
            .into_iter()
            .rev()
            .fold(result, |body, (var, val)| {
                CExpr::Let(var, Box::new(val), Box::new(body))
            })
    }

    /// Lower a handler expression to a tuple of per-op handler lambdas.
    /// Used when a handler expression appears as a value (returned from function,
    /// passed as argument, etc.) rather than in a `handle` binding.
    ///
    /// The tuple layout is: ops sorted alphabetically by "Effect.op" key,
    /// with an optional return clause lambda as the last element.
    pub(super) fn lower_handler_expr_to_tuple(&mut self, body: &crate::ast::HandlerBody) -> CExpr {
        let canonical_effects: Vec<String> = body
            .effects
            .iter()
            .map(|e| self.canonicalize_effect(&e.name))
            .collect();
        let handler_ops = self.effect_handler_ops(&canonical_effects);

        // Index arms by op name for quick lookup
        let arms_by_op: std::collections::HashMap<&str, &crate::ast::HandlerArm> = body
            .arms
            .iter()
            .map(|a| (a.node.op_name.as_str(), &a.node))
            .collect();

        let mut tuple_elements = Vec::new();
        for (_eff, op) in &handler_ops {
            if let Some(arm) = arms_by_op.get(op.as_str()) {
                tuple_elements.push(self.build_op_handler_fun(arm));
            } else {
                // Passthrough: identity continuation
                let k_param = self.fresh();
                tuple_elements.push(CExpr::Fun(
                    vec![k_param.clone()],
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(k_param)),
                        vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
                    )),
                ));
            }
        }
        if let Some(rc) = &body.return_clause {
            let ret_body = self.lower_expr(&rc.body);
            let (param, body) = if rc.params.is_empty() {
                (self.fresh(), ret_body)
            } else {
                self.destructure_pat(&rc.params[0], ret_body)
            };
            tuple_elements.push(CExpr::Fun(vec![param], Box::new(body)));
        }
        CExpr::Tuple(tuple_elements)
    }

    /// Lower a named handler definition to a tuple-of-lambdas.
    /// Used when a handler name appears as a value (e.g. returned from a function,
    /// passed as an argument) rather than in a `with` block.
    pub(super) fn lower_handler_def_to_tuple(&mut self, handler_name: &str) -> Option<CExpr> {
        let canonical = self.resolve_handler_name(handler_name);
        let info = self.handler_defs.get(&canonical)?.clone();
        let handler_ops = self.effect_handler_ops(&info.effects);

        let mut tuple_elements = Vec::new();
        for (_eff, op) in &handler_ops {
            if let Some(arm) = info.arms.iter().find(|a| a.op_name == *op) {
                tuple_elements.push(self.build_op_handler_fun(arm));
            } else {
                let k_param = self.fresh();
                tuple_elements.push(CExpr::Fun(
                    vec![k_param.clone()],
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(k_param)),
                        vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
                    )),
                ));
            }
        }
        if let Some(rc) = &info.return_clause {
            let ret_body = self.lower_expr(&rc.body);
            let (param, body) = if rc.params.is_empty() {
                (self.fresh(), ret_body)
            } else {
                self.destructure_pat(&rc.params[0], ret_body)
            };
            tuple_elements.push(CExpr::Fun(vec![param], Box::new(body)));
        }
        Some(CExpr::Tuple(tuple_elements))
    }
}
