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
use crate::codegen::cerl::{CExpr, CLit};

use super::Lowerer;
use super::util::{collect_fun_call, core_var};

impl<'a> Lowerer<'a> {
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
        // Find which effect this op belongs to
        let effect_name = if let Some(q) = qualifier {
            q.to_string()
        } else {
            self.op_to_effect
                .get(op_name)
                .unwrap_or_else(|| panic!("unknown effect operation: {}", op_name))
                .clone()
        };

        // Find the per-op handler param variable
        let key = format!("{}.{}", effect_name, op_name);
        let handler_var = self
            .current_handler_params
            .get(&key)
            .unwrap_or_else(|| {
                panic!(
                    "no handler param for op '{}.{}', handler_params: {:?}",
                    effect_name, op_name, self.current_handler_params
                )
            })
            .clone();

        // Build: apply Handler(arg1, ..., argN, K)
        // Per-op handlers have natural arity -- no atom dispatch, no padding.
        let mut call_args = Vec::new();
        let mut bindings = Vec::new();
        for arg in args {
            // Skip unit literal args (they don't exist at the BEAM level)
            if matches!(
                arg.kind,
                ExprKind::Lit {
                    value: crate::ast::Lit::Unit,
                    ..
                }
            ) {
                continue;
            }
            let v = self.fresh();
            let ce = self.lower_expr(arg);
            bindings.push((v.clone(), ce));
            call_args.push(CExpr::Var(v));
        }

        // Append continuation. If the handler arm never calls resume, pass a cheap atom
        // instead of a real closure so Erlang doesn't warn about a constructed-but-unused term.
        let k = if self.no_resume_ops.contains(key.as_str()) {
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

    /// Op-name to BEAM BIF mapping for native effect operations.
    /// Returns (erlang_module, erlang_func, param_count).
    fn beam_native_op_info(op_name: &str) -> Option<(&'static str, &'static str, usize)> {
        match op_name {
            "spawn" => Some(("erlang", "spawn", 1)),
            "self" => Some(("erlang", "self", 0)),
            "send" => Some(("erlang", "send", 2)),
            "monitor" => Some(("erlang", "monitor", 1)), // gets 'process' atom prepended
            "demonitor" => Some(("erlang", "demonitor", 1)),
            "link" => Some(("erlang", "link", 1)),
            "unlink" => Some(("erlang", "unlink", 1)),
            "sleep" => Some(("timer", "sleep", 1)),
            "cancel_timer" => Some(("erlang", "cancel_timer", 1)),
            "send_after" => Some(("erlang", "send_after", 3)), // args reordered
            _ => None,
        }
    }

    /// Build a per-op handler function for a single BEAM-native operation.
    /// Synthesizes: `fun (Arg0, ..., ArgN, K) -> let R = mod:func(...) in K(R)`
    fn build_beam_native_op_fun(&mut self, op_name: &str) -> CExpr {
        let (module, func, param_count) = Self::beam_native_op_info(op_name)
            .unwrap_or_else(|| panic!("unknown BEAM-native op: {}", op_name));

        let k_var = self.fresh();
        let param_vars: Vec<String> = (0..param_count).map(|i| format!("_HArg{}", i)).collect();

        let mut fun_params: Vec<String> = param_vars.clone();
        fun_params.push(k_var.clone());

        // Build the BEAM call args from handler params
        let call_args = match op_name {
            "self" => vec![],
            "monitor" => {
                let mut a = vec![CExpr::Lit(CLit::Atom("process".into()))];
                a.push(CExpr::Var(param_vars[0].clone()));
                a
            }
            "send_after" => {
                // reorder: pid, ms, msg -> ms, pid, msg
                vec![
                    CExpr::Var(param_vars[1].clone()),
                    CExpr::Var(param_vars[0].clone()),
                    CExpr::Var(param_vars[2].clone()),
                ]
            }
            _ => param_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
        };

        let call = CExpr::Call(module.to_string(), func.to_string(), call_args);

        // let Result = call(...) in K(Result)
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
        // Collect effects from BEAM-native handlers in this `with` block.
        let beam_native_effects: std::collections::HashSet<String> = match handler {
            Handler::Named(name, _) if self.is_beam_native_handler(name) => {
                self.handler_defs[name].effects.iter().cloned().collect()
            }
            Handler::Inline { named, .. } => named
                .iter()
                .filter(|n| self.is_beam_native_handler(n))
                .flat_map(|n| self.handler_defs[n].effects.clone())
                .collect(),
            _ => std::collections::HashSet::new(),
        };

        // Resolve all handler arms, return clause, and which effects are handled
        let (all_arms, return_clause, handled_effects) = self.resolve_handler(handler);

        // Index handler arms by op name for quick lookup
        let mut arms_by_op: std::collections::HashMap<String, &HandlerArm> =
            std::collections::HashMap::new();
        for arm in &all_arms {
            arms_by_op.insert(arm.op_name.clone(), arm);
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
            self.current_handler_params.insert(key.clone(), var_name.clone());
            // Track arms that never call resume so call sites can skip building a real continuation.
            if let Some(arm) = arms_by_op.get(op.as_str())
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
            if beam_native_effects.contains(eff) {
                let handler_fun = self.build_beam_native_op_fun(op);
                handler_bindings.push((var_name.clone(), handler_fun));
            }
        }
        for (eff, op, var_name) in &op_vars {
            if !beam_native_effects.contains(eff) {
                if let Some(arm) = arms_by_op.get(op.as_str()) {
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
        let saved_return_k = self.current_return_k.take();
        let return_k_lambda = if let Some(ret) = &return_clause {
            let param = if ret.params.is_empty() {
                self.fresh()
            } else {
                core_var(&ret.params[0].0)
            };
            let ret_body = self.lower_expr(&ret.body);
            Some(CExpr::Fun(vec![param], Box::new(ret_body)))
        } else {
            None
        };

        // Check if the inner expression is a direct effectful function call.
        // If so, pass the return clause as _ReturnK parameter instead of
        // wrapping externally. This prevents abort values from being wrapped.
        let is_direct_effectful_call = collect_fun_call(expr)
            .map(|(name, _, _)| {
                self.is_effectful(name) || self.current_effectful_vars.contains_key(name)
            })
            .unwrap_or(false);

        let result = if is_direct_effectful_call {
            // Pass return clause as _ReturnK to the callee via pending_callee_return_k.
            // When there IS a return clause: save the outer pending (e.g. rest-of-block
            // continuation) so the block can apply it to the CPS result afterwards.
            // When there is NO return clause: let the outer pending flow through as
            // _ReturnK so abort-style handlers skip subsequent statements.
            if let Some(rk) = return_k_lambda {
                let saved_outer = self.pending_callee_return_k.take();
                self.pending_callee_return_k = Some(rk);
                let ce = self.lower_expr(expr);
                self.pending_callee_return_k = saved_outer;
                ce
            } else {
                self.lower_expr(expr)
            }
        } else {
            // Block form or non-call: use current_return_k for terminal application
            if let Some(rk) = return_k_lambda {
                self.current_return_k = Some(rk);
            }
            let inner_ce = self.lower_expr(expr);
            // Block expressions apply current_return_k internally (at the terminal
            // statement), so don't apply it again here to avoid double-wrapping.
            if matches!(expr.kind, ExprKind::Block { .. }) {
                inner_ce
            } else {
                self.apply_return_k(inner_ce)
            }
        };

        self.current_handler_params = saved_handler_params;
        self.no_resume_ops = saved_no_resume_ops;
        self.current_return_k = saved_return_k;

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

        handler_bindings
            .into_iter()
            .rev()
            .fold(result, |body, (var, val)| {
                CExpr::Let(var, Box::new(val), Box::new(body))
            })
    }

    /// Build a per-op handler function from a single handler arm.
    ///
    /// Produces: `fun (Arg0, ..., ArgN, K) -> body`
    /// Each op gets its own function with natural arity.
    fn build_op_handler_fun(&mut self, arm: &HandlerArm) -> CExpr {
        // If resume is never called, use `_` (Core Erlang wildcard) so the compiler
        // doesn't warn about the unused continuation parameter. Safe because
        // `contains_resume()` being false guarantees no Resume node exists in the arm
        // body, so `current_handler_k` ("<_>") is never read during lowering.
        let k_var = if arm.body.contains_resume() { self.fresh() } else { "_".to_string() };
        let param_vars: Vec<String> = (0..arm.params.len())
            .map(|i| format!("_HArg{}", i))
            .collect();

        let mut fun_params: Vec<String> = param_vars.clone();
        fun_params.push(k_var.clone());

        // Set up K for resume references in the body.
        // Clear current_return_k so the handler arm body doesn't leak the
        // function-level _ReturnK. The handler's result is the with-block
        // value, which flows to the rest of the block via rest_k, not through
        // the function's own return continuation.
        let prev_handler_k = self.current_handler_k.replace(k_var);
        let saved_return_k = self.current_return_k.take();
        let saved_pending_k = self.pending_callee_return_k.take();
        let mut body_ce = self.lower_expr(&arm.body);
        self.current_return_k = saved_return_k;
        self.pending_callee_return_k = saved_pending_k;

        // Bind arm's named params to the positional handler args
        for (i, (param_name, _)) in arm.params.iter().enumerate().rev() {
            body_ce = CExpr::Let(
                core_var(param_name),
                Box::new(CExpr::Var(param_vars[i].clone())),
                Box::new(body_ce),
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
                let info = self
                    .handler_defs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown handler: {}", name));
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

                for name in named {
                    let info = self
                        .handler_defs
                        .get(name)
                        .unwrap_or_else(|| panic!("unknown handler: {}", name));
                    all_arms.extend(info.arms.iter().cloned());
                    handled_effects.extend(info.effects.iter().cloned());
                    if resolved_return.is_none() {
                        resolved_return = info.return_clause.clone();
                    }
                }

                all_arms.extend(arms.iter().map(|a| a.node.clone()));

                // Determine effects from inline arms
                for arm in arms {
                    if let Some(eff) = self.op_to_effect.get(&arm.node.op_name)
                        && !handled_effects.contains(eff)
                    {
                        handled_effects.push(eff.clone());
                    }
                }

                (all_arms, resolved_return, handled_effects)
            }
        }
    }
}

