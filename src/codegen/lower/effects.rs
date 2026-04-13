/// Effect system lowering: CPS transform, handler building, BEAM-native ops.
///
/// This module handles:
/// - `lower_effect_call`: lowering `op! args` to handler application
/// - `lower_with`: lowering `expr with handler` blocks
/// - `build_op_handler_fun`: building per-op CPS handler functions
/// - `build_beam_native_op_fun`: synthesizing handlers for BEAM-native ops
/// - named/inline handler composition for `with` lowering
use std::collections::{HashMap, HashSet, VecDeque};

use crate::ast::{Expr, ExprKind, Handler, HandlerArm, HandlerItem, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::Lowerer;
use super::util::{cerl_call, collect_fun_call};

struct PendingLet {
    var: String,
    val: CExpr,
    deps: HashSet<String>,
}

#[derive(Clone)]
enum NamedHandlerItem {
    Static {
        canonical: String,
        info: super::HandlerInfo,
    },
    Conditional {
        cond_var: String,
        cond_ce: CExpr,
        then_info: super::HandlerInfo,
        else_info: super::HandlerInfo,
    },
    Dynamic {
        tuple_var: String,
        effects: Vec<String>,
        has_return: bool,
    },
}

#[derive(Clone)]
enum OpHandlerPlan {
    Inline {
        arm: HandlerArm,
    },
    Static {
        arm: HandlerArm,
        source_module: Option<String>,
        handler_canonical: String,
    },
    Conditional {
        cond_var: String,
        then_arm: Option<HandlerArm>,
        then_source: Option<String>,
        else_arm: Option<HandlerArm>,
        else_source: Option<String>,
    },
    Dynamic {
        element_expr: CExpr,
    },
    BeamNative {
        handler_canonical: String,
    },
    Passthrough,
}

enum WithHandlerLayer {
    Named {
        reference: crate::ast::NamedHandlerRef,
    },
    Inline {
        arms: Vec<HandlerArm>,
        return_clause: Option<Box<HandlerArm>>,
    },
}

impl<'a> Lowerer<'a> {
    fn compose_return_k(&mut self, inner: Option<CExpr>, outer: Option<CExpr>) -> Option<CExpr> {
        match (inner, outer) {
            (Some(inner), Some(outer)) => {
                let param = self.fresh();
                let inner_value = self.fresh();
                Some(CExpr::Fun(
                    vec![param.clone()],
                    Box::new(CExpr::Let(
                        inner_value.clone(),
                        Box::new(CExpr::Apply(Box::new(inner), vec![CExpr::Var(param)])),
                        Box::new(CExpr::Apply(Box::new(outer), vec![CExpr::Var(inner_value)])),
                    )),
                ))
            }
            (Some(k), None) | (None, Some(k)) => Some(k),
            (None, None) => None,
        }
    }

    fn lower_handler_owned_expr(&mut self, expr: &Expr) -> CExpr {
        // Handler-local computations produce the handled result itself, so they
        // must not inherit an enclosing function/handler return continuation.
        self.lower_expr_value(expr)
    }

    fn lower_handled_expr_with_return_k(&mut self, expr: &Expr, return_k: Option<CExpr>) -> CExpr {
        self.lower_expr_with_installed_return_k(expr, return_k)
    }

    fn lower_handled_inner_expr(
        &mut self,
        expr: &Expr,
        handled_return_k: Option<CExpr>,
        inherited_return_k: Option<CExpr>,
    ) -> CExpr {
        let return_k = self.compose_return_k(handled_return_k, inherited_return_k);
        let is_direct_effectful_call = collect_fun_call(expr)
            .map(|(name, _, _)| {
                self.is_effectful(name) || self.current_effectful_vars.contains_key(name)
            })
            .unwrap_or(false);

        if is_direct_effectful_call {
            self.lower_expr_with_call_return_k(expr, return_k)
        } else {
            self.lower_handled_expr_with_return_k(expr, return_k)
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

    fn build_return_lambda(&mut self, ret: &HandlerArm, source_module: Option<&str>) -> CExpr {
        let saved_source_module = self.current_handler_source_module.clone();
        let ctor_aliases = self.push_source_module_ctor_aliases(source_module);
        self.current_handler_source_module = source_module.map(str::to_string);
        let ret_body = self.lower_handler_owned_expr(&ret.body);
        self.current_handler_source_module = saved_source_module;
        let (param, body) = if ret.params.is_empty() {
            (self.fresh(), ret_body)
        } else {
            self.destructure_pat(&ret.params[0], ret_body)
        };
        self.pop_source_module_ctor_aliases(ctor_aliases);
        CExpr::Fun(vec![param], Box::new(body))
    }

    /// Lower an effect call: `op! args`.
    ///
    /// Emits: `apply _Handle_Effect_op(arg1, ..., argN, K)`
    ///
    /// If `continuation` is Some, it's the pre-built K closure. If None
    /// (standalone effect call not in a block), we use an identity continuation.
    pub(super) fn lower_effect_call(
        &mut self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
        args: &[Expr],
        continuation: Option<CExpr>,
    ) -> CExpr {
        // Resolve the effect name (canonical form).
        let effect_name = self
            .resolved_effect_call_name(node_id, op_name, qualifier)
            .unwrap_or_else(|| panic!("unknown effect operation: {}", op_name));
        let effect_key = format!("{}.{}", effect_name, op_name);

        // Lower args (shared between direct and CPS paths).
        let runtime_param_count = self
            .effect_defs
            .get(&effect_name)
            .and_then(|effect| effect.ops.get(op_name))
            .map(|op| op.runtime_param_count)
            .unwrap_or(args.len());
        let mut unit_args_to_erase = args.len().saturating_sub(runtime_param_count);
        let mut param_vars = Vec::new();
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
            // Effect call args are not CPS-expanded: BEAM-native ops (e.g.
            // spawn) wrap their callback as a value-shape thunk and can't
            // supply CPS handlers, and user-defined op handlers receive the
            // callback as a captured-handler closure too. So clear any
            // ambient lambda_effect_context here — it only applies to
            // ordinary (App) HOF parameters.
            let saved_ctx = self.lambda_effect_context.take();
            let ce = self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg));
            self.lambda_effect_context = saved_ctx;
            bindings.push((v.clone(), ce));
            param_vars.push(v);
        }

        // Direct path: ops that always resume exactly once can be inlined as
        // `let Result = <native call> in <continuation body>` — no closure allocation.
        if let Some(handler_canonical) = self.direct_ops.get(&effect_key).cloned() {
            let param_var_strs: Vec<String> = param_vars.clone();
            let native_call = if super::beam_interop::is_ref_op(op_name) {
                super::beam_interop::build_ref_native_call(
                    &handler_canonical,
                    op_name,
                    &param_var_strs,
                    &mut || self.fresh(),
                )
            } else if super::beam_interop::is_vec_op(op_name) {
                super::beam_interop::build_vec_native_call(op_name, &param_var_strs, &mut || {
                    self.fresh()
                })
            } else {
                let ctor_atoms = self.constructor_atoms.clone();
                super::beam_interop::build_native_call(
                    op_name,
                    &param_var_strs,
                    &ctor_atoms,
                    &mut || self.fresh(),
                )
            };

            // Unwrap the continuation closure to inline its body directly.
            // K is Fun([result_param], body) — we bind result_param via let.
            let result = if let Some(k) = continuation {
                match k {
                    CExpr::Fun(params, body) if params.len() == 1 => {
                        let result_var = params[0].clone();
                        CExpr::Let(result_var, Box::new(native_call), body)
                    }
                    // K is a variable reference (e.g. _ReturnK) — apply it
                    other => {
                        let result_var = self.fresh();
                        CExpr::Let(
                            result_var.clone(),
                            Box::new(native_call),
                            Box::new(CExpr::Apply(Box::new(other), vec![CExpr::Var(result_var)])),
                        )
                    }
                }
            } else {
                // No continuation — standalone effect call, just return the result
                native_call
            };

            return bindings.into_iter().rev().fold(result, |body, (var, val)| {
                CExpr::Let(var, Box::new(val), Box::new(body))
            });
        }

        // CPS path: apply Handler(arg1, ..., argN, K)
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

        let mut call_args: Vec<CExpr> = param_vars.into_iter().map(CExpr::Var).collect();

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
    fn build_beam_native_op_fun(&mut self, op_name: &str, handler_canonical: &str) -> CExpr {
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
        } else if super::beam_interop::is_vec_op(op_name) {
            super::beam_interop::build_vec_native_call(op_name, &param_vars, &mut || self.fresh())
        } else {
            let ctor_atoms = self.constructor_atoms.clone();
            super::beam_interop::build_native_call(op_name, &param_vars, &ctor_atoms, &mut || {
                self.fresh()
            })
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
        self.lower_with_inherited_return_k(expr, handler, None)
    }

    pub(super) fn lower_with_inherited_return_k(
        &mut self,
        expr: &Expr,
        handler: &Handler,
        inherited_return_k: Option<CExpr>,
    ) -> CExpr {
        let normalized = self.normalize_with_handler(handler);
        let (inline_arms, explicit_return_clause) = match &normalized {
            WithHandlerLayer::Named { .. } => (Vec::new(), None),
            WithHandlerLayer::Inline {
                arms,
                return_clause,
            } => (arms.clone(), return_clause.clone()),
        };

        let mut condition_bindings: Vec<(String, CExpr)> = Vec::new();
        let named_item = match &normalized {
            WithHandlerLayer::Named { reference } => {
                self.pre_register_local_with_binding(expr, &reference.name);
                let item = self.resolve_named_handler_item(reference);
                if let NamedHandlerItem::Conditional {
                    cond_var, cond_ce, ..
                } = &item
                {
                    condition_bindings.push((cond_var.clone(), cond_ce.clone()));
                }
                Some(item)
            }
            WithHandlerLayer::Inline { .. } => None,
        };

        let (handled_effects, inline_arms_by_op) = if let Some(item) = &named_item {
            (item.effects().to_vec(), HashMap::new())
        } else {
            let mut handled_effects = Vec::new();
            let mut inline_arms_by_op: HashMap<String, HandlerArm> = HashMap::new();
            for arm in &inline_arms {
                if let Some(effect) = self.effect_for_handler_arm(arm) {
                    if !handled_effects.contains(&effect) {
                        handled_effects.push(effect.clone());
                    }
                    if let Some(ref q) = arm.qualifier {
                        let canonical = self.canonicalize_effect(q);
                        inline_arms_by_op
                            .insert(format!("{}.{}", canonical, arm.op_name), arm.clone());
                    } else {
                        inline_arms_by_op.insert(arm.op_name.clone(), arm.clone());
                    }
                }
            }
            (handled_effects, inline_arms_by_op)
        };

        let handler_ops = self.effect_handler_ops(&handled_effects);

        // For each op, build a handler function and bind it.
        // Two passes: first register all param names (so handler arm bodies
        // can reference sibling handlers via closure capture),
        // then build the handler functions.
        let saved_handler_params = self.current_handler_params.clone();
        let saved_no_resume_ops = self.no_resume_ops.clone();
        let saved_direct_ops = self.direct_ops.clone();

        // Pass 1: register all handler param variables (one per op)
        let mut op_vars: Vec<(String, String, String, OpHandlerPlan)> = Vec::new();
        for (eff, op) in &handler_ops {
            let var_name = self.fresh_handler_binding_name(eff, op);
            let key = format!("{}.{}", eff, op);
            self.current_handler_params
                .insert(key.clone(), var_name.clone());
            let plan = match &named_item {
                Some(item) => self.plan_named_op_handler(eff, op, item),
                None => self.plan_inline_op_handler(eff, op, &inline_arms_by_op),
            };
            match &plan {
                OpHandlerPlan::Inline { arm } if !arm.body.contains_resume() => {
                    self.no_resume_ops.insert(key.clone());
                }
                OpHandlerPlan::BeamNative { handler_canonical } => {
                    if self.use_direct_native_fast_path(handler_canonical) {
                        self.direct_ops
                            .insert(key.clone(), handler_canonical.clone());
                    }
                }
                OpHandlerPlan::Static {
                    arm,
                    handler_canonical,
                    ..
                } => {
                    if !arm.body.contains_resume() {
                        self.no_resume_ops.insert(key.clone());
                    }
                    if self.is_beam_native_handler_canonical(handler_canonical)
                        && self.use_direct_native_fast_path(handler_canonical)
                    {
                        self.direct_ops
                            .insert(key.clone(), handler_canonical.clone());
                    }
                }
                _ => {}
            }
            op_vars.push((eff.clone(), op.clone(), var_name, plan));
        }

        // Lower the inner expression once handler params are in scope.
        let return_k_lambda = match (&explicit_return_clause, &named_item) {
            (Some(ret), _) => Some(self.build_return_lambda(ret, None)),
            (None, Some(item)) => self.named_return_lambda(item),
            (None, None) => None,
        };
        let result = self.lower_handled_inner_expr(expr, return_k_lambda, inherited_return_k);

        // Pass 2: build ALL handler functions unconditionally.
        // We'll prune unreachable ones after lowering the body.
        // BEAM-native ops are emitted first since they're self-contained
        // (direct BEAM calls, no closures). CPS handlers may reference them
        // (e.g. async_handler's body calls spawn!/send!), so they must come after.
        let mut handler_bindings: Vec<(String, CExpr)> = Vec::new();
        for (_eff, op, var_name, plan) in &op_vars {
            let binding = match plan {
                OpHandlerPlan::Inline { arm } => self.build_op_handler_fun(arm, None),
                OpHandlerPlan::Static {
                    handler_canonical, ..
                } if self.is_beam_native_handler_canonical(handler_canonical) => {
                    self.build_beam_native_op_fun(op, handler_canonical)
                }
                OpHandlerPlan::Static {
                    arm, source_module, ..
                } => self.build_op_handler_fun(arm, source_module.as_deref()),
                OpHandlerPlan::Conditional {
                    cond_var,
                    then_arm,
                    then_source,
                    else_arm,
                    else_source,
                } => self.build_conditional_handler_fun(
                    cond_var,
                    then_arm.as_ref(),
                    then_source.as_deref(),
                    else_arm.as_ref(),
                    else_source.as_deref(),
                ),
                OpHandlerPlan::Dynamic { element_expr } => element_expr.clone(),
                OpHandlerPlan::BeamNative { handler_canonical } => {
                    self.build_beam_native_op_fun(op, handler_canonical)
                }
                OpHandlerPlan::Passthrough => self.build_passthrough_handler_fun(),
            };
            handler_bindings.push((var_name.clone(), binding));
        }

        self.current_handler_params = saved_handler_params;
        self.no_resume_ops = saved_no_resume_ops;
        self.direct_ops = saved_direct_ops;
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

        self.attach_scoped_handler_bindings(result, condition_bindings, handler_bindings)
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
    fn build_op_handler_fun(&mut self, arm: &HandlerArm, source_module: Option<&str>) -> CExpr {
        let has_resume = arm.body.contains_resume();
        let op_info = self
            .effect_for_handler_arm(arm)
            .and_then(|effect_name| {
                self.effect_defs
                    .get(&effect_name)
                    .and_then(|info| info.ops.get(&arm.op_name))
            })
            .cloned();
        let source_param_count = op_info
            .as_ref()
            .map(|op| op.source_param_count)
            .unwrap_or(arm.params.len());
        let runtime_param_positions = op_info
            .as_ref()
            .map(|op| op.runtime_param_positions.clone())
            .unwrap_or_else(|| (0..source_param_count).collect());
        let runtime_param_count = op_info
            .as_ref()
            .map(|op| op.runtime_param_count)
            .unwrap_or(source_param_count);

        // If resume is never called, use `_` (Core Erlang wildcard) so the compiler
        // doesn't warn about the unused continuation parameter. Safe because
        // `contains_resume()` being false guarantees no Resume node exists in the arm
        // body, so `current_handler_k` ("<_>") is never read during lowering.
        let k_var = if has_resume {
            self.fresh()
        } else {
            "_".to_string()
        };
        let param_vars: Vec<String> = (0..runtime_param_count)
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
        let saved_source_module = self.current_handler_source_module.clone();
        let ctor_aliases = self.push_source_module_ctor_aliases(source_module);
        self.current_handler_source_module = source_module.map(str::to_string);
        if let Some(ref fb) = arm.finally_block {
            self.current_handler_finally = Some(fb.as_ref().clone());
        }

        let saved_effectful_vars = self.current_effectful_vars.clone();
        if let Some(effect_name) = self.effect_for_handler_arm(arm)
            && let Some(param_effs) = self
                .op_param_absorbed_effects(&effect_name, &arm.op_name)
                .cloned()
        {
            for (idx, effs) in &param_effs {
                if let Some(Pat::Var { name, .. }) = arm.params.get(*idx) {
                    self.current_effectful_vars
                        .insert(name.clone(), effs.clone());
                }
            }
        }
        let mut body_ce = self.lower_handler_owned_expr(&arm.body);

        self.current_handler_finally = saved_finally;
        self.current_handler_source_module = saved_source_module;
        self.current_effectful_vars = saved_effectful_vars;

        // Bind arm's params (possibly patterns) to the positional handler args
        for (i, pat) in arm.params.iter().enumerate().rev() {
            let bound_value = runtime_param_positions
                .iter()
                .position(|&source_idx| source_idx == i)
                .map(|runtime_idx| CExpr::Var(param_vars[runtime_idx].clone()))
                .unwrap_or_else(|| CExpr::Lit(CLit::Atom("unit".to_string())));
            let (var, wrapped_body) = self.destructure_pat(pat, body_ce);
            body_ce = CExpr::Let(var, Box::new(bound_value), Box::new(wrapped_body));
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

        self.pop_source_module_ctor_aliases(ctor_aliases);
        self.current_handler_k = prev_handler_k;
        CExpr::Fun(fun_params, Box::new(body_ce))
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
                tuple_elements.push(self.build_op_handler_fun(arm, None));
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
                tuple_elements.push(self.build_op_handler_fun(arm, info.source_module.as_deref()));
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

    fn normalize_with_handler(&self, handler: &Handler) -> WithHandlerLayer {
        match handler {
            Handler::Named(named) => WithHandlerLayer::Named {
                reference: named.clone(),
            },
            Handler::Inline { items, .. } => {
                let mut inline_arms = Vec::new();
                let mut return_clause = None;
                for ann in items {
                    match &ann.node {
                        HandlerItem::Named(_) => panic!(
                            "internal lowering error: named handler refs should have been desugared into nested `with` layers before lowering"
                        ),
                        HandlerItem::Arm(a) => inline_arms.push(a.clone()),
                        HandlerItem::Return(rc) => {
                            assert!(
                                return_clause.is_none(),
                                "internal lowering error: inline handler segment has multiple return clauses"
                            );
                            return_clause = Some(Box::new(rc.clone()));
                        }
                    }
                }
                WithHandlerLayer::Inline {
                    arms: inline_arms,
                    return_clause,
                }
            }
        }
    }

    fn pre_register_local_with_binding(&mut self, expr: &Expr, named_ref: &str) {
        let mut current = expr;
        let stmts = loop {
            match &current.kind {
                ExprKind::Block { stmts, .. } => break stmts,
                ExprKind::With { expr: inner, .. } => current = inner,
                _ => return,
            }
        };

        for stmt in stmts {
            if let Stmt::Let { pattern, value, .. } = &stmt.node
                && let Pat::Var { name, .. } = pattern
                && name == named_ref
                && self.is_handler_value(value)
            {
                self.lower_handle_binding(name, value);
            }
        }
    }

    fn resolve_named_handler_item(
        &self,
        reference: &crate::ast::NamedHandlerRef,
    ) -> NamedHandlerItem {
        let name = &reference.name;
        if let Some((tuple_var, effects, has_return)) = self.handle_dynamic_vars.get(name).cloned()
        {
            return NamedHandlerItem::Dynamic {
                tuple_var,
                effects,
                has_return,
            };
        }
        if let Some((cond_var, cond_ce, then_canonical, else_canonical)) =
            self.handle_cond_vars.get(name).cloned()
        {
            let then_info = self
                .handler_defs
                .get(&then_canonical)
                .cloned()
                .unwrap_or_else(|| {
                    panic!(
                        "internal lowering error: unknown conditional handler branch '{}' for '{}'",
                        then_canonical, name
                    )
                });
            let else_info = self
                .handler_defs
                .get(&else_canonical)
                .cloned()
                .unwrap_or_else(|| {
                    panic!(
                        "internal lowering error: unknown conditional handler branch '{}' for '{}'",
                        else_canonical, name
                    )
                });
            return NamedHandlerItem::Conditional {
                cond_var,
                cond_ce,
                then_info,
                else_info,
            };
        }
        let canonical = self.resolved_handler_binding_name(reference.id, name);
        let info = self
            .handler_defs
            .get(&canonical)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "internal lowering error: unknown handler item '{}' (canonical: {})",
                    name, canonical
                )
            });
        NamedHandlerItem::Static { canonical, info }
    }

    fn effect_for_handler_arm(&self, arm: &HandlerArm) -> Option<String> {
        if let Some(resolved) = self
            .current_front_resolution()
            .and_then(|r| r.handler_arm_qualifier(arm.id))
        {
            Some(resolved.to_string())
        } else if let Some(ref q) = arm.qualifier {
            Some(self.canonicalize_effect(q))
        } else {
            self.op_to_effect.get(&arm.op_name).cloned()
        }
    }

    fn static_arm_for_effect_op(
        &self,
        info: &super::HandlerInfo,
        eff: &str,
        op: &str,
    ) -> Option<(HandlerArm, Option<String>)> {
        info.arms
            .iter()
            .find(|arm| {
                if let Some(resolved) = self
                    .current_front_resolution()
                    .and_then(|r| r.handler_arm_qualifier(arm.id))
                {
                    resolved == eff && arm.op_name == op
                } else if let Some(ref q) = arm.qualifier {
                    self.canonicalize_effect(q) == eff && arm.op_name == op
                } else {
                    arm.op_name == op
                }
            })
            .cloned()
            .map(|arm| (arm, info.source_module.clone()))
    }

    fn dynamic_tuple_element_expr(
        &self,
        tuple_var: &str,
        effects: &[String],
        eff: &str,
        op: &str,
    ) -> CExpr {
        let handler_ops = self.effect_handler_ops(effects);
        let index = handler_ops
            .iter()
            .position(|(item_eff, item_op)| item_eff == eff && item_op == op)
            .unwrap_or_else(|| {
                panic!(
                    "internal lowering error: dynamic handler tuple '{}' is missing op '{}.{}'",
                    tuple_var, eff, op
                )
            });
        cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(index as i64 + 1)),
                CExpr::Var(tuple_var.to_string()),
            ],
        )
    }

    fn plan_named_op_handler(
        &self,
        eff: &str,
        op: &str,
        named_item: &NamedHandlerItem,
    ) -> OpHandlerPlan {
        match named_item {
            NamedHandlerItem::Static { canonical, info } => {
                if let Some((arm, source_module)) = self.static_arm_for_effect_op(info, eff, op) {
                    OpHandlerPlan::Static {
                        arm,
                        source_module,
                        handler_canonical: canonical.clone(),
                    }
                } else if self.is_beam_native_handler_canonical(canonical) {
                    OpHandlerPlan::BeamNative {
                        handler_canonical: canonical.clone(),
                    }
                } else {
                    OpHandlerPlan::Passthrough
                }
            }
            NamedHandlerItem::Conditional {
                cond_var,
                then_info,
                else_info,
                ..
            } => {
                let then_arm = self
                    .static_arm_for_effect_op(then_info, eff, op)
                    .map(|(arm, _)| arm);
                let then_source = then_info.source_module.clone();
                let else_arm = self
                    .static_arm_for_effect_op(else_info, eff, op)
                    .map(|(arm, _)| arm);
                let else_source = else_info.source_module.clone();
                OpHandlerPlan::Conditional {
                    cond_var: cond_var.clone(),
                    then_arm,
                    then_source,
                    else_arm,
                    else_source,
                }
            }
            NamedHandlerItem::Dynamic {
                tuple_var, effects, ..
            } => OpHandlerPlan::Dynamic {
                element_expr: self.dynamic_tuple_element_expr(tuple_var, effects, eff, op),
            },
        }
    }

    fn plan_inline_op_handler(
        &self,
        eff: &str,
        op: &str,
        inline_arms_by_op: &HashMap<String, HandlerArm>,
    ) -> OpHandlerPlan {
        let qualified_key = format!("{}.{}", eff, op);
        if let Some(arm) = inline_arms_by_op
            .get(&qualified_key)
            .or_else(|| inline_arms_by_op.get(op))
        {
            return OpHandlerPlan::Inline { arm: arm.clone() };
        }
        OpHandlerPlan::Passthrough
    }

    fn build_passthrough_handler_fun(&mut self) -> CExpr {
        let k_param = self.fresh();
        CExpr::Fun(
            vec![k_param.clone()],
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(k_param)),
                vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
            )),
        )
    }

    fn build_conditional_handler_fun(
        &mut self,
        cond_var: &str,
        then_arm: Option<&HandlerArm>,
        then_source: Option<&str>,
        else_arm: Option<&HandlerArm>,
        else_source: Option<&str>,
    ) -> CExpr {
        let then_fun = if let Some(arm) = then_arm {
            self.build_op_handler_fun(arm, then_source)
        } else {
            self.build_passthrough_handler_fun()
        };
        let else_fun = if let Some(arm) = else_arm {
            self.build_op_handler_fun(arm, else_source)
        } else {
            self.build_passthrough_handler_fun()
        };
        let arity = match then_arm.or(else_arm) {
            Some(arm) => arm.params.len() + 1,
            None => 1,
        };
        let wrapper_params: Vec<String> = (0..arity).map(|i| format!("_HW{}", i)).collect();
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
        CExpr::Fun(wrapper_params, Box::new(case_expr))
    }

    fn identity_return_lambda(&mut self) -> CExpr {
        let param = self.fresh();
        CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)))
    }

    fn collect_top_level_scoped_vars(expr: &CExpr, out: &mut HashSet<String>) {
        match expr {
            CExpr::Let(var, _, body) => {
                out.insert(var.clone());
                Self::collect_top_level_scoped_vars(body, out);
            }
            CExpr::LetRec(_, body) => Self::collect_top_level_scoped_vars(body, out),
            CExpr::Annotated { expr, .. } => Self::collect_top_level_scoped_vars(expr, out),
            _ => {}
        }
    }

    fn collect_var_refs(expr: &CExpr, out: &mut HashSet<String>) {
        let mut bound = HashSet::new();
        Self::collect_free_var_refs(expr, &mut bound, out);
    }

    /// Scope-aware free-variable collector. Tracks which names are locally
    /// bound by `Let`/`Fun`/`LetRec`/`Case` patterns and only records vars
    /// that escape those bindings. Without this, naive walking treats inner
    /// shadowing names (e.g. a handler lambda that rebinds `Conn = _HArg0`)
    /// as references to the outer name, producing spurious dependencies.
    fn collect_free_var_refs(expr: &CExpr, bound: &mut HashSet<String>, out: &mut HashSet<String>) {
        match expr {
            CExpr::Var(v) => {
                if !bound.contains(v) {
                    out.insert(v.clone());
                }
            }
            CExpr::Lit(_) | CExpr::Nil | CExpr::FunRef(_, _) => {}
            CExpr::Fun(params, body) => {
                let added: Vec<String> = params
                    .iter()
                    .filter(|p| bound.insert((*p).clone()))
                    .cloned()
                    .collect();
                Self::collect_free_var_refs(body, bound, out);
                for p in &added {
                    bound.remove(p);
                }
            }
            CExpr::Let(var, val, body) => {
                Self::collect_free_var_refs(val, bound, out);
                let added = bound.insert(var.clone());
                Self::collect_free_var_refs(body, bound, out);
                if added {
                    bound.remove(var);
                }
            }
            CExpr::Apply(func, args) => {
                Self::collect_free_var_refs(func, bound, out);
                for arg in args {
                    Self::collect_free_var_refs(arg, bound, out);
                }
            }
            CExpr::Call(_, _, args) | CExpr::Tuple(args) | CExpr::Values(args) => {
                for arg in args {
                    Self::collect_free_var_refs(arg, bound, out);
                }
            }
            CExpr::Case(scrutinee, arms) => {
                Self::collect_free_var_refs(scrutinee, bound, out);
                for arm in arms {
                    let mut pat_vars = Vec::new();
                    Self::collect_pat_vars(&arm.pat, &mut pat_vars);
                    let added: Vec<String> = pat_vars
                        .into_iter()
                        .filter(|v| bound.insert(v.clone()))
                        .collect();
                    if let Some(guard) = &arm.guard {
                        Self::collect_free_var_refs(guard, bound, out);
                    }
                    Self::collect_free_var_refs(&arm.body, bound, out);
                    for v in &added {
                        bound.remove(v);
                    }
                }
            }
            CExpr::Cons(head, tail) => {
                Self::collect_free_var_refs(head, bound, out);
                Self::collect_free_var_refs(tail, bound, out);
            }
            CExpr::LetRec(defs, body) => {
                // letrec: all defined names are in scope inside every def and the body
                let added: Vec<String> = defs
                    .iter()
                    .filter_map(|(name, _, _)| {
                        if bound.insert(name.clone()) {
                            Some(name.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                for (_, _, def) in defs {
                    Self::collect_free_var_refs(def, bound, out);
                }
                Self::collect_free_var_refs(body, bound, out);
                for v in &added {
                    bound.remove(v);
                }
            }
            CExpr::Receive(arms, timeout, timeout_body) => {
                for arm in arms {
                    let mut pat_vars = Vec::new();
                    Self::collect_pat_vars(&arm.pat, &mut pat_vars);
                    let added: Vec<String> = pat_vars
                        .into_iter()
                        .filter(|v| bound.insert(v.clone()))
                        .collect();
                    if let Some(guard) = &arm.guard {
                        Self::collect_free_var_refs(guard, bound, out);
                    }
                    Self::collect_free_var_refs(&arm.body, bound, out);
                    for v in &added {
                        bound.remove(v);
                    }
                }
                Self::collect_free_var_refs(timeout, bound, out);
                Self::collect_free_var_refs(timeout_body, bound, out);
            }
            CExpr::Try {
                expr,
                ok_var,
                ok_body,
                catch_vars,
                catch_body,
            } => {
                Self::collect_free_var_refs(expr, bound, out);
                let ok_added = bound.insert(ok_var.clone());
                Self::collect_free_var_refs(ok_body, bound, out);
                if ok_added {
                    bound.remove(ok_var);
                }
                let catch_added: Vec<String> = [&catch_vars.0, &catch_vars.1, &catch_vars.2]
                    .iter()
                    .filter_map(|v| {
                        if bound.insert((*v).clone()) {
                            Some((*v).clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                Self::collect_free_var_refs(catch_body, bound, out);
                for v in &catch_added {
                    bound.remove(v);
                }
            }
            CExpr::Binary(segs) => {
                for seg in segs {
                    match seg {
                        crate::codegen::cerl::CBinSeg::BinaryAll(expr) => {
                            Self::collect_free_var_refs(expr, bound, out);
                        }
                        crate::codegen::cerl::CBinSeg::Segment { value, size, .. } => {
                            Self::collect_free_var_refs(value, bound, out);
                            if let crate::codegen::cerl::BinSegSize::Expr(size_expr) = size {
                                Self::collect_free_var_refs(size_expr, bound, out);
                            }
                        }
                        crate::codegen::cerl::CBinSeg::Byte(_) => {}
                    }
                }
            }
            CExpr::Annotated { expr, .. } => Self::collect_free_var_refs(expr, bound, out),
        }
    }

    fn collect_pat_vars(pat: &CPat, out: &mut Vec<String>) {
        match pat {
            CPat::Var(v) => out.push(v.clone()),
            CPat::Lit(_) | CPat::Wildcard | CPat::Nil => {}
            CPat::Tuple(ps) | CPat::Values(ps) => {
                for p in ps {
                    Self::collect_pat_vars(p, out);
                }
            }
            CPat::Cons(head, tail) => {
                Self::collect_pat_vars(head, out);
                Self::collect_pat_vars(tail, out);
            }
            CPat::Alias(name, inner) => {
                out.push(name.clone());
                Self::collect_pat_vars(inner, out);
            }
            CPat::Binary(segs) => {
                for seg in segs {
                    match seg {
                        crate::codegen::cerl::CBinSeg::BinaryAll(p) => {
                            Self::collect_pat_vars(p, out);
                        }
                        crate::codegen::cerl::CBinSeg::Segment { value, size, .. } => {
                            Self::collect_pat_vars(value, out);
                            if let crate::codegen::cerl::BinSegSize::Expr(_) = size {
                                // size expr is not a binding site
                            }
                        }
                        crate::codegen::cerl::CBinSeg::Byte(_) => {}
                    }
                }
            }
        }
    }

    fn wrap_ready_pending_lets(
        mut body: CExpr,
        pending: &mut VecDeque<PendingLet>,
        bound: &mut HashSet<String>,
    ) -> CExpr {
        let bound_snapshot = bound.clone();
        let mut ready = Vec::new();
        let mut waiting = VecDeque::new();

        while let Some(item) = pending.pop_front() {
            if item.deps.is_subset(&bound_snapshot) {
                ready.push(item);
            } else {
                waiting.push_back(item);
            }
        }

        *pending = waiting;

        for item in ready.into_iter().rev() {
            body = CExpr::Let(item.var, Box::new(item.val), Box::new(body));
        }

        body
    }

    fn place_pending_lets(
        body: CExpr,
        pending: &mut VecDeque<PendingLet>,
        bound: &mut HashSet<String>,
    ) -> CExpr {
        let body = Self::wrap_ready_pending_lets(body, pending, bound);
        match body {
            CExpr::Let(var, val, inner) => {
                bound.insert(var.clone());
                let inner = Self::place_pending_lets(*inner, pending, bound);
                CExpr::Let(var, val, Box::new(inner))
            }
            CExpr::LetRec(defs, body) => {
                let body = Self::place_pending_lets(*body, pending, bound);
                CExpr::LetRec(defs, Box::new(body))
            }
            CExpr::Annotated { expr, line, file } => CExpr::Annotated {
                expr: Box::new(Self::place_pending_lets(*expr, pending, bound)),
                line,
                file,
            },
            other => Self::wrap_ready_pending_lets(other, pending, bound),
        }
    }

    fn attach_scoped_handler_bindings(
        &self,
        result: CExpr,
        condition_bindings: Vec<(String, CExpr)>,
        handler_bindings: Vec<(String, CExpr)>,
    ) -> CExpr {
        let mut relevant_names = HashSet::new();
        Self::collect_top_level_scoped_vars(&result, &mut relevant_names);
        for (var, _) in &condition_bindings {
            relevant_names.insert(var.clone());
        }
        for (var, _) in &handler_bindings {
            relevant_names.insert(var.clone());
        }

        let mut pending: VecDeque<PendingLet> = condition_bindings
            .into_iter()
            .chain(handler_bindings)
            .map(|(var, val)| {
                let mut refs = HashSet::new();
                Self::collect_var_refs(&val, &mut refs);
                let deps = refs
                    .into_iter()
                    .filter(|name| name != &var && relevant_names.contains(name))
                    .collect();
                PendingLet { var, val, deps }
            })
            .collect();

        let mut bound = HashSet::new();
        let output = Self::place_pending_lets(result, &mut pending, &mut bound);
        if pending.is_empty() {
            output
        } else {
            let waiting_on: Vec<String> = pending
                .iter()
                .map(|item| format!("{} -> {:?}", item.var, item.deps))
                .collect();
            panic!(
                "internal lowering error: could not place scoped handler bindings: {}",
                waiting_on.join(", ")
            );
        }
    }

    fn named_return_lambda(&mut self, item: &NamedHandlerItem) -> Option<CExpr> {
        match item {
            NamedHandlerItem::Static { info, .. } => info
                .return_clause
                .as_ref()
                .map(|ret| self.build_return_lambda(ret, info.source_module.as_deref())),
            NamedHandlerItem::Conditional {
                cond_var,
                then_info,
                else_info,
                ..
            } => {
                if then_info.return_clause.is_some() || else_info.return_clause.is_some() {
                    let then_fun = then_info
                        .return_clause
                        .as_ref()
                        .map(|ret| {
                            self.build_return_lambda(ret, then_info.source_module.as_deref())
                        })
                        .unwrap_or_else(|| self.identity_return_lambda());
                    let else_fun = else_info
                        .return_clause
                        .as_ref()
                        .map(|ret| {
                            self.build_return_lambda(ret, else_info.source_module.as_deref())
                        })
                        .unwrap_or_else(|| self.identity_return_lambda());
                    let param = self.fresh();
                    let then_call =
                        CExpr::Apply(Box::new(then_fun), vec![CExpr::Var(param.clone())]);
                    let else_call =
                        CExpr::Apply(Box::new(else_fun), vec![CExpr::Var(param.clone())]);
                    let body = CExpr::Case(
                        Box::new(CExpr::Var(cond_var.clone())),
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
                    Some(CExpr::Fun(vec![param], Box::new(body)))
                } else {
                    None
                }
            }
            NamedHandlerItem::Dynamic {
                tuple_var,
                effects,
                has_return,
            } => {
                if *has_return {
                    Some(
                        self.dynamic_return_lambda(
                            tuple_var,
                            self.effect_handler_ops(effects).len(),
                        ),
                    )
                } else {
                    None
                }
            }
        }
    }

    fn is_beam_native_handler_canonical(&self, canonical: &str) -> bool {
        self.handler_defs
            .get(canonical)
            .and_then(|info| info.source_module.as_deref())
            .is_some_and(|module| super::beam_interop::is_beam_native_handler(module, canonical))
    }

    fn use_direct_native_fast_path(&self, canonical: &str) -> bool {
        let _ = canonical;
        false
    }
}

impl NamedHandlerItem {
    fn effects(&self) -> &[String] {
        match self {
            NamedHandlerItem::Static { info, .. } => &info.effects,
            NamedHandlerItem::Conditional { then_info, .. } => &then_info.effects,
            NamedHandlerItem::Dynamic { effects, .. } => effects,
        }
    }
}
