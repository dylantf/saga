use super::*;
use crate::ast::{Expr, ExprKind};
use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::lower::*;
use crate::codegen::runtime_shape::CpsShape;

impl<'a> Lowerer<'a> {
    /// Lower an effect call: `op! args`.
    ///
    /// Emits: `apply _Handle_Effect_op(arg1, ..., argN, K)`
    ///
    /// If `continuation` is Some, it's the pre-built K closure. If None
    /// (standalone effect call not in a block), we use an identity continuation.
    pub(crate) fn lower_effect_call(
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
        let op_info = self
            .effect_defs
            .get(&effect_name)
            .and_then(|effect| effect.ops.get(op_name));
        let runtime_param_count = op_info
            .map(|op| op.runtime_param_count)
            .unwrap_or(args.len());
        let runtime_param_positions = op_info
            .map(|op| op.runtime_param_positions.clone())
            .unwrap_or_else(|| (0..args.len()).collect());
        let op_param_absorbed = op_info.and_then(|op| {
            if op.param_absorbed_effects.is_empty() {
                None
            } else {
                Some(op.param_absorbed_effects.clone())
            }
        });
        let op_param_open_rows = op_info
            .map(|op| op.param_open_rows.clone())
            .unwrap_or_default();
        // Trailing dictionary args appended by the elaborator for the op's own
        // `where` constraints are real runtime values (never `Unit` placeholders),
        // so they must not be counted toward unit-arg erasure.
        let dict_param_count = op_info.map(|op| op.dict_param_names.len()).unwrap_or(0);
        let mut unit_args_to_erase = args
            .len()
            .saturating_sub(runtime_param_count + dict_param_count);
        let mut param_vars = Vec::new();
        let mut bindings = Vec::new();
        // An argument that performs effects when evaluated (e.g. `add! (make_frag
        // ())`, or one nested deeper like `add! (combine [make_frag ()])`) cannot
        // be lowered as a plain value: a CPS-compiled function delivers its result
        // through its own `_ReturnK`, not as the value of `apply`. Lowering it with
        // an identity continuation would feed the *handler's* yielded value into
        // the op call instead of the argument's actual value. Defer each such arg
        // and sequence it through the op call's continuation below, mirroring the
        // statement-position path that already handles arbitrary nesting.
        //
        // `branch_is_effectful` is depth-aware (it descends through constructor
        // calls, records, tuples, etc.) but does NOT flag lambda bodies, so
        // callback arguments stay on the normal value path.
        let mut effectful_chain: Vec<(String, &Expr)> = Vec::new();
        for (source_idx, arg) in args.iter().enumerate() {
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
            if self.branch_is_effectful(arg) {
                // Real runtime param, but its value is produced by sequencing the
                // argument through a continuation rather than a let-binding here.
                param_vars.push(v.clone());
                effectful_chain.push((v, arg));
                continue;
            }
            // Effect call args are generally not CPS-expanded — the handler
            // arm receives the callback as a plain value. However, if the op's
            // parameter declares absorbed effects, the lambda always gets its
            // own evidence/continuation params: the handler arm invokes it via
            // lower_effectful_var_call with the evidence the *handler* chooses
            // (it may install its own handler around the call, e.g. a nested
            // `with`), so capturing the caller's in-scope evidence would both
            // mismatch the arm's CPS calling convention and pin the callback
            // to the wrong handler. BEAM-native effects (e.g. spawn's Actor)
            // are the exception below: their context comes from direct erlang
            // calls, not handler params.
            let saved_ctx = self.lambda_effect_context.take();
            let saved_captured_evidence = self.lambda_captured_evidence.take();
            let saved_direct_ops = self.direct_ops.clone();
            let absorbed_effects = op_param_absorbed
                .as_ref()
                .and_then(|pae| pae.get(&source_idx));
            let has_open_row = op_param_open_rows.contains(&source_idx);
            if absorbed_effects.is_some() || has_open_row {
                let actual_callback_effects = self
                    .semantic_type_at_node(arg.id)
                    .and_then(|ty| self.cps_function_shape_from_type(ty))
                    .map(|shape| shape.static_effects)
                    .unwrap_or_default();
                let mut uncapturable: Vec<String> = Vec::new();
                let mut uses_native_callback_context = false;
                for eff in absorbed_effects.into_iter().flatten() {
                    let ops = self.effect_handler_ops(std::slice::from_ref(eff));
                    if ops.is_empty() {
                        continue;
                    }
                    // The op being called declares this effect as absorbed on
                    // its parameter -- meaning the handler invokes the lambda
                    // in a context where the effect is in scope. For BEAM-native
                    // handlers (e.g. spawn installing Actor in the new process),
                    // that context is satisfied by direct erlang calls, not an
                    // explicit handler param. Mark the ops as `direct_ops` so any
                    // use in the lambda body lowers natively.
                    if let Some(handler_canonical) = self.beam_native_handler_for_effect(eff) {
                        uses_native_callback_context = true;
                        for (e, op) in &ops {
                            self.direct_ops
                                .insert(format!("{}.{}", e, op), handler_canonical.clone());
                        }
                        continue;
                    }
                    let concrete = if actual_callback_effects.contains(eff) {
                        eff.clone()
                    } else {
                        let family = crate::typechecker::applied_effect_family(eff);
                        let matches = actual_callback_effects
                            .iter()
                            .filter(|actual| {
                                crate::typechecker::applied_effect_family(actual) == family
                            })
                            .collect::<Vec<_>>();
                        if matches.len() == 1 {
                            matches[0].to_string()
                        } else {
                            eff.clone()
                        }
                    };
                    uncapturable.push(concrete);
                }
                uncapturable.sort();
                uncapturable.dedup();
                let cps_open_row = has_open_row && !uses_native_callback_context;
                if !uncapturable.is_empty() || cps_open_row {
                    self.lambda_effect_context = Some(CpsShape {
                        static_effects: uncapturable,
                        is_open_row: cps_open_row,
                    });
                    if cps_open_row {
                        // Named callback effects are supplied by the handler
                        // at invocation time. Capture the perform-site frame
                        // only as a source for the callback's `..r` entries;
                        // lambda lowering overlays the call-time static frame
                        // and removes exact duplicates.
                        self.lambda_captured_evidence = self.current_evidence.clone();
                    }
                }
            }
            let ce = self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg));
            self.lambda_effect_context = saved_ctx;
            self.lambda_captured_evidence = saved_captured_evidence;
            self.direct_ops = saved_direct_ops;
            bindings.push((v.clone(), ce));
            param_vars.push(v);
        }

        let mut result = match self.effect_op_lowering_plan(&effect_key, &effect_name) {
            EffectOpLoweringPlan::DirectNative { handler_canonical } => {
                // Direct path: ops that always resume exactly once can be
                // inlined as `let Result = <native call> in <continuation
                // body>` — no closure allocation.
                self.push_effect_op_trace(
                    node_id,
                    &effect_name,
                    op_name,
                    args.len(),
                    param_vars.len(),
                    format!("direct-native(handler={handler_canonical})"),
                );
                let param_var_strs: Vec<String> = param_vars.clone();
                let native_call = if crate::codegen::lower::beam_interop::is_ref_op(op_name) {
                    crate::codegen::lower::beam_interop::build_ref_native_call(
                        &handler_canonical,
                        op_name,
                        &param_var_strs,
                        &mut || self.fresh(),
                    )
                } else if crate::codegen::lower::beam_interop::is_vec_op(op_name) {
                    crate::codegen::lower::beam_interop::build_vec_native_call(
                        op_name,
                        &param_var_strs,
                        &mut || self.fresh(),
                    )
                } else {
                    let ctor_atoms = self.constructor_atoms.clone();
                    crate::codegen::lower::beam_interop::build_native_call(
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
                                Box::new(CExpr::Apply(
                                    Box::new(other),
                                    vec![CExpr::Var(result_var)],
                                )),
                            )
                        }
                    }
                } else {
                    // No continuation — standalone effect call, just return the result
                    native_call
                };

                bindings.into_iter().rev().fold(result, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
            EffectOpLoweringPlan::DirectStaticTailResume { plan } => {
                self.push_effect_op_trace(
                    node_id,
                    &effect_name,
                    op_name,
                    args.len(),
                    param_vars.len(),
                    "direct-static-tail-resume".to_string(),
                );
                let result = self
                    .lower_static_tail_resume_op(
                        plan,
                        &param_vars,
                        &runtime_param_positions,
                        continuation,
                    )
                    .unwrap_or_else(|| {
                        panic!(
                            "internal optimizer error: static tail-resume proof for '{}.{}' was not lowerable",
                            effect_name, op_name
                        )
                    });
                bindings.into_iter().rev().fold(result, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
            EffectOpLoweringPlan::EvidenceLookup { trace_shape } => {
                // CPS path: read the per-op closure out of the evidence vector
                // and apply it.
                self.push_effect_op_trace(
                    node_id,
                    &effect_name,
                    op_name,
                    args.len(),
                    param_vars.len(),
                    trace_shape,
                );
                let applied_effect = self
                    .check_result
                    .effect_at_node
                    .get(&node_id)
                    .map(crate::typechecker::applied_effect_key)
                    .unwrap_or_else(|| effect_name.clone());
                let applied_effect = self.canonicalize_effect(&applied_effect);
                let handler_expr = self.evidence_op_lookup(&applied_effect, op_name);

                let mut call_args: Vec<CExpr> = param_vars.into_iter().map(CExpr::Var).collect();

                // Append continuation. If the handler arm never calls resume,
                // pass a cheap atom instead of a real closure so Erlang doesn't
                // warn about a constructed-but-unused term.
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

                let apply = CExpr::Apply(Box::new(handler_expr), call_args);

                // Wrap with let-bindings for args
                bindings.into_iter().rev().fold(apply, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
        };

        // Sequence deferred effectful arguments. Rightmost first so the outermost
        // wrapper is the leftmost arg, preserving left-to-right evaluation: `arg0`
        // resolves and binds its var, then `arg1`, then the op call runs. Each arg
        // is threaded to a continuation that binds its result var (referenced by
        // the op call in `param_vars`) and proceeds with `result`.
        // `lower_terminal_effectful_expr_to_k` dispatches on the argument's shape:
        // a bare effectful call, an effectful call nested inside a constructor /
        // record / tuple, or (degenerately) a pure value.
        for (v, arg) in effectful_chain.into_iter().rev() {
            let k_fun = CExpr::Fun(vec![v], Box::new(result));
            let k_var = self.fresh();
            let threaded = self.lower_terminal_effectful_expr_to_k(arg, &k_var);
            result = CExpr::Let(k_var, Box::new(k_fun), Box::new(threaded));
        }
        result
    }

    /// Build a per-op handler function for a single BEAM-native operation.
    /// Synthesizes: `fun (Arg0, ..., ArgN, K) -> let R = <native call> in K(R)`
    ///
    /// `handler_canonical` identifies which handler is providing this op,
    /// used to dispatch handler-specific lowerings (e.g. beam_ref vs ets_ref).
    pub(crate) fn build_beam_native_op_fun(
        &mut self,
        op_name: &str,
        handler_canonical: &str,
    ) -> CExpr {
        let (_, _, param_count) = crate::codegen::lower::beam_interop::lookup_native_op(op_name)
            .unwrap_or_else(|| panic!("unknown BEAM-native op: {}", op_name));

        let k_var = self.fresh();
        let param_vars: Vec<String> = (0..param_count).map(|i| format!("_HArg{}", i)).collect();

        let mut fun_params: Vec<String> = param_vars.clone();
        fun_params.push(k_var.clone());

        let call = if crate::codegen::lower::beam_interop::is_ref_op(op_name) {
            crate::codegen::lower::beam_interop::build_ref_native_call(
                handler_canonical,
                op_name,
                &param_vars,
                &mut || self.fresh(),
            )
        } else if crate::codegen::lower::beam_interop::is_vec_op(op_name) {
            crate::codegen::lower::beam_interop::build_vec_native_call(
                op_name,
                &param_vars,
                &mut || self.fresh(),
            )
        } else {
            let ctor_atoms = self.constructor_atoms.clone();
            crate::codegen::lower::beam_interop::build_native_call(
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
}
