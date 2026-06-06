//! Effect-machinery lowering for the new monadic lowerer (sub-steps 7d + 7e).
//!
//! Implements `MExpr::Yield` / `MExpr::With` in the **uniform open-row shape**
//! (every yield goes through `std_evidence_bridge:find_evidence/2` at runtime,
//! no closed-row specialization), and the handler-emission machinery feeding
//! into With sites: arm closure compilation, multi-arm-per-op `case` fan-out,
//! per-effect OpTuple assembly, and return-clause composition.
//!
//! See:
//!   - `docs/effect-implementation.md` — runtime evidence layout, the
//!     `find_evidence` / `insert_canonical` ABI, "Handler Representation",
//!     "The `return` Clause", "Non-Resumable Effects".
//!   - `src/codegen/lower/effects.rs` — the old lowerer's
//!     `build_op_handler_fun`, `build_multi_arm_inline_op_handler_fun`,
//!     `build_return_lambda`, and `compose_return_k` are the conventions we
//!     mirror here (copied, not imported, per the agent-guide allowlist).
//!   - `docs/planning/uniform-effect-translation/monadic-ir-spec.md` —
//!     `MExpr::Yield`, `MExpr::With`, `MHandler` variants, `MHandlerArm`.

use crate::ast::Pat;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::monadic::ir::{Atom, EffectOpRef, MExpr, MHandler, MHandlerArm};

use super::ctx::ResultDelimiter;
use super::util::{
    ABORT_TAG, VALUE_RESULT_TAG, core_var, marked_control_pattern, marked_control_tuple,
};
use super::{LowerCtx, Lowerer};

/// Erlang module hosting the runtime helpers
/// (`find_evidence/2`, `insert_canonical/2`, `project_evidence/2`).
const EVIDENCE_BRIDGE_MODULE: &str = "std_evidence_bridge";

fn apply_to_k(k: &str, value: CExpr) -> CExpr {
    CExpr::Apply(Box::new(CExpr::Var(k.to_string())), vec![value])
}

#[derive(Clone, Copy)]
enum ArmReturnMode {
    Captured,
    Direct,
}

fn delimiter_stack_handles(delimiter: &ResultDelimiter, effect: &str) -> bool {
    let mut current = Some(delimiter);
    while let Some(delim) = current {
        if delim.effects.iter().any(|handled| handled == effect) {
            return true;
        }
        current = delim.parent.as_deref();
    }
    false
}

fn delimiter_stack_marker_for(delimiter: &ResultDelimiter, effect: &str) -> Option<String> {
    let mut current = Some(delimiter);
    while let Some(delim) = current {
        if delim.effects.iter().any(|handled| handled == effect) {
            return Some(delim.abort_marker.clone());
        }
        current = delim.parent.as_deref();
    }
    None
}

impl<'ctx> Lowerer<'ctx> {
    // -----------------------------------------------------------------
    // MExpr::Yield
    // -----------------------------------------------------------------

    /// Lower `Yield { op, args }` to an open-row evidence lookup followed
    /// by an `apply` of the resolved op closure to the user args plus the
    /// perform-site evidence vector and ambient return continuation.
    ///
    /// Emits (sketch):
    /// ```text
    ///   apply (call 'erlang':'element'(<op_index>,
    ///             call 'std_evidence_bridge':'find_evidence'(
    ///                 _Evidence, '<EffectAtom>')))
    ///         (<args...>, <ctx.evidence>, <ctx.return_k>)
    /// ```
    ///
    /// `find_evidence/2` returns the per-effect `OpTuple` (a runtime tuple
    /// of op closures sorted alphabetically by op name); `erlang:element/2`
    /// then picks out the specific op by its 1-based canonical index, which
    /// is pre-resolved at translation time as `EffectOpRef.op_index`.
    ///
    /// Open-row is uniform here — the closed-row optimization (static
    /// `element/2` loads when the layout is statically known) requires
    /// per-call decisions that the new path explicitly avoids. The runtime
    /// walk is O(n) over a typically-≤5-entry tuple; closed-row
    /// specialization is a step-11+ optimization.
    pub(super) fn lower_yield(&mut self, op: &EffectOpRef, args: &[Atom], ctx: &LowerCtx) -> CExpr {
        // Lower args first — they're atoms (ANF), so non-effectful.
        let lowered_args: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a, ctx)).collect();

        let find_call = CExpr::Call(
            EVIDENCE_BRIDGE_MODULE.to_string(),
            "find_evidence".to_string(),
            vec![
                CExpr::Var(ctx.evidence.clone()),
                CExpr::Lit(CLit::Atom(op.effect.clone())),
            ],
        );
        let op_closure = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(op.op_index as i64)), find_call],
        );

        // A handler arm result is the result of the handler that owns the
        // performed operation, not an ordinary value at the perform site.
        // This only needs explicit marking while lowering an arm body
        // (`abort_marker` is present). Ordinary handled-body performs keep
        // the existing return-clause composition path; marking them here
        // would skip or double-apply return clauses.
        let target_marker = ctx.abort_marker.as_ref().and_then(|_| {
            ctx.result_delimiter
                .as_ref()
                .and_then(|delimiter| delimiter_stack_marker_for(delimiter, &op.effect))
        });
        let k_for_op = self.delimited_perform_k(&op.effect, ctx);

        let mut apply_args = lowered_args;
        apply_args.push(CExpr::Var(ctx.evidence.clone()));
        apply_args.push(k_for_op);
        let op_apply = CExpr::Apply(Box::new(op_closure), apply_args);
        if let Some(marker) = target_marker {
            self.wrap_yield_result_for_target(op_apply, &marker)
        } else {
            op_apply
        }
    }

    fn delimited_perform_k(&mut self, effect: &str, ctx: &LowerCtx) -> CExpr {
        let Some(delimiter) = &ctx.result_delimiter else {
            return CExpr::Var(ctx.return_k.clone());
        };
        if !delimiter_stack_handles(delimiter, effect) {
            return CExpr::Var(ctx.return_k.clone());
        }

        let arg = self.fresh_helper_name();
        let applied = CExpr::Apply(
            Box::new(CExpr::Var(ctx.return_k.clone())),
            vec![CExpr::Var(arg.clone())],
        );
        let body = self.wrap_result_delimiter_stack_until(applied, delimiter, effect, ctx);
        CExpr::Fun(vec![arg], Box::new(body))
    }

    fn wrap_yield_result_for_target(&mut self, op_apply: CExpr, target_marker: &str) -> CExpr {
        let result = self.fresh_helper_name();
        let mut arms = self.propagate_marked_control_arms();
        arms.push(CArm {
            pat: CPat::Var("_YieldValue".to_string()),
            guard: None,
            body: marked_control_tuple(
                VALUE_RESULT_TAG,
                CExpr::Lit(CLit::Atom(target_marker.to_string())),
                CExpr::Var("_YieldValue".to_string()),
            ),
        });
        CExpr::Let(
            result.clone(),
            Box::new(op_apply),
            Box::new(CExpr::Case(Box::new(CExpr::Var(result)), arms)),
        )
    }

    // -----------------------------------------------------------------
    // MExpr::With
    // -----------------------------------------------------------------

    /// Lower `With { handler, body }` by extending the in-scope evidence
    /// vector with the handler's `{EffectAtom, OpTuple}` entry/entries, then
    /// lowering `body` under the extended evidence.
    ///
    /// Multi-effect static handlers emit one `insert_canonical` per effect
    /// in sequence; innermost-wins ordering falls out of the runtime helper
    /// (it replaces a same-tagged entry rather than appending).
    pub(super) fn lower_with(&mut self, handler: &MHandler, body: &MExpr, ctx: &LowerCtx) -> CExpr {
        match handler {
            MHandler::Static {
                effects,
                arms,
                return_clause,
                ..
            } => self.lower_with_static(effects, arms, return_clause.as_ref(), body, ctx),
            MHandler::Native {
                effects, handler, ..
            } => self.lower_with_native(effects, handler, body, ctx),
            MHandler::Composite { handlers, source } => {
                let nested = handlers
                    .iter()
                    .rev()
                    .fold(body.clone(), |acc, h| MExpr::With {
                        handler: h.clone(),
                        body: Box::new(acc),
                        source: *source,
                    });
                self.lower_expr(&nested, ctx)
            }
            MHandler::Dynamic {
                effects,
                op_tuple,
                return_lambda,
                ..
            } => {
                if effects.is_empty() {
                    eprintln!(
                        "  warning: dynamic handler at `with` site has unknown effect tag — \
                         evidence install skipped"
                    );
                    return self.lower_expr(body, ctx);
                }
                self.lower_with_dynamic(effects, op_tuple, return_lambda.as_ref(), body, ctx)
            }
        }
    }

    fn lower_with_native(
        &mut self,
        effects: &[String],
        handler: &str,
        body: &MExpr,
        ctx: &LowerCtx,
    ) -> CExpr {
        let mut entry_bindings: Vec<(String, CExpr)> = Vec::with_capacity(effects.len());
        let mut acc_evidence_var = ctx.evidence.clone();

        for effect in effects {
            let Some(op_tuple) = super::bootstrap::native_handler_op_tuple(effect, handler) else {
                eprintln!(
                    "  warning: native handler `{}` for effect `{}` is not implemented in \
                     the new lowerer; evidence install skipped",
                    handler, effect
                );
                continue;
            };
            let entry = CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(effect.clone())), op_tuple]);
            let insert = CExpr::Call(
                EVIDENCE_BRIDGE_MODULE.to_string(),
                "insert_canonical".to_string(),
                vec![CExpr::Var(acc_evidence_var.clone()), entry],
            );
            let new_name = self.fresh_evidence_name();
            entry_bindings.push((new_name.clone(), insert));
            acc_evidence_var = new_name;
        }

        let body_ctx = ctx.with_evidence(acc_evidence_var);
        let body_ce = self.lower_expr(body, &body_ctx);
        entry_bindings
            .into_iter()
            .rev()
            .fold(body_ce, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            })
    }

    /// Static-handler case of [`lower_with`]. For each effect handled, build
    /// `{EffectAtom, OpTuple}` from the matching arms (sorted by canonical
    /// op index) and chain `insert_canonical` calls; lower the return clause
    /// (if any) as a fresh `_K_ret{n}` continuation; finally lower the body
    /// under the extended evidence with K = return-clause K (or outer K).
    ///
    /// Arm closures are built using the outer `ctx` (its `ctx.evidence` /
    /// `ctx.return_k` still reflect the *outer* scope) — re-performs from
    /// inside an arm body must reach the outer handler stack, not recurse
    /// into the just-installed entry. This falls out of building the
    /// closures before deriving a `body_ctx` with the extended evidence
    /// for lowering the `with` body.
    fn lower_with_static(
        &mut self,
        effects: &[String],
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
        body: &MExpr,
        ctx: &LowerCtx,
    ) -> CExpr {
        // Snapshot the outer scope. Arm bodies and the return-clause body
        // both lower with these in scope, so re-performs hit the outer
        // handler stack and the return clause forwards through the outer K.
        let outer_evidence = ctx.evidence.clone();
        let raw_result_k = self.fresh_k_ret_name();
        let abort_marker = self.fresh_abort_marker();
        let raw_result_k_binding = identity_continuation();
        let arm_ctx = ctx
            .with_return_k(raw_result_k.clone())
            .with_abort_marker(abort_marker.clone());

        // 1. Build per-effect entries from the arms. Arm closures reference
        //    `outer_evidence` / `outer_return_k` inside; we build them with
        //    the lowerer state still pointing at the outer scope.
        //
        // The handler's `effects` vec carries the **bare** source-level
        // effect names (e.g. `Stdio`). Arm `op.effect` carries the
        // **canonical** name (e.g. `Std.IO.Stdio`) from the typechecker's
        // `effect_calls` map. The lowerer's `Yield` path also uses
        // canonical names to look up evidence at runtime, so the with-site
        // must install entries under the canonical tag — otherwise the
        // tags don't match and `find_evidence` reports
        // `evidence_tag_not_found`. We therefore derive the effect set
        // from the arms, ignoring the bare-named `effects` parameter
        // (left in for spec parity).
        let _ = effects;
        let mut canonical_effects: Vec<String> = Vec::new();
        for arm in arms {
            if !canonical_effects.contains(&arm.op.effect) {
                canonical_effects.push(arm.op.effect.clone());
            }
        }
        let mut entry_bindings: Vec<(String, CExpr)> = Vec::with_capacity(canonical_effects.len());
        let mut acc_evidence_var = outer_evidence.clone();
        for eff in &canonical_effects {
            let effect_arms: Vec<&MHandlerArm> =
                arms.iter().filter(|a| a.op.effect == *eff).collect();
            let op_tuple = self.build_op_tuple_for_effect(eff, &effect_arms, &arm_ctx);
            let entry = CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(eff.clone())), op_tuple]);
            let insert = CExpr::Call(
                EVIDENCE_BRIDGE_MODULE.to_string(),
                "insert_canonical".to_string(),
                vec![CExpr::Var(acc_evidence_var.clone()), entry],
            );
            let new_name = self.fresh_evidence_name();
            entry_bindings.push((new_name.clone(), insert));
            acc_evidence_var = new_name;
        }

        // 2. Build the return-clause continuation (if any). Lowered while
        //    state still reflects outer scope so its body forwards through
        //    the outer K and references the outer evidence.
        let ret_binding: Option<(String, CExpr)> = return_clause.map(|arm| {
            let closure = self.build_return_clause_closure(arm, &arm_ctx);
            (self.fresh_k_ret_name(), closure)
        });

        // 3. Lower the body under the inner K (return-clause K if present,
        //    else the outer K) and the extended evidence.
        let inner_k = ret_binding
            .as_ref()
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| raw_result_k.clone());
        let prompt_k = self.fresh_k_ret_name();
        let prompt_k_binding =
            self.build_result_delimiter_k(&abort_marker, &inner_k, &raw_result_k);

        let body_ctx = ctx
            .with_evidence(acc_evidence_var)
            .with_return_k(prompt_k.clone())
            .with_result_delimiter(
                canonical_effects.clone(),
                abort_marker.clone(),
                prompt_k.clone(),
                ctx.preserve_abort_marker,
            );
        let body_ce = self.lower_expr(body, &body_ctx);
        let wrapped_body = self.wrap_with_result_delimiter(body_ce, &abort_marker, ctx);

        // 4. Wrap inside-out: insert_canonical chain wraps the body, then
        //    the return-K binding (if any) wraps the chain. The raw-result
        //    K sits outermost so both handler arms and return clauses can
        //    produce values back to the `with` delimiter; only the wrapper
        //    around the whole handled computation applies the outer K.
        let with_evidence = entry_bindings
            .into_iter()
            .rev()
            .fold(wrapped_body, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            });
        let with_prompt = CExpr::Let(
            prompt_k,
            Box::new(prompt_k_binding),
            Box::new(with_evidence),
        );
        let with_return = match ret_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(with_prompt)),
            None => with_prompt,
        };
        CExpr::Let(
            raw_result_k,
            Box::new(raw_result_k_binding),
            Box::new(with_return),
        )
    }

    /// Dynamic-handler case of [`lower_with`]. The op tuple is a runtime
    /// closure-tuple value (an `Atom` carrying it); we lower it in place and
    /// wrap into `{EffectAtom, OpTuple}` exactly like the static path. The
    /// optional `return_lambda` is wrapped into a continuation closure that
    /// applies the lambda under outer evidence + outer K — same composition
    /// shape as Static's return clause.
    fn lower_with_dynamic(
        &mut self,
        effects: &[String],
        op_tuple: &Atom,
        return_lambda: Option<&Atom>,
        body: &MExpr,
        ctx: &LowerCtx,
    ) -> CExpr {
        // Sort effects canonically (alphabetical) so the positional index of
        // each effect into `OpsByEffect` matches the producer's ordering in
        // `build_ops_by_effect_tuple`. Single-effect is a 1-element list and
        // the loop below installs exactly one entry.
        let mut sorted_effects: Vec<String> = effects.to_vec();
        sorted_effects.sort();

        let outer_evidence = ctx.evidence.clone();
        let raw_result_k = self.fresh_k_ret_name();
        let abort_marker = self.fresh_abort_marker();
        let raw_result_k_binding = identity_continuation();

        let handler_value_ce = self.lower_atom(op_tuple, ctx);
        let handler_value_var = self.fresh_helper_name();
        let runtime_return_var = self.fresh_helper_name();
        let runtime_return_value = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![
                CExpr::Lit(CLit::Int(3)),
                CExpr::Var(handler_value_var.clone()),
            ],
        );
        // element 2 is the OpsByEffect tuple of {EffectAtom, OpTuple} pairs.
        let ops_by_effect_var = self.fresh_helper_name();
        let ops_by_effect_value = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![
                CExpr::Lit(CLit::Int(2)),
                CExpr::Var(handler_value_var.clone()),
            ],
        );

        // Return-lambda composition (built under outer scope).
        let ret_binding: Option<(String, CExpr)> = return_lambda.map(|atom| {
            let lambda_ce = self.lower_atom(atom, ctx);
            let v_param = self.fresh_helper_name();
            // The Atom is a uniform-CPS lambda: `fun(value, _Evidence, _ReturnK)`.
            // Wrap as a delimited continuation: the lambda produces a raw
            // with-result, and the `with` wrapper applies the outer K once.
            let wrapper = CExpr::Fun(
                vec![v_param.clone()],
                Box::new(CExpr::Apply(
                    Box::new(lambda_ce),
                    vec![
                        CExpr::Var(v_param),
                        CExpr::Var(outer_evidence.clone()),
                        CExpr::Var(raw_result_k.clone()),
                    ],
                )),
            );
            (self.fresh_k_ret_name(), wrapper)
        });

        let runtime_ret_k = self.fresh_k_ret_name();
        let runtime_ret_param = self.fresh_helper_name();
        let runtime_ret_binding = CExpr::Fun(
            vec![runtime_ret_param.clone()],
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(runtime_return_var.clone())),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("unit".to_string())),
                        guard: None,
                        body: CExpr::Apply(
                            Box::new(CExpr::Var(raw_result_k.clone())),
                            vec![CExpr::Var(runtime_ret_param.clone())],
                        ),
                    },
                    CArm {
                        pat: CPat::Var("_RuntimeReturn".to_string()),
                        guard: None,
                        body: CExpr::Apply(
                            Box::new(CExpr::Var("_RuntimeReturn".to_string())),
                            vec![
                                CExpr::Var(runtime_ret_param),
                                CExpr::Var(outer_evidence.clone()),
                                CExpr::Var(raw_result_k.clone()),
                            ],
                        ),
                    },
                ],
            )),
        );

        let inner_k = ret_binding
            .as_ref()
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| runtime_ret_k.clone());

        // Build the per-effect evidence-install chain. For each effect at
        // sorted index i, extract `element(i+1, OpsByEffect)` (a
        // {EffectAtom, OpTuple} pair), then `element(2, pair)` (the
        // per-effect op tuple), then call `insert_canonical(acc_ev,
        // {EffectAtom_literal, op_tuple})` to extend the evidence vector.
        // The effect atom is re-emitted as a literal — the pair carries the
        // same atom but the consumer reconstructs it from static knowledge.
        let mut install_bindings: Vec<(String, CExpr)> = Vec::new();
        let mut acc_ev = outer_evidence.clone();
        for (i, eff) in sorted_effects.iter().enumerate() {
            let pair_var = self.fresh_helper_name();
            let pair_value = CExpr::Call(
                "erlang".to_string(),
                "element".to_string(),
                vec![
                    CExpr::Lit(CLit::Int((i as i64) + 1)),
                    CExpr::Var(ops_by_effect_var.clone()),
                ],
            );
            install_bindings.push((pair_var.clone(), pair_value));

            let op_tuple_var = self.fresh_helper_name();
            let op_tuple_value = CExpr::Call(
                "erlang".to_string(),
                "element".to_string(),
                vec![CExpr::Lit(CLit::Int(2)), CExpr::Var(pair_var)],
            );
            install_bindings.push((op_tuple_var.clone(), op_tuple_value));

            let entry = CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom(eff.clone())),
                CExpr::Var(op_tuple_var),
            ]);
            let insert = CExpr::Call(
                EVIDENCE_BRIDGE_MODULE.to_string(),
                "insert_canonical".to_string(),
                vec![CExpr::Var(acc_ev.clone()), entry],
            );
            let new_ev_name = self.fresh_evidence_name();
            install_bindings.push((new_ev_name.clone(), insert));
            acc_ev = new_ev_name;
        }

        let prompt_k = self.fresh_k_ret_name();
        let prompt_k_binding =
            self.build_result_delimiter_k(&abort_marker, &inner_k, &raw_result_k);

        let body_ctx = ctx
            .with_evidence(acc_ev.clone())
            .with_return_k(prompt_k.clone())
            .with_result_delimiter(
                sorted_effects.clone(),
                abort_marker.clone(),
                prompt_k.clone(),
                ctx.preserve_abort_marker,
            );
        let body_ce = self.lower_expr(body, &body_ctx);
        let wrapped_body = self.wrap_with_result_delimiter(body_ce, &abort_marker, ctx);

        let with_evidence = install_bindings
            .into_iter()
            .rev()
            .fold(wrapped_body, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            });
        let with_prompt = CExpr::Let(
            prompt_k,
            Box::new(prompt_k_binding),
            Box::new(with_evidence),
        );
        let with_runtime_return = CExpr::Let(
            runtime_return_var,
            Box::new(runtime_return_value),
            Box::new(CExpr::Let(
                runtime_ret_k,
                Box::new(runtime_ret_binding),
                Box::new(with_prompt),
            )),
        );
        let with_return = match ret_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(with_runtime_return)),
            None => with_runtime_return,
        };
        let with_ops_by_effect = CExpr::Let(
            ops_by_effect_var,
            Box::new(ops_by_effect_value),
            Box::new(with_return),
        );
        let with_handler_value = CExpr::Let(
            handler_value_var,
            Box::new(handler_value_ce),
            Box::new(with_ops_by_effect),
        );
        CExpr::Let(
            raw_result_k,
            Box::new(raw_result_k_binding),
            Box::new(with_handler_value),
        )
    }

    fn build_result_delimiter_k(
        &mut self,
        abort_marker: &str,
        success_k: &str,
        abort_k: &str,
    ) -> CExpr {
        let result = self.fresh_helper_name();
        let arms = self.result_delimiter_arms(
            abort_marker,
            |value| apply_to_k(success_k, value),
            |value| apply_to_k(abort_k, value),
            |value| apply_to_k(success_k, value),
        );
        CExpr::Fun(
            vec![result.clone()],
            Box::new(CExpr::Case(Box::new(CExpr::Var(result)), arms)),
        )
    }

    /// Wrap a lowered `with` body in the common delimiter that interprets
    /// local abort markers and forwards ordinary values through the outer K.
    fn wrap_with_result_delimiter(
        &mut self,
        body_ce: CExpr,
        abort_marker: &str,
        ctx: &LowerCtx,
    ) -> CExpr {
        self.wrap_with_result_delimiter_to_k(
            body_ce,
            abort_marker,
            &ctx.return_k,
            ctx.preserve_abort_marker,
        )
    }

    pub(super) fn wrap_with_result_delimiter_to_k(
        &mut self,
        body_ce: CExpr,
        abort_marker: &str,
        return_k: &str,
        preserve_abort_marker: bool,
    ) -> CExpr {
        let with_result = self.fresh_helper_name();
        let arms = self.result_delimiter_arms(
            abort_marker,
            |value| apply_to_k(return_k, value),
            |value| {
                if preserve_abort_marker {
                    marked_control_tuple(
                        ABORT_TAG,
                        CExpr::Lit(CLit::Atom(abort_marker.to_string())),
                        value,
                    )
                } else {
                    apply_to_k(return_k, value)
                }
            },
            |value| apply_to_k(return_k, value),
        );
        CExpr::Let(
            with_result.clone(),
            Box::new(body_ce),
            Box::new(CExpr::Case(Box::new(CExpr::Var(with_result)), arms)),
        )
    }

    pub(super) fn wrap_with_result_delimiter_raw(
        &mut self,
        body_ce: CExpr,
        abort_marker: &str,
        preserve_abort_marker: bool,
    ) -> CExpr {
        let with_result = self.fresh_helper_name();
        let arms = self.result_delimiter_arms(
            abort_marker,
            |value| value,
            |value| {
                if preserve_abort_marker {
                    marked_control_tuple(
                        ABORT_TAG,
                        CExpr::Lit(CLit::Atom(abort_marker.to_string())),
                        value,
                    )
                } else {
                    value
                }
            },
            |value| value,
        );
        CExpr::Let(
            with_result.clone(),
            Box::new(body_ce),
            Box::new(CExpr::Case(Box::new(CExpr::Var(with_result)), arms)),
        )
    }

    fn result_delimiter_arms(
        &mut self,
        abort_marker: &str,
        local_value_body: impl Fn(CExpr) -> CExpr,
        local_abort_body: impl Fn(CExpr) -> CExpr,
        ordinary_value_body: impl Fn(CExpr) -> CExpr,
    ) -> Vec<CArm> {
        let abort_value = self.fresh_helper_name();
        let mut arms = vec![
            CArm {
                pat: marked_control_pattern(
                    VALUE_RESULT_TAG,
                    CPat::Lit(CLit::Atom(abort_marker.to_string())),
                    abort_value.clone(),
                ),
                guard: None,
                body: local_value_body(CExpr::Var(abort_value.clone())),
            },
            CArm {
                pat: marked_control_pattern(
                    ABORT_TAG,
                    CPat::Lit(CLit::Atom(abort_marker.to_string())),
                    abort_value.clone(),
                ),
                guard: None,
                body: local_abort_body(CExpr::Var(abort_value)),
            },
        ];
        arms.extend(self.propagate_marked_control_arms());
        arms.push(CArm {
            pat: CPat::Var("_WithValue".to_string()),
            guard: None,
            body: ordinary_value_body(CExpr::Var("_WithValue".to_string())),
        });
        arms
    }

    fn wrap_result_delimiter_stack_until(
        &mut self,
        mut body_ce: CExpr,
        delimiter: &ResultDelimiter,
        effect: &str,
        ctx: &LowerCtx,
    ) -> CExpr {
        let mut current = Some(delimiter);
        while let Some(delim) = current {
            body_ce = self.wrap_with_result_delimiter_raw(
                body_ce,
                &delim.abort_marker,
                ctx.preserve_abort_marker || delim.preserve_abort_marker,
            );
            if delim.effects.iter().any(|handled| handled == effect) {
                break;
            }
            current = delim.parent.as_deref();
        }
        body_ce
    }

    // -----------------------------------------------------------------
    // OpTuple assembly + arm closure compilation
    // -----------------------------------------------------------------

    /// Build the `OpTuple` (a Core Erlang tuple of per-op closures) for a
    /// single effect's arms. Arms are sorted by `op_index`, grouped by
    /// `op_index` (multi-arm-per-op is permitted — Saga's surface syntax
    /// allows pattern-matching across op params), and emitted in canonical
    /// (alphabetical) order.
    ///
    /// Invariant: op indices must be 1..N consecutive. If gaps appear (an
    /// effect declares more ops than the handler covers), we panic rather
    /// than emit a misaligned tuple — the typechecker is responsible for
    /// rejecting handlers that don't discharge every op of every effect they
    /// list. (Flagged: if a real workload hits this, the right fix is to
    /// thread effect-op-set info via `EffectInfo` and pad missing ops with
    /// a passthrough closure — same as `build_passthrough_handler_fun` in
    /// the old lowerer.)
    fn build_op_tuple_for_effect(
        &mut self,
        eff: &str,
        arms: &[&MHandlerArm],
        ctx: &LowerCtx,
    ) -> CExpr {
        let mut sorted: Vec<&MHandlerArm> = arms.to_vec();
        sorted.sort_by_key(|a| a.op.op_index);

        // Group consecutive arms with the same op_index together.
        let mut groups: Vec<Vec<&MHandlerArm>> = Vec::new();
        for arm in sorted {
            if let Some(last) = groups.last_mut()
                && last[0].op.op_index == arm.op.op_index
            {
                last.push(arm);
                continue;
            }
            groups.push(vec![arm]);
        }

        // Verify canonical 1..N consecutive coverage.
        for (i, group) in groups.iter().enumerate() {
            let expected = (i as u32) + 1;
            let actual = group[0].op.op_index;
            if actual != expected {
                panic!(
                    "build_op_tuple_for_effect: Static handler for effect '{}' is missing \
                     arm for op_index {} (next arm has op_index {}). The typechecker \
                     should have rejected handlers that don't cover every op; if this \
                     fires in practice, thread effect-op-set info via EffectInfo and \
                     emit passthrough closures for missing ops.",
                    eff, expected, actual
                );
            }
        }

        let closures: Vec<CExpr> = groups
            .into_iter()
            .map(|g| {
                if g.len() == 1 {
                    self.build_arm_closure(g[0], ctx)
                } else {
                    self.build_multi_arm_op_closure(&g, ctx)
                }
            })
            .collect();

        CExpr::Tuple(closures)
    }

    /// Compile a single `MHandlerArm` into its per-op closure:
    ///
    /// ```text
    /// fun(<arm.params...>, _Ev_perform, _K_arm{n}) -> <arm.body lowered under _K_arm{n}>
    /// ```
    ///
    /// Each arm param maps to a closure parameter:
    ///   - `Pat::Var { name }` → that name (mangled via `core_var`).
    ///   - non-Var patterns → a positional `_HArg{i}` plus a destructuring
    ///     `case` wrap around the body.
    pub(super) fn build_arm_closure(&mut self, arm: &MHandlerArm, ctx: &LowerCtx) -> CExpr {
        self.build_arm_closure_with_return_mode(arm, ctx, ArmReturnMode::Captured)
    }

    pub(super) fn build_handler_value_arm_closure(
        &mut self,
        arm: &MHandlerArm,
        ctx: &LowerCtx,
    ) -> CExpr {
        self.build_arm_closure_with_return_mode(arm, ctx, ArmReturnMode::Direct)
    }

    fn build_arm_closure_with_return_mode(
        &mut self,
        arm: &MHandlerArm,
        ctx: &LowerCtx,
        mode: ArmReturnMode,
    ) -> CExpr {
        let (closure_params, body_wraps) = self.plan_arm_params(&arm.params);
        let perform_ev = self.fresh_helper_name();
        let k_arm = self.fresh_k_arm_name();
        let direct_k = if matches!(mode, ArmReturnMode::Direct) {
            Some(self.fresh_helper_name())
        } else {
            None
        };
        let body_ctx = match mode {
            ArmReturnMode::Captured => ctx.with_arm_k(k_arm.clone()),
            ArmReturnMode::Direct => ctx
                .with_arm_k(k_arm.clone())
                .with_return_k(direct_k.as_ref().unwrap().clone()),
        };
        let mut body_ce = self.lower_captured_arm_body(arm, &body_ctx);

        if let Some(direct_k) = direct_k {
            body_ce = CExpr::Let(
                direct_k,
                Box::new(CExpr::Fun(
                    vec!["_V".to_string()],
                    Box::new(CExpr::Var("_V".to_string())),
                )),
                Box::new(body_ce),
            );
        }
        let body_with_pats = self.wrap_arm_param_destructures(body_ce, body_wraps);

        let mut params = closure_params;
        params.push(perform_ev);
        params.push(k_arm);
        CExpr::Fun(params, Box::new(body_with_pats))
    }

    /// Lower a handler arm's body under a continuation already set in
    /// `body_ctx` (its `arm_k`, and for value arms its `return_k`), applying
    /// the arm's `finally` cleanup and abort-marker tagging:
    ///   - resuming arm + finally: the cleanup runs at each resume site
    ///     (threaded via `with_finally`, consumed in `lower_resume`).
    ///   - aborting arm + finally: the cleanup is appended after the body.
    ///   - aborting arm (no resume): the result is tagged with the with-site's
    ///     abort marker so nested delimiters can propagate it.
    ///
    /// Param binding (closure params for single arms, case patterns for
    /// multi-arm-per-op) is the caller's job; this only registers `arm.params`
    /// as locals so the body resolves them.
    fn lower_captured_arm_body(&mut self, arm: &MHandlerArm, body_ctx: &LowerCtx) -> CExpr {
        let has_resume = arm.body.contains_resume();
        let mut lower_ctx = body_ctx.clone();
        if let Some(ref fb) = arm.finally_block
            && has_resume
        {
            lower_ctx = lower_ctx.with_finally(fb.clone());
        }
        let arm_ctx = lower_ctx.with_param_locals(&arm.params);
        let mut body_ce = self.lower_expr(&arm.body, &arm_ctx);

        // For abort arms (no resume) with finally: append cleanup after body.
        if let (Some(fb), false) = (&arm.finally_block, has_resume) {
            let result_var = self.fresh_helper_name();
            body_ce = CExpr::Let(
                result_var.clone(),
                Box::new(body_ce),
                Box::new(self.sequence_finally_then(fb, &arm_ctx, CExpr::Var(result_var))),
            );
        }

        if !has_resume && let Some(marker) = &arm_ctx.abort_marker {
            let result_var = self.fresh_helper_name();
            let mut arms = self.propagate_marked_control_arms();
            arms.push(CArm {
                pat: CPat::Var("_AbortValue".to_string()),
                guard: None,
                body: marked_control_tuple(
                    ABORT_TAG,
                    CExpr::Lit(CLit::Atom(marker.clone())),
                    CExpr::Var("_AbortValue".to_string()),
                ),
            });
            body_ce = CExpr::Let(
                result_var.clone(),
                Box::new(body_ce),
                Box::new(CExpr::Case(Box::new(CExpr::Var(result_var)), arms)),
            );
        }

        body_ce
    }

    /// Multi-arm-per-op closure. The op has N>1 arms that pattern-match on
    /// op params; emit:
    ///
    /// ```text
    /// fun(_HArg0, ..., _HArgK, _Ev_perform, _K_arm{n}) ->
    ///   case _HArg0 of
    ///     <arm0.params[0]> -> <arm0.body under _K_arm{n}>
    ///     <arm1.params[0]> -> <arm1.body under _K_arm{n}>
    ///     ...
    ///   end
    /// ```
    ///
    /// For >1 op param, the scrutinee is `<_HArg0, ..., _HArgK>` and each
    /// arm pattern is `<arm.params[0], ..., arm.params[K]>` — matching the
    /// old lowerer's `build_multi_arm_inline_op_handler_fun` shape.
    ///
    /// All arms share one K (`_K_arm{n}`) — the captured continuation of the
    /// perform site is independent of which arm matched.
    fn build_multi_arm_op_closure(&mut self, arms: &[&MHandlerArm], ctx: &LowerCtx) -> CExpr {
        let n_params = arms[0].params.len();
        for arm in arms.iter().skip(1) {
            assert_eq!(
                arm.params.len(),
                n_params,
                "multi-arm-per-op: all arms must take the same number of op params \
                 (effect={}, op={})",
                arm.op.effect,
                arm.op.op
            );
        }

        let positional: Vec<String> = (0..n_params).map(|i| format!("_HArg{}", i)).collect();
        let perform_ev = self.fresh_helper_name();
        let k_arm = self.fresh_k_arm_name();

        let scrutinee = if n_params == 1 {
            CExpr::Var(positional[0].clone())
        } else {
            CExpr::Values(positional.iter().cloned().map(CExpr::Var).collect())
        };

        let body_ctx = ctx.with_arm_k(k_arm.clone());
        let mut case_arms: Vec<CArm> = Vec::with_capacity(arms.len());
        for arm in arms {
            let body_ce = self.lower_captured_arm_body(arm, &body_ctx);
            let pat = if n_params == 1 {
                self.lower_pat(&arm.params[0])
            } else {
                CPat::Values(arm.params.iter().map(|p| self.lower_pat(p)).collect())
            };
            case_arms.push(CArm {
                pat,
                guard: None,
                body: body_ce,
            });
        }

        let mut fun_params = positional;
        fun_params.push(perform_ev);
        fun_params.push(k_arm);
        CExpr::Fun(
            fun_params,
            Box::new(CExpr::Case(Box::new(scrutinee), case_arms)),
        )
    }

    /// Build the return-clause closure: a continuation `fun(_V) -> body`
    /// where `body` is lowered with the outer K still in scope, so the
    /// clause's tail value flows naturally to the surrounding caller.
    ///
    /// The closure shape matches a regular continuation (single value
    /// parameter) — the with site binds it as `_K_ret{n}` and threads it
    /// as the body's K. Nested withs compose innermost-first by
    /// construction: each inner with binds its own `_K_ret{m}` referring
    /// to the next-outer K, which is itself a `_K_ret{m-1}` if that layer
    /// has a return clause.
    pub(super) fn build_return_clause_closure(
        &mut self,
        arm: &MHandlerArm,
        ctx: &LowerCtx,
    ) -> CExpr {
        // The parser never attaches a `finally` to a `return` clause (both the
        // named- and inline-handler paths hardcode `finally_block: None`), so a
        // return clause's cleanup is structurally impossible. Asserted, not
        // handled.
        debug_assert!(
            arm.finally_block.is_none(),
            "return clause unexpectedly carries a finally block (effect={}, op={})",
            arm.op.effect,
            arm.op.op
        );
        let (param_name, body_wrap) = match arm.params.as_slice() {
            [] => (self.fresh_helper_name(), None),
            [Pat::Var { name, .. }] => (core_var(name), None),
            [pat] => {
                let positional = format!("_HArg{}", 0);
                (positional, Some(pat.clone()))
            }
            many => panic!(
                "build_return_clause_closure: return clause expected ≤1 param; got {}",
                many.len()
            ),
        };

        // Body lowers under the outer K + outer evidence (the ctx passed in
        // by `lower_with_static` is the outer scope — see that fn).
        let body_ctx = ctx.with_param_locals(&arm.params);
        let body_ce = self.lower_expr(&arm.body, &body_ctx);
        let body_with_pat = match body_wrap {
            None => body_ce,
            Some(pat) => {
                let cpat = self.lower_pat(&pat);
                CExpr::Case(
                    Box::new(CExpr::Var(param_name.clone())),
                    vec![CArm {
                        pat: cpat,
                        guard: None,
                        body: body_ce,
                    }],
                )
            }
        };
        CExpr::Fun(vec![param_name], Box::new(body_with_pat))
    }

    /// Compute closure-parameter names + body-destructure plan for an arm's
    /// op-parameter patterns.
    ///
    /// Single-arm path only: `Pat::Var` lets the var name *be* the closure
    /// param; anything else gets a positional `_HArg{i}` and a destructure
    /// wrapper on the body.
    fn plan_arm_params(&self, params: &[Pat]) -> (Vec<String>, Vec<(String, Pat)>) {
        let mut closure_params = Vec::with_capacity(params.len());
        let mut wraps = Vec::new();
        for (i, pat) in params.iter().enumerate() {
            match pat {
                Pat::Var { name, .. } => closure_params.push(core_var(name)),
                Pat::Wildcard { .. } => closure_params.push(format!("_HArg{}", i)),
                _ => {
                    let name = format!("_HArg{}", i);
                    closure_params.push(name.clone());
                    wraps.push((name, pat.clone()));
                }
            }
        }
        (closure_params, wraps)
    }

    /// Apply the destructure plan from [`plan_arm_params`]: wrap `body` with
    /// a `case <_HArg{i}> of <pat> -> body` for each non-Var/Wildcard arm
    /// param. Outer wraps are emitted last so inner patterns bind first.
    fn wrap_arm_param_destructures(&self, mut body: CExpr, wraps: Vec<(String, Pat)>) -> CExpr {
        for (arg_name, pat) in wraps.into_iter().rev() {
            let cpat = self.lower_pat(&pat);
            body = CExpr::Case(
                Box::new(CExpr::Var(arg_name)),
                vec![CArm {
                    pat: cpat,
                    guard: None,
                    body,
                }],
            );
        }
        body
    }
}

fn identity_continuation() -> CExpr {
    CExpr::Fun(
        vec!["_V".to_string()],
        Box::new(CExpr::Var("_V".to_string())),
    )
}
