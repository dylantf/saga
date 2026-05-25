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

use super::Lowerer;
use super::pats::lower_pat;
use super::util::core_var;

/// Erlang module hosting the runtime helpers
/// (`find_evidence/2`, `insert_canonical/2`, `project_evidence/2`).
const EVIDENCE_BRIDGE_MODULE: &str = "std_evidence_bridge";

impl<'ctx> Lowerer<'ctx> {
    // -----------------------------------------------------------------
    // MExpr::Yield
    // -----------------------------------------------------------------

    /// Lower `Yield { op, args }` to an open-row evidence lookup followed
    /// by an `apply` of the resolved op closure to the user args plus the
    /// ambient return continuation.
    ///
    /// Emits (sketch):
    /// ```text
    ///   apply (call 'erlang':'element'(<op_index>,
    ///             call 'std_evidence_bridge':'find_evidence'(
    ///                 _Evidence, '<EffectAtom>')))
    ///         (<args...>, <current_return_k>)
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
    pub(super) fn lower_yield(&mut self, op: &EffectOpRef, args: &[Atom]) -> CExpr {
        // Lower args first — they're atoms (ANF), so non-effectful.
        let lowered_args: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a)).collect();

        let find_call = CExpr::Call(
            EVIDENCE_BRIDGE_MODULE.to_string(),
            "find_evidence".to_string(),
            vec![
                CExpr::Var(self.current_evidence.clone()),
                CExpr::Lit(CLit::Atom(op.effect.clone())),
            ],
        );
        let op_closure = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(op.op_index as i64)), find_call],
        );

        let mut apply_args = lowered_args;
        apply_args.push(CExpr::Var(self.current_return_k.clone()));
        CExpr::Apply(Box::new(op_closure), apply_args)
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
    pub(super) fn lower_with(&mut self, handler: &MHandler, body: &MExpr) -> CExpr {
        match handler {
            MHandler::Static {
                effects,
                arms,
                return_clause,
                ..
            } => self.lower_with_static(effects, arms, return_clause.as_ref(), body),
            MHandler::Dynamic {
                effects,
                op_tuple,
                return_lambda,
                ..
            } => {
                // Per the spec, the translator currently only emits Dynamic
                // handlers carrying a single effect; relaxing this requires
                // an explicit spec amendment, not a silent multi-effect
                // expansion here.
                if effects.len() != 1 {
                    panic!(
                        "lower_with: Dynamic handler must carry exactly one effect \
                         (spec invariant); got {:?}",
                        effects
                    );
                }
                self.lower_with_dynamic(&effects[0], op_tuple, return_lambda.as_ref(), body)
            }
        }
    }

    /// Static-handler case of [`lower_with`]. For each effect handled, build
    /// `{EffectAtom, OpTuple}` from the matching arms (sorted by canonical
    /// op index) and chain `insert_canonical` calls; lower the return clause
    /// (if any) as a fresh `_K_ret{n}` continuation; finally lower the body
    /// under the extended evidence with K = return-clause K (or outer K).
    ///
    /// Arm closures are built while `self.current_evidence` / `self.current_return_k`
    /// still reflect the *outer* scope — re-performs from inside an arm body
    /// must reach the outer handler stack, not recurse into the just-installed
    /// entry. This falls out of building the closures before swapping the
    /// evidence var for the body.
    fn lower_with_static(
        &mut self,
        effects: &[String],
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
        body: &MExpr,
    ) -> CExpr {
        // Snapshot the outer scope. Arm bodies and the return-clause body
        // both lower with these in scope, so re-performs hit the outer
        // handler stack and the return clause forwards through the outer K.
        let outer_evidence = self.current_evidence.clone();
        let outer_return_k = self.current_return_k.clone();

        // 1. Build per-effect entries from the arms. Arm closures reference
        //    `outer_evidence` / `outer_return_k` inside; we build them with
        //    the lowerer state still pointing at the outer scope.
        let mut entry_bindings: Vec<(String, CExpr)> = Vec::with_capacity(effects.len());
        let mut acc_evidence_var = outer_evidence.clone();
        for eff in effects {
            let effect_arms: Vec<&MHandlerArm> =
                arms.iter().filter(|a| a.op.effect == *eff).collect();
            let op_tuple = self.build_op_tuple_for_effect(eff, &effect_arms);
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
            let closure = self.build_return_clause_closure(arm);
            (self.fresh_k_ret_name(), closure)
        });

        // 3. Lower the body under the inner K (return-clause K if present,
        //    else the outer K) and the extended evidence.
        let inner_k = ret_binding
            .as_ref()
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| outer_return_k.clone());
        let body_ce = {
            let saved_ev = std::mem::replace(&mut self.current_evidence, acc_evidence_var);
            let saved_k = std::mem::replace(&mut self.current_return_k, inner_k);
            let ce = self.lower_expr(body);
            self.current_return_k = saved_k;
            self.current_evidence = saved_ev;
            ce
        };

        // 4. Wrap inside-out: insert_canonical chain wraps the body, then
        //    the return-K binding (if any) wraps the chain. Outer K binding
        //    sits outermost so its closure value can reference outer evidence
        //    by name (which is in scope at the with site).
        let with_evidence = entry_bindings
            .into_iter()
            .rev()
            .fold(body_ce, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            });
        match ret_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(with_evidence)),
            None => with_evidence,
        }
    }

    /// Dynamic-handler case of [`lower_with`]. The op tuple is a runtime
    /// closure-tuple value (an `Atom` carrying it); we lower it in place and
    /// wrap into `{EffectAtom, OpTuple}` exactly like the static path. The
    /// optional `return_lambda` is wrapped into a continuation closure that
    /// applies the lambda under outer evidence + outer K — same composition
    /// shape as Static's return clause.
    fn lower_with_dynamic(
        &mut self,
        effect: &str,
        op_tuple: &Atom,
        return_lambda: Option<&Atom>,
        body: &MExpr,
    ) -> CExpr {
        let outer_evidence = self.current_evidence.clone();
        let outer_return_k = self.current_return_k.clone();

        let op_tuple_ce = self.lower_atom(op_tuple);

        // Return-lambda composition (built under outer scope).
        let ret_binding: Option<(String, CExpr)> = return_lambda.map(|atom| {
            let lambda_ce = self.lower_atom(atom);
            let v_param = self.fresh_helper_name();
            // The Atom is a uniform-CPS lambda: `fun(value, _Evidence, _ReturnK)`.
            // Wrap as a continuation: `fun(_V) -> apply <lambda>(_V, outer_ev, outer_k)`.
            let wrapper = CExpr::Fun(
                vec![v_param.clone()],
                Box::new(CExpr::Apply(
                    Box::new(lambda_ce),
                    vec![
                        CExpr::Var(v_param),
                        CExpr::Var(outer_evidence.clone()),
                        CExpr::Var(outer_return_k.clone()),
                    ],
                )),
            );
            (self.fresh_k_ret_name(), wrapper)
        });

        let inner_k = ret_binding
            .as_ref()
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| outer_return_k.clone());

        let entry = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom(effect.to_string())),
            op_tuple_ce,
        ]);
        let insert = CExpr::Call(
            EVIDENCE_BRIDGE_MODULE.to_string(),
            "insert_canonical".to_string(),
            vec![CExpr::Var(outer_evidence.clone()), entry],
        );
        let new_ev_name = self.fresh_evidence_name();

        let body_ce = {
            let saved_ev = std::mem::replace(&mut self.current_evidence, new_ev_name.clone());
            let saved_k = std::mem::replace(&mut self.current_return_k, inner_k);
            let ce = self.lower_expr(body);
            self.current_return_k = saved_k;
            self.current_evidence = saved_ev;
            ce
        };

        let with_evidence = CExpr::Let(new_ev_name, Box::new(insert), Box::new(body_ce));
        match ret_binding {
            Some((name, value)) => CExpr::Let(name, Box::new(value), Box::new(with_evidence)),
            None => with_evidence,
        }
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
    fn build_op_tuple_for_effect(&mut self, eff: &str, arms: &[&MHandlerArm]) -> CExpr {
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
                    self.build_arm_closure(g[0])
                } else {
                    self.build_multi_arm_op_closure(&g)
                }
            })
            .collect();

        CExpr::Tuple(closures)
    }

    /// Compile a single `MHandlerArm` into its per-op closure:
    ///
    /// ```text
    /// fun(<arm.params...>, _K_arm{n}) -> <arm.body lowered under _K_arm{n}>
    /// ```
    ///
    /// Each arm param maps to a closure parameter:
    ///   - `Pat::Var { name }` → that name (mangled via `core_var`).
    ///   - non-Var patterns → a positional `_HArg{i}` plus a destructuring
    ///     `case` wrap around the body.
    fn build_arm_closure(&mut self, arm: &MHandlerArm) -> CExpr {
        if arm.finally_block.is_some() {
            // The slow uniform K-threaded path needs a synthetic wrapper K
            // that runs `finally` before forwarding to the captured arm-K.
            // The old lowerer's pattern (`current_handler_finally` set during
            // body lowering, then per-resume try/catch wrap) doesn't map
            // cleanly onto uniform-K because Resume is now just an
            // `apply K_arm`. Sketch from the task brief
            // (`let _R = body in let _ = finally in _R`) collapses K usage
            // into a value form, but `body` doesn't *produce* a value under
            // uniform CPS — it tail-calls `_K_arm`. Flagged for a follow-up
            // step to land alongside finally support.
            panic!(
                "build_arm_closure: finally_block lowering deferred — uniform \
                 K-threaded composition needs a synthetic wrapper K that runs \
                 finally before forwarding; the old lowerer's per-resume \
                 try/catch shape does not transfer directly to the monadic \
                 path. (effect={}, op={})",
                arm.op.effect, arm.op.op
            );
        }

        let (closure_params, body_wraps) = self.plan_arm_params(&arm.params);
        let k_arm = self.fresh_k_arm_name();
        let body_ce = {
            let saved = std::mem::replace(&mut self.current_return_k, k_arm.clone());
            let ce = self.lower_expr(&arm.body);
            self.current_return_k = saved;
            ce
        };
        let body_with_pats = self.wrap_arm_param_destructures(body_ce, body_wraps);

        let mut params = closure_params;
        params.push(k_arm);
        CExpr::Fun(params, Box::new(body_with_pats))
    }

    /// Multi-arm-per-op closure. The op has N>1 arms that pattern-match on
    /// op params; emit:
    ///
    /// ```text
    /// fun(_HArg0, ..., _HArgK, _K_arm{n}) ->
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
    fn build_multi_arm_op_closure(&mut self, arms: &[&MHandlerArm]) -> CExpr {
        let n_params = arms[0].params.len();
        for arm in arms.iter().skip(1) {
            if arm.finally_block.is_some() {
                panic!(
                    "build_multi_arm_op_closure: finally_block deferred (effect={}, op={})",
                    arm.op.effect, arm.op.op
                );
            }
            assert_eq!(
                arm.params.len(),
                n_params,
                "multi-arm-per-op: all arms must take the same number of op params \
                 (effect={}, op={})",
                arm.op.effect,
                arm.op.op
            );
        }
        if arms[0].finally_block.is_some() {
            panic!(
                "build_multi_arm_op_closure: finally_block deferred (effect={}, op={})",
                arms[0].op.effect, arms[0].op.op
            );
        }

        let positional: Vec<String> = (0..n_params).map(|i| format!("_HArg{}", i)).collect();
        let k_arm = self.fresh_k_arm_name();

        let scrutinee = if n_params == 1 {
            CExpr::Var(positional[0].clone())
        } else {
            CExpr::Values(positional.iter().cloned().map(CExpr::Var).collect())
        };

        let mut case_arms: Vec<CArm> = Vec::with_capacity(arms.len());
        for arm in arms {
            let body_ce = {
                let saved = std::mem::replace(&mut self.current_return_k, k_arm.clone());
                let ce = self.lower_expr(&arm.body);
                self.current_return_k = saved;
                ce
            };
            let pat = if n_params == 1 {
                lower_pat(&arm.params[0], self.ctors)
            } else {
                CPat::Values(
                    arm.params
                        .iter()
                        .map(|p| lower_pat(p, self.ctors))
                        .collect(),
                )
            };
            case_arms.push(CArm {
                pat,
                guard: None,
                body: body_ce,
            });
        }

        let mut fun_params = positional;
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
    fn build_return_clause_closure(&mut self, arm: &MHandlerArm) -> CExpr {
        if arm.finally_block.is_some() {
            panic!(
                "build_return_clause_closure: finally_block on a return clause is unusual; \
                 deferred until needed (effect={}, op={})",
                arm.op.effect, arm.op.op
            );
        }
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

        // Body lowers under the outer K + outer evidence (the lowerer state
        // is still pointing there when this is called — see lower_with_static).
        let body_ce = self.lower_expr(&arm.body);
        let body_with_pat = match body_wrap {
            None => body_ce,
            Some(pat) => {
                let cpat = lower_pat(&pat, self.ctors);
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
    fn wrap_arm_param_destructures(
        &self,
        mut body: CExpr,
        wraps: Vec<(String, Pat)>,
    ) -> CExpr {
        for (arg_name, pat) in wraps.into_iter().rev() {
            let cpat = lower_pat(&pat, self.ctors);
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
