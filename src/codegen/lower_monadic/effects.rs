//! Effect-machinery lowering for the new monadic lowerer (sub-step 7d).
//!
//! Implements `MExpr::Yield` and `MExpr::With` in the **uniform open-row
//! shape**: every yield goes through `std_evidence_bridge:find_evidence/2`
//! at runtime (no closed-row specialization). The `Resume` variant is
//! handler-arm-body territory and lands in sub-step 7e — it still panics
//! from `exprs.rs`.
//!
//! See:
//!   - `docs/effect-implementation.md` — runtime evidence layout and the
//!     `find_evidence` / `insert_canonical` ABI.
//!   - `src/codegen/lower/evidence.rs` — the same helpers used by the old
//!     lowerer (allowlisted module; we emit the same bridge calls inline
//!     here to avoid the per-call branching the old path carries).
//!   - `docs/planning/uniform-effect-translation/monadic-ir-spec.md` —
//!     `MExpr::Yield`, `MExpr::With`, `MHandler` variants.

use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::monadic::ir::{Atom, EffectOpRef, MExpr, MHandler, MHandlerArm};

use super::Lowerer;

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
            MHandler::Static { effects, arms, .. } => {
                self.lower_with_static(effects, arms, body)
            }
            MHandler::Dynamic {
                effects, op_tuple, ..
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
                self.lower_with_dynamic(&effects[0], op_tuple, body)
            }
        }
    }

    /// Static-handler case of [`lower_with`]. For each effect handled, build
    /// `{EffectAtom, OpTuple}` from the matching arms (sorted by canonical
    /// op index) and chain `insert_canonical` calls; finally lower the body
    /// under the extended evidence.
    fn lower_with_static(
        &mut self,
        effects: &[String],
        arms: &[MHandlerArm],
        body: &MExpr,
    ) -> CExpr {
        // Build (new_ev_name, ev_value_expr) pairs threaded through
        // insert_canonical. Each step binds a fresh `_Ev{n}` to the result
        // of `insert_canonical(<prev_ev>, {EffectAtom, OpTuple})`.
        let mut acc_evidence_var = self.current_evidence.clone();
        let mut wrappers: Vec<(String, CExpr)> = Vec::with_capacity(effects.len());

        for eff in effects {
            let mut effect_arms: Vec<&MHandlerArm> =
                arms.iter().filter(|a| a.op.effect == *eff).collect();
            // Canonical OpTuple ordering — by 1-based op_index, which the
            // translator computes from the alphabetical op name order.
            effect_arms.sort_by_key(|a| a.op.op_index);

            let op_closures: Vec<CExpr> = effect_arms
                .iter()
                .map(|arm| stub_arm_closure(arm))
                .collect();

            // {EffectAtom, OpTuple}
            let entry = CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom(eff.clone())),
                CExpr::Tuple(op_closures),
            ]);

            let insert = CExpr::Call(
                EVIDENCE_BRIDGE_MODULE.to_string(),
                "insert_canonical".to_string(),
                vec![CExpr::Var(acc_evidence_var.clone()), entry],
            );

            let new_name = self.fresh_evidence_name();
            wrappers.push((new_name.clone(), insert));
            acc_evidence_var = new_name;
        }

        let body_ce = {
            let saved = std::mem::replace(&mut self.current_evidence, acc_evidence_var);
            let ce = self.lower_expr(body);
            self.current_evidence = saved;
            ce
        };

        // Wrap inside-out so the outermost `let` binds the first evidence
        // extension and the body sees the innermost.
        wrappers
            .into_iter()
            .rev()
            .fold(body_ce, |inner, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(inner))
            })
    }

    /// Dynamic-handler case of [`lower_with`]. The op tuple is already a
    /// runtime closure-tuple value (an `Atom` carrying it), so we lower it
    /// in place and wrap into `{EffectAtom, OpTuple}` exactly like the
    /// static path. The optional `return_lambda` is irrelevant for
    /// evidence-insert (it composes with arm bodies in 7e).
    fn lower_with_dynamic(&mut self, effect: &str, op_tuple: &Atom, body: &MExpr) -> CExpr {
        let op_tuple_ce = self.lower_atom(op_tuple);

        let entry = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom(effect.to_string())),
            op_tuple_ce,
        ]);
        let insert = CExpr::Call(
            EVIDENCE_BRIDGE_MODULE.to_string(),
            "insert_canonical".to_string(),
            vec![CExpr::Var(self.current_evidence.clone()), entry],
        );
        let new_name = self.fresh_evidence_name();

        let body_ce = {
            let saved = std::mem::replace(&mut self.current_evidence, new_name.clone());
            let ce = self.lower_expr(body);
            self.current_evidence = saved;
            ce
        };

        CExpr::Let(new_name, Box::new(insert), Box::new(body_ce))
    }
}

// STUB (7d): arm closures emit placeholder body. 7e replaces with the real
// handler-arm lowering (which threads `resume`, the arm-K, and the handler's
// return clause).
fn stub_arm_closure(arm: &MHandlerArm) -> CExpr {
    let mut params: Vec<String> = (0..arm.params.len())
        .map(|i| format!("_StubArg{}", i))
        .collect();
    params.push("_StubK".to_string());
    let body = CExpr::Apply(
        Box::new(CExpr::Var("_StubK".to_string())),
        vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
    );
    CExpr::Fun(params, Box::new(body))
}
