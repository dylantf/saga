//! Per-derivation lowering context, threaded by `&LowerCtx` through every
//! `lower_*` method that reads continuation-flavored state.
//!
//! Replaces the ambient mutable fields (`current_return_k`,
//! `current_evidence`, `current_arm_k`) that used to live on `Lowerer`.
//! Counters (`k_counter`, `ev_counter`, …) remain on `Lowerer` — they need
//! monotonic uniqueness across a function body and must NOT be moved here.
//!
//! See `docs/planning/uniform-effect-translation/lowerer-state-refactor.md`
//! for the design rationale (step 1).

use super::exprs;

/// Immutable per-derivation lowering context.
///
/// Cloning three short strings per `Bind` / `With` / arm derivation is cheap
/// compared to the CExpr nodes being built. Carrying this by value (rather
/// than mutating fields on the lowerer + save/restore) keeps the distinct
/// continuation roles (`Pure` target vs. `Resume` target) from collapsing
/// into a single slot.
#[derive(Clone)]
pub(crate) struct LowerCtx {
    /// What `Pure(v)` applies — the "tail" target of the current
    /// computation. Defaults to `_ReturnK` at function entry. Rebound to a
    /// fresh `_K{n}` by `Bind`.
    pub return_k: String,

    /// In-scope evidence vector variable. Defaults to `_Evidence` at
    /// function entry. Rebound to `_Ev{n}` inside a `With` body.
    pub evidence: String,

    /// `Some(perform_site_k)` while lowering a handler arm body. `None`
    /// outside an arm. `Resume(v)` applies this K when set.
    pub arm_k: Option<String>,
}

impl LowerCtx {
    /// Context at the entry of a fresh function/lambda/letfun body.
    pub fn fresh() -> Self {
        Self {
            return_k: exprs::RETURN_K_VAR.to_string(),
            evidence: exprs::EVIDENCE_VAR.to_string(),
            arm_k: None,
        }
    }

    /// Clone + override `return_k`.
    pub fn with_return_k(&self, k: String) -> Self {
        Self {
            return_k: k,
            ..self.clone()
        }
    }

    /// Clone + override `evidence`.
    pub fn with_evidence(&self, e: String) -> Self {
        Self {
            evidence: e,
            ..self.clone()
        }
    }

    /// Clone + override `arm_k` (set to `Some(k)`).
    pub fn with_arm_k(&self, k: String) -> Self {
        Self {
            arm_k: Some(k),
            ..self.clone()
        }
    }
}
