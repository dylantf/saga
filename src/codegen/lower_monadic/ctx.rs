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

use std::collections::BTreeSet;

use crate::ast::Pat;

use super::exprs;
use super::pats::pat_bound_names;

/// Runtime delimiter/prompt that should be re-entered by continuations captured
/// inside a `with` body. Ordinary evaluation is still wrapped at the `with`
/// site, but resumptions call bind continuations directly; carrying this lets
/// those continuation bodies reinstall the same delimiter.
#[derive(Clone)]
pub(crate) struct ResultDelimiter {
    pub effects: Vec<String>,
    pub abort_marker: String,
    pub return_k: String,
    pub preserve_abort_marker: bool,
    pub parent: Option<Box<ResultDelimiter>>,
}

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

    /// Marker for aborting handler arms at the current `with` delimiter.
    /// Non-resuming arms wrap their result with this marker so nested `with`
    /// boundaries can propagate the abort until the owning delimiter unwraps
    /// it. This keeps outer return clauses from treating abort values as
    /// successful inner results.
    pub abort_marker: Option<String>,

    /// `Some(finally_block)` while lowering a handler arm body that has a
    /// `finally` clause. `lower_resume` sequences this cleanup after the
    /// delimited resume continuation returns, while preserving the resume
    /// site's lexical scope for values captured by the cleanup block.
    pub finally_block: Option<Box<crate::codegen::monadic::ir::MExpr>>,

    /// Preserve abort tuples instead of unwrapping the current delimiter's
    /// marker through `return_k`. Used by value-position binds, whose local
    /// success continuation must not turn aborting handler arms into ordinary
    /// argument values.
    pub preserve_abort_marker: bool,

    /// Active with-body delimiter to wrap bind-continuation bodies with. This
    /// is separate from `abort_marker`, which belongs to handler arm bodies.
    pub result_delimiter: Option<ResultDelimiter>,

    /// Source-level names bound in the current lexical scope.
    ///
    /// The backend resolution map is keyed by original AST node ids and may
    /// still contain top-level/import resolutions for names that are later
    /// shadowed by ANF/monadic binders. Local binders must win before those
    /// resolved symbols are considered.
    pub locals: BTreeSet<String>,
}

impl LowerCtx {
    /// Context at the entry of a fresh function/lambda/letfun body.
    pub fn fresh() -> Self {
        Self {
            return_k: exprs::RETURN_K_VAR.to_string(),
            evidence: exprs::EVIDENCE_VAR.to_string(),
            arm_k: None,
            abort_marker: None,
            finally_block: None,
            preserve_abort_marker: false,
            result_delimiter: None,
            locals: BTreeSet::new(),
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

    /// Clone + set the current handler-abort marker.
    pub fn with_abort_marker(&self, marker: String) -> Self {
        Self {
            abort_marker: Some(marker),
            ..self.clone()
        }
    }

    /// Clone + set `finally_block`.
    pub fn with_finally(&self, block: Box<crate::codegen::monadic::ir::MExpr>) -> Self {
        Self {
            finally_block: Some(block),
            ..self.clone()
        }
    }

    /// Clone + clear `finally_block`.
    pub fn without_finally(&self) -> Self {
        Self {
            finally_block: None,
            ..self.clone()
        }
    }

    /// Clone + set whether current `with` delimiters should preserve abort
    /// tuples for a surrounding value-position binder.
    pub fn with_preserve_abort_marker(&self, preserve_abort_marker: bool) -> Self {
        Self {
            preserve_abort_marker,
            ..self.clone()
        }
    }

    /// Clone + install the with-body delimiter that captured bind
    /// continuations should re-enter.
    pub fn with_result_delimiter(
        &self,
        effects: Vec<String>,
        abort_marker: String,
        return_k: String,
        preserve_abort_marker: bool,
    ) -> Self {
        Self {
            result_delimiter: Some(ResultDelimiter {
                effects,
                abort_marker,
                return_k,
                preserve_abort_marker,
                parent: self.result_delimiter.clone().map(Box::new),
            }),
            ..self.clone()
        }
    }

    /// Clone + clear the active with-body delimiter. Handler arm bodies use the
    /// outer evidence and K, but they are not lexically part of the handled body
    /// whose prompt captured resumptions must re-enter.
    pub fn without_result_delimiter(&self) -> Self {
        Self {
            result_delimiter: None,
            ..self.clone()
        }
    }

    /// Clone + add one source-level local binding.
    pub fn with_local(&self, name: impl Into<String>) -> Self {
        let mut next = self.clone();
        next.locals.insert(name.into());
        next
    }

    /// Clone + add many source-level local bindings.
    pub fn with_locals<I>(&self, names: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        let mut next = self.clone();
        next.locals.extend(names);
        next
    }

    /// Clone + add every variable bound by a pattern.
    pub fn with_pat_locals(&self, pat: &Pat) -> Self {
        self.with_locals(pat_bound_names(pat))
    }

    /// Clone + add every variable bound by a parameter/pattern list.
    pub fn with_param_locals(&self, params: &[Pat]) -> Self {
        let mut names = Vec::new();
        for pat in params {
            names.extend(pat_bound_names(pat));
        }
        self.with_locals(names)
    }
}
