//! Trait-specialization stats.
//!
//! Per-module counts of trait dictionary-method dispatch sites that were
//! specialized to a direct call (`__saga_dictmethod_*`) versus left on the
//! runtime `element/2` dict-passing path, with a reason for each fallback.
//! This is the direct-first analog of the old `--monadic-stats`: it measures
//! backend truth (what lowering actually decided), so we can confirm — as each
//! phase lands — that we are replacing dict passing with direct calls, and see
//! at a glance what is still on the slow path and why.
//!
//! Enable with `SAGA_STATS=trait-spec` (or `1`/`all`, or a module-name
//! substring filter). The report prints to stderr at the end of lowering each
//! module, so any command that lowers (`emit`/`build`/`run`) shows it.

use crate::ast::NodeId;
use std::collections::{BTreeMap, HashMap, HashSet};

/// Why a statically-known (`KnownImpl`) dispatch site stayed on the
/// `element/2` dict-passing path instead of specializing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FallbackReason {
    /// Dict constructor is not a locally-hoisted method (imported dict).
    /// Resolved by Phase 3 (cross-module method facts).
    Imported,
    /// Parameterized impl: the call passes sub-dictionaries. Later phase.
    Parameterized,
    /// Partial application: supplied args != the method's user arity.
    Unsaturated,
    /// The call site's pure/CPS shape disagreed with the planned method ABI.
    /// Should be rare; surfaced because it signals a classifier/lowerer
    /// inconsistency rather than an expected not-yet-supported shape.
    AbiMismatch,
}

impl FallbackReason {
    fn label(self) -> &'static str {
        match self {
            FallbackReason::Imported => "imported",
            FallbackReason::Parameterized => "parameterized",
            FallbackReason::Unsaturated => "unsaturated",
            FallbackReason::AbiMismatch => "abi-mismatch",
        }
    }
}

/// Per-module specialization outcomes, keyed by dispatch-site App `NodeId` so
/// repeated visits to the same site (e.g. nested lowering) do not double-count.
#[derive(Default)]
pub(crate) struct TraitSpecStats {
    specialized: HashSet<NodeId>,
    fell_back: HashMap<NodeId, FallbackReason>,
}

impl TraitSpecStats {
    pub(crate) fn clear(&mut self) {
        self.specialized.clear();
        self.fell_back.clear();
    }

    pub(crate) fn record_specialized(&mut self, app_id: NodeId) {
        self.fell_back.remove(&app_id);
        self.specialized.insert(app_id);
    }

    pub(crate) fn record_fallback(&mut self, app_id: NodeId, reason: FallbackReason) {
        // A site proven specializable elsewhere wins over a speculative miss.
        if !self.specialized.contains(&app_id) {
            self.fell_back.insert(app_id, reason);
        }
    }

    /// One-line summary: known sites, specialized, fell back (+ reason breakdown).
    pub(crate) fn report(&self, subject: &str) -> String {
        let specialized = self.specialized.len();
        let fell_back = self.fell_back.len();
        let known = specialized + fell_back;
        let mut out = format!(
            "trait-spec[{subject}]: {known} known site(s) | {specialized} specialized | {fell_back} fell back"
        );
        if fell_back > 0 {
            let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
            for reason in self.fell_back.values() {
                *counts.entry(reason.label()).or_default() += 1;
            }
            let parts: Vec<String> = counts
                .iter()
                .map(|(label, n)| format!("{n} {label}"))
                .collect();
            out.push_str(&format!(" ({})", parts.join(", ")));
        }
        out
    }
}

/// Whether `SAGA_STATS` requests the trait-spec report for this module.
pub(crate) fn stats_enabled_for(subject: &str) -> bool {
    let Some(value) = std::env::var_os("SAGA_STATS") else {
        return false;
    };
    let value = value.to_string_lossy();
    let value = value.trim();
    value.is_empty()
        || matches!(value, "1" | "true" | "all")
        || value.contains("trait-spec")
        || subject.contains(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_report_has_no_breakdown() {
        let stats = TraitSpecStats::default();
        assert_eq!(
            stats.report("M"),
            "trait-spec[M]: 0 known site(s) | 0 specialized | 0 fell back"
        );
    }

    #[test]
    fn report_counts_known_specialized_and_fallback_reasons() {
        let mut stats = TraitSpecStats::default();
        stats.record_specialized(NodeId(1));
        stats.record_specialized(NodeId(2));
        stats.record_fallback(NodeId(3), FallbackReason::Imported);
        stats.record_fallback(NodeId(4), FallbackReason::Imported);
        stats.record_fallback(NodeId(5), FallbackReason::Parameterized);
        assert_eq!(
            stats.report("M"),
            "trait-spec[M]: 5 known site(s) | 2 specialized | 3 fell back (2 imported, 1 parameterized)"
        );
    }

    #[test]
    fn specialized_wins_over_a_prior_fallback_for_the_same_site() {
        // A speculative miss on one lowering path must not count against a site
        // that specializes on another path (keyed by App NodeId).
        let mut stats = TraitSpecStats::default();
        stats.record_fallback(NodeId(1), FallbackReason::AbiMismatch);
        stats.record_specialized(NodeId(1));
        assert_eq!(
            stats.report("M"),
            "trait-spec[M]: 1 known site(s) | 1 specialized | 0 fell back"
        );
    }

    #[test]
    fn repeated_records_for_one_site_do_not_double_count() {
        let mut stats = TraitSpecStats::default();
        stats.record_specialized(NodeId(1));
        stats.record_specialized(NodeId(1));
        stats.record_fallback(NodeId(2), FallbackReason::Imported);
        stats.record_fallback(NodeId(2), FallbackReason::Imported);
        assert_eq!(
            stats.report("M"),
            "trait-spec[M]: 2 known site(s) | 1 specialized | 1 fell back (1 imported)"
        );
    }
}
