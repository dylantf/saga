//! Compile-time helpers for emitting evidence-vector operations in Core Erlang.
//!
//! The evidence vector is a Core Erlang tuple of per-effect entries. Initial
//! layouts are canonical; call boundaries may reshape them into a positional
//! callee prefix followed by an unselected tagged tail:
//!
//! ```text
//!   { {'Std.Fail.Fail',  {FailHandler}},
//!     {'Std.IO.Stdio',   {EprintHandler, PrintHandler, ReadHandler}},
//!     {'Std.State.State', {GetHandler, PutHandler}} }
//! ```
//!
//! Each entry is `{EffectAtom, OpTuple}`. Within each `OpTuple`, op closures
//! are sorted alphabetically by op name (this is already guaranteed by
//! `lower_handler_def_to_tuple`). Op closures themselves keep the same shape
//! as today — `fun(Args..., K) -> ...`.
//!
//! ## Static vs runtime helpers
//!
//! - **Closed rows** (the layout is statically known at lowering time): use
//!   [`evidence_index_of`] to compute a 1-based tuple index, then emit
//!   `erlang:element/2` calls inline. No bridge call needed.
//! - **Open rows** (row-polymorphic evidence flowing through): use
//!   [`reframe_evidence`] to select the callee prefix and retain the tail;
//!   [`find_evidence`], [`insert_canonical`], and [`project_evidence`] emit the
//!   other runtime bridge operations. Bodies are O(n) linear over the tuple;
//!   n is typically ≤5.

use super::util::cerl_call;
use crate::codegen::cerl::{CExpr, CLit};

const EVIDENCE_BRIDGE_MODULE: &str = "std_evidence_bridge";

/// Records the canonical-ordered effect tags for a known-shape evidence
/// vector at a specific lowering point. Used by closed-row callers to look
/// up static positions for `element/2` emission.
#[derive(Debug, Clone, Default)]
pub(super) struct EvidenceLayout {
    /// Effect tags in canonical (alphabetical, deduplicated) order.
    tags: Vec<String>,
}

impl EvidenceLayout {
    pub(super) fn new<I, S>(tags: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut tags: Vec<String> = tags.into_iter().map(Into::into).collect();
        tags.sort();
        tags.dedup();
        Self { tags }
    }

    pub(super) fn tags(&self) -> &[String] {
        &self.tags
    }
}

/// Compile-time tuple index for `tag` in `layout`. Returns a 1-based index
/// suitable for direct use with `erlang:element/2`. Panics if the tag is
/// not present — callers must only ask for tags they know are in scope.
pub(super) fn evidence_index_of(layout: &EvidenceLayout, tag: &str) -> usize {
    match layout.tags.iter().position(|t| t == tag) {
        Some(i) => i + 1,
        None => panic!(
            "evidence layout {:?} does not contain tag '{}'",
            layout.tags, tag
        ),
    }
}

/// Build a single `{EffectAtom, OpTuple}` Core Erlang tuple. `op_closures`
/// must already be sorted alphabetically by op name; today's
/// `lower_handler_def_to_tuple` produces them in that order.
pub(super) fn build_evidence_entry(tag: &str, op_closures: Vec<CExpr>) -> CExpr {
    CExpr::Tuple(vec![
        CExpr::Lit(CLit::Atom(tag.to_string())),
        CExpr::Tuple(op_closures),
    ])
}

/// Emit a runtime canonical-insert. The bridge walks the source tuple,
/// builds a new tuple with `new_entry` at its canonical position, and
/// replaces an existing entry whose tag matches (innermost-wins).
///
/// For closed-row sites where the layout is known statically, callers
/// should build the new tuple inline instead of going through this helper.
pub(super) fn insert_canonical(evidence: CExpr, new_entry: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "insert_canonical",
        vec![evidence, new_entry],
    )
}

/// Install an entry into the canonical static prefix of an open evidence
/// frame without reordering its unknown tagged tail.
pub(super) fn insert_static(evidence: CExpr, static_count: usize, new_entry: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "insert_static",
        vec![
            evidence,
            CExpr::Lit(CLit::Int(static_count as i64)),
            new_entry,
        ],
    )
}

/// Emit a runtime tag lookup. Returns the `OpTuple` for the entry whose tag
/// equals `tag`. Used on open-row paths; closed-row sites compute the static
/// index via [`evidence_index_of`] and emit `element/2` directly.
pub(super) fn find_evidence(evidence: CExpr, tag: &str) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "find_evidence",
        vec![evidence, CExpr::Lit(CLit::Atom(tag.to_string()))],
    )
}

/// Emit a runtime projection: build a new tuple containing only the
/// `{Tag, OpTuple}` entries for the named tags, in canonical order. Used
/// for closed-row narrowing at call boundaries when the source evidence
/// shape is not known statically.
pub(super) fn project_evidence(evidence: CExpr, tags: &[&str]) -> CExpr {
    let mut sorted: Vec<&str> = tags.to_vec();
    sorted.sort();
    sorted.dedup();
    let tag_list = sorted.into_iter().rev().fold(CExpr::Nil, |tail, tag| {
        CExpr::Cons(
            Box::new(CExpr::Lit(CLit::Atom(tag.to_string()))),
            Box::new(tail),
        )
    });
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "project_evidence",
        vec![evidence, tag_list],
    )
}

/// Select a closed callee frame using the same position/tag selector language
/// as [`reframe_evidence`], but drop every unselected caller entry. This is
/// required when a closed CPS function value is passed through an open-row
/// callback ABI: the HOF's open tail must not leak into the closed function.
pub(super) fn select_evidence(evidence: CExpr, selectors: Vec<CExpr>) -> CExpr {
    let selectors = selectors
        .into_iter()
        .rev()
        .fold(CExpr::Nil, |tail, selector| {
            CExpr::Cons(Box::new(selector), Box::new(tail))
        });
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "select_evidence",
        vec![evidence, selectors],
    )
}

/// Reshape evidence for an open-row callee. Integer selectors address the
/// caller's positional static prefix; tag selectors select a concrete applied
/// effect from its forwarded tail.
pub(super) fn reframe_evidence(
    evidence: CExpr,
    static_count: usize,
    selectors: Vec<CExpr>,
) -> CExpr {
    let selectors = selectors
        .into_iter()
        .rev()
        .fold(CExpr::Nil, |tail, selector| {
            CExpr::Cons(Box::new(selector), Box::new(tail))
        });
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "reframe_evidence",
        vec![
            evidence,
            CExpr::Lit(CLit::Int(static_count as i64)),
            selectors,
        ],
    )
}

/// Combine handler-supplied callback evidence with the unknown tail captured
/// at the original effect-operation call site. The call-time frame remains the
/// positional static prefix and is relabeled to `static_tags`; exact entries
/// replaced at call time are omitted from the captured frame while independent
/// tail entries are appended.
pub(super) fn append_tail(
    call_evidence: CExpr,
    captured_evidence: CExpr,
    static_tags: &[String],
) -> CExpr {
    let tag_list = static_tags.iter().rev().fold(CExpr::Nil, |tail, tag| {
        CExpr::Cons(
            Box::new(CExpr::Lit(CLit::Atom(tag.clone()))),
            Box::new(tail),
        )
    });
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "append_tail",
        vec![call_evidence, captured_evidence, tag_list],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_closure(name: &str) -> CExpr {
        CExpr::Var(name.to_string())
    }

    #[test]
    fn layout_sorts_and_dedups() {
        let layout = EvidenceLayout::new([
            "Std.IO.Stdio".to_string(),
            "Std.Fail.Fail".to_string(),
            "Std.IO.Stdio".to_string(),
        ]);
        assert_eq!(layout.tags(), &["Std.Fail.Fail", "Std.IO.Stdio"]);
    }

    #[test]
    fn index_of_is_one_based() {
        let layout = EvidenceLayout::new([
            "Std.IO.Stdio".to_string(),
            "Std.Fail.Fail".to_string(),
            "Std.State.State".to_string(),
        ]);
        assert_eq!(evidence_index_of(&layout, "Std.Fail.Fail"), 1);
        assert_eq!(evidence_index_of(&layout, "Std.IO.Stdio"), 2);
        assert_eq!(evidence_index_of(&layout, "Std.State.State"), 3);
    }

    #[test]
    #[should_panic(expected = "does not contain tag")]
    fn index_of_panics_on_missing_tag() {
        let layout = EvidenceLayout::new(["Std.Fail.Fail".to_string()]);
        let _ = evidence_index_of(&layout, "Std.IO.Stdio");
    }

    #[test]
    fn build_entry_shape() {
        let entry = build_evidence_entry(
            "Std.IO.Stdio",
            vec![
                dummy_closure("Eprint"),
                dummy_closure("Print"),
                dummy_closure("Read"),
            ],
        );
        let CExpr::Tuple(top) = entry else {
            panic!("expected outer tuple")
        };
        assert_eq!(top.len(), 2);
        match &top[0] {
            CExpr::Lit(CLit::Atom(a)) => assert_eq!(a, "Std.IO.Stdio"),
            other => panic!("expected tag atom, got {:?}", other),
        }
        match &top[1] {
            CExpr::Tuple(ops) => {
                assert_eq!(ops.len(), 3);
                let names: Vec<&str> = ops
                    .iter()
                    .map(|e| match e {
                        CExpr::Var(v) => v.as_str(),
                        _ => panic!("expected var closure"),
                    })
                    .collect();
                assert_eq!(names, vec!["Eprint", "Print", "Read"]);
            }
            other => panic!("expected op tuple, got {:?}", other),
        }
    }

    #[test]
    fn insert_canonical_is_bridge_call() {
        let ev = CExpr::Var("_Evidence".to_string());
        let entry = build_evidence_entry("Std.Fail.Fail", vec![dummy_closure("Fail")]);
        let call = insert_canonical(ev, entry);
        match call {
            CExpr::Call(m, f, args) => {
                assert_eq!(m, "std_evidence_bridge");
                assert_eq!(f, "insert_canonical");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], CExpr::Var(v) if v == "_Evidence"));
                assert!(matches!(&args[1], CExpr::Tuple(_)));
            }
            other => panic!("expected bridge call, got {:?}", other),
        }
    }

    #[test]
    fn insert_static_is_bridge_call_with_prefix_size() {
        let entry = build_evidence_entry("Router.Skip", vec![dummy_closure("Skip")]);
        let call = insert_static(CExpr::Var("_Evidence".to_string()), 1, entry);
        let CExpr::Call(module, function, args) = call else {
            panic!("expected bridge call")
        };
        assert_eq!(module, "std_evidence_bridge");
        assert_eq!(function, "insert_static");
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[1], CExpr::Lit(CLit::Int(1))));
    }

    #[test]
    fn find_evidence_is_bridge_call_with_tag_atom() {
        let ev = CExpr::Var("_Evidence".to_string());
        let call = find_evidence(ev, "Std.State.State");
        match call {
            CExpr::Call(m, f, args) => {
                assert_eq!(m, "std_evidence_bridge");
                assert_eq!(f, "find_evidence");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], CExpr::Var(v) if v == "_Evidence"));
                match &args[1] {
                    CExpr::Lit(CLit::Atom(a)) => assert_eq!(a, "Std.State.State"),
                    other => panic!("expected tag atom, got {:?}", other),
                }
            }
            other => panic!("expected bridge call, got {:?}", other),
        }
    }

    #[test]
    fn project_evidence_emits_sorted_tag_list() {
        let ev = CExpr::Var("_Evidence".to_string());
        let call = project_evidence(ev, &["Std.IO.Stdio", "Std.Fail.Fail", "Std.IO.Stdio"]);
        let CExpr::Call(m, f, args) = call else {
            panic!("expected bridge call")
        };
        assert_eq!(m, "std_evidence_bridge");
        assert_eq!(f, "project_evidence");
        assert_eq!(args.len(), 2);
        // Walk the cons list and collect tag atoms in order.
        let mut node = &args[1];
        let mut tags: Vec<String> = Vec::new();
        loop {
            match node {
                CExpr::Cons(h, t) => {
                    match h.as_ref() {
                        CExpr::Lit(CLit::Atom(a)) => tags.push(a.clone()),
                        other => panic!("expected atom in cons, got {:?}", other),
                    }
                    node = t.as_ref();
                }
                CExpr::Nil => break,
                other => panic!("expected cons or nil, got {:?}", other),
            }
        }
        assert_eq!(tags, vec!["Std.Fail.Fail", "Std.IO.Stdio"]);
    }

    #[test]
    fn project_evidence_with_empty_tags_yields_nil_list() {
        let ev = CExpr::Var("_Evidence".to_string());
        let call = project_evidence(ev, &[]);
        let CExpr::Call(_, _, args) = call else {
            panic!("expected bridge call")
        };
        assert!(matches!(&args[1], CExpr::Nil));
    }

    #[test]
    fn reframe_evidence_preserves_selector_order() {
        let call = reframe_evidence(
            CExpr::Var("_Evidence".to_string()),
            2,
            vec![
                CExpr::Lit(CLit::Int(2)),
                CExpr::Lit(CLit::Atom("Repo<UsersDb>".to_string())),
            ],
        );
        let CExpr::Call(module, function, args) = call else {
            panic!("expected bridge call")
        };
        assert_eq!(module, "std_evidence_bridge");
        assert_eq!(function, "reframe_evidence");
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[1], CExpr::Lit(CLit::Int(2))));
        let CExpr::Cons(first, rest) = &args[2] else {
            panic!("expected selector list")
        };
        assert!(matches!(first.as_ref(), CExpr::Lit(CLit::Int(2))));
        let CExpr::Cons(second, tail) = rest.as_ref() else {
            panic!("expected second selector")
        };
        assert!(matches!(
            second.as_ref(),
            CExpr::Lit(CLit::Atom(tag)) if tag == "Repo<UsersDb>"
        ));
        assert!(matches!(tail.as_ref(), CExpr::Nil));
    }

    #[test]
    fn select_evidence_preserves_selector_order() {
        let call = select_evidence(
            CExpr::Var("_Evidence".to_string()),
            vec![
                CExpr::Lit(CLit::Int(2)),
                CExpr::Lit(CLit::Atom("Repo<UsersDb>".to_string())),
            ],
        );
        let CExpr::Call(module, function, args) = call else {
            panic!("expected bridge call")
        };
        assert_eq!(module, "std_evidence_bridge");
        assert_eq!(function, "select_evidence");
        assert_eq!(args.len(), 2);
        let CExpr::Cons(first, rest) = &args[1] else {
            panic!("expected selector list")
        };
        assert!(matches!(first.as_ref(), CExpr::Lit(CLit::Int(2))));
        let CExpr::Cons(second, tail) = rest.as_ref() else {
            panic!("expected second selector")
        };
        assert!(matches!(
            second.as_ref(),
            CExpr::Lit(CLit::Atom(tag)) if tag == "Repo<UsersDb>"
        ));
        assert!(matches!(tail.as_ref(), CExpr::Nil));
    }

    #[test]
    fn append_tail_is_bridge_call() {
        let call = append_tail(
            CExpr::Var("CallEvidence".to_string()),
            CExpr::Var("CapturedEvidence".to_string()),
            &["Abort<String>".to_string(), "Repo".to_string()],
        );
        let CExpr::Call(module, function, args) = call else {
            panic!("expected bridge call")
        };
        assert_eq!(module, "std_evidence_bridge");
        assert_eq!(function, "append_tail");
        assert_eq!(args.len(), 3);
    }

    #[test]
    fn build_entry_with_empty_ops_is_legal() {
        // An effect with no live ops at the moment (degenerate but representable).
        let entry = build_evidence_entry("Std.Fail.Fail", vec![]);
        let CExpr::Tuple(top) = entry else {
            panic!("expected tuple")
        };
        assert_eq!(top.len(), 2);
        match &top[1] {
            CExpr::Tuple(ops) => assert!(ops.is_empty()),
            other => panic!("expected empty op tuple, got {:?}", other),
        }
    }

    #[test]
    fn build_entry_atom_uses_tag_unmangled() {
        // Evidence tags are canonical effect names emitted as-is; they must
        // not be lowercase-mangled like constructor atoms.
        let entry = build_evidence_entry("Std.Fail.Fail", vec![dummy_closure("F")]);
        let CExpr::Tuple(top) = entry else { panic!() };
        match &top[0] {
            CExpr::Lit(CLit::Atom(a)) => assert_eq!(a, "Std.Fail.Fail"),
            other => panic!("expected unmangled tag atom, got {:?}", other),
        }
    }
}
