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
//!   `EvidenceAbi::resolve_slot` to obtain a 1-based tuple index, then emit
//!   `erlang:element/2` calls inline. No bridge call needed.
//! - **Open rows** (row-polymorphic evidence flowing through): use
//!   [`reframe_evidence`] to select the callee prefix and retain the tail;
//!   [`find_evidence`] and [`insert_canonical`] emit the other runtime bridge
//!   operations. Bodies are O(n) linear over the tuple;
//!   n is typically ≤5.

use super::util::cerl_call;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::runtime_shape::{
    EvidenceAbi, EvidenceInstallKind, EvidenceInstallPlan, EvidenceReframeKind,
    EvidenceReframePlan, EvidenceSelector,
};

const EVIDENCE_BRIDGE_MODULE: &str = "std_evidence_bridge";

/// A Core Erlang variable carrying evidence with one authoritative ABI.
#[derive(Debug, Clone)]
pub(crate) struct EvidenceFrame {
    pub(super) var: String,
    pub(super) abi: EvidenceAbi,
}

impl EvidenceFrame {
    pub(super) fn new(var: impl Into<String>, abi: EvidenceAbi) -> Self {
        Self {
            var: var.into(),
            abi,
        }
    }
}

fn lower_selector(selector: &EvidenceSelector) -> CExpr {
    match selector {
        EvidenceSelector::Position(position) => CExpr::Lit(CLit::Int(*position as i64)),
        EvidenceSelector::DynamicTag(tag) => CExpr::Lit(CLit::Atom(tag.clone())),
    }
}

pub(super) fn apply_reframe(evidence: CExpr, plan: &EvidenceReframePlan) -> CExpr {
    match &plan.kind {
        EvidenceReframeKind::Identity => evidence,
        EvidenceReframeKind::SelectClosed { selectors } => {
            select_evidence(evidence, selectors.iter().map(lower_selector).collect())
        }
        EvidenceReframeKind::ReframeOpen {
            source_static_count,
            forward_static_positions,
            selectors,
        } => reframe_evidence(
            evidence,
            *source_static_count,
            forward_static_positions.clone(),
            selectors.iter().map(lower_selector).collect(),
        ),
    }
}

/// Execute a handler-installation plan. The plan also carries the resulting
/// `EvidenceAbi`, so callers cannot update runtime and compile-time frame
/// shapes through separate decisions.
pub(super) fn apply_install(
    evidence: CExpr,
    new_entry: CExpr,
    plan: &EvidenceInstallPlan,
) -> CExpr {
    match plan.kind {
        EvidenceInstallKind::Canonical => insert_canonical(evidence, new_entry),
        EvidenceInstallKind::StaticPrefix {
            source_static_count,
        } => insert_static(evidence, source_static_count, new_entry),
    }
}

/// Build a single `{EffectAtom, OpTuple}` Core Erlang tuple. `op_closures`
/// must already be sorted alphabetically by op name; today's
/// `lower_handler_def_to_tuple` produces them in that order.
///
/// With `lifted`, the entry is `{EffectAtom, OpTuple, lift}`: a `with` inside
/// the one installing it lifts its operations (`lift_evidence`). Without, its
/// arms can run where the operation is performed.
pub(super) fn build_evidence_entry(tag: &str, op_closures: Vec<CExpr>, lifted: bool) -> CExpr {
    let mut entry = vec![
        CExpr::Lit(CLit::Atom(tag.to_string())),
        CExpr::Tuple(op_closures),
    ];
    if lifted {
        entry.push(CExpr::Lit(CLit::Atom("lift".to_string())));
    }
    CExpr::Tuple(entry)
}

/// An entry whose arms have the shape of a direct one but perform, through
/// `frame`: direct exactly when every entry of `frame` is (`entry/3`).
pub(super) fn entry_for_frame(tag: &str, op_closures: Vec<CExpr>, frame: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "entry",
        vec![
            CExpr::Lit(CLit::Atom(tag.to_string())),
            CExpr::Tuple(op_closures),
            frame,
        ],
    )
}

/// Emit a runtime canonical-insert. The bridge walks the source tuple,
/// builds a new tuple with `new_entry` at its canonical position, and
/// replaces an existing entry whose tag matches (innermost-wins).
///
/// This is selected by an `EvidenceInstallPlan`; callers do not independently
/// choose between canonical and static-prefix insertion.
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
    forward_static_positions: Vec<usize>,
    selectors: Vec<CExpr>,
) -> CExpr {
    let forward_static_positions =
        forward_static_positions
            .into_iter()
            .rev()
            .fold(CExpr::Nil, |tail, position| {
                CExpr::Cons(
                    Box::new(CExpr::Lit(CLit::Int(position as i64))),
                    Box::new(tail),
                )
            });
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
            CExpr::Tuple(vec![
                CExpr::Lit(CLit::Int(static_count as i64)),
                forward_static_positions,
            ]),
            selectors,
        ],
    )
}

/// Combine handler-supplied callback evidence with the frame captured at the
/// original effect-operation call site: the entries for `named_tags` (the
/// effects the callback's type names) come from the call-time frame, every
/// other entry from the captured one. The result has no positional layout.
pub(super) fn append_tail(
    call_evidence: CExpr,
    captured_evidence: CExpr,
    named_tags: &[String],
) -> CExpr {
    let tags = named_tags.iter().rev().fold(CExpr::Nil, |tail, tag| {
        CExpr::Cons(
            Box::new(CExpr::Lit(CLit::Atom(tag.clone()))),
            Box::new(tail),
        )
    });
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "append_tail",
        vec![call_evidence, captured_evidence, tags],
    )
}

/// The inherited frame of a `with`, every operation suspending until the
/// `with` supplies its continuation, and every resumption delimited again by
/// the `with` whose abort reference is `abort_ref`. Same tags and layout.
pub(super) fn lift_evidence(evidence: CExpr, abort_ref: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "lift_evidence",
        vec![evidence, abort_ref],
    )
}

/// `lift_evidence` for a `with` whose arms resume in another frame: every
/// entry is lifted, direct ones too (`reroot`).
pub(super) fn lift_all_evidence(evidence: CExpr, abort_ref: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "lift_all_evidence",
        vec![evidence, abort_ref],
    )
}

/// The lifting for a `with` of a handler value, `installed` its tuple:
/// `lift_all_evidence` when the value's arms resume in another frame (its
/// tuple ends in `reroot`), otherwise `lift_evidence`.
pub(super) fn lift_for(evidence: CExpr, abort_ref: CExpr, installed: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "lift_for",
        vec![evidence, abort_ref, installed],
    )
}

/// `let r = resume x; rest` where the frame at the `resume` is `frame`, not
/// the one the arm's `with` lifted: the resumed computation is delimited
/// again there, and what it performs outside its `with` goes to `frame`.
pub(super) fn meta_reroot(resumed: CExpr, frame: CExpr, rest: CExpr) -> CExpr {
    cerl_call(EVIDENCE_BRIDGE_MODULE, "reroot", vec![resumed, frame, rest])
}

/// Give the result of a handled computation (a plain value or a suspension)
/// to the continuation of its `with`.
pub(super) fn meta_bind(result: CExpr, continuation: CExpr) -> CExpr {
    cerl_call(EVIDENCE_BRIDGE_MODULE, "bind", vec![result, continuation])
}

/// `meta_bind` for the result of a handled computation, with the common
/// case, a plain value, applied directly: `case R of {'$saga_meta', _} ->
/// bind(R, K); V -> K(V)`. `vars` are two fresh names.
pub(super) fn meta_bind_inline(result: CExpr, continuation: CExpr, vars: [String; 2]) -> CExpr {
    let [r, v] = vars;
    CExpr::Let(
        r.clone(),
        Box::new(result),
        Box::new(CExpr::Case(
            Box::new(CExpr::Var(r.clone())),
            vec![
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Lit(CLit::Atom("$saga_meta".to_string())),
                        CPat::Wildcard,
                    ]),
                    guard: None,
                    body: meta_bind(CExpr::Var(r), continuation.clone()),
                },
                CArm {
                    pat: CPat::Var(v.clone()),
                    guard: None,
                    body: CExpr::Apply(Box::new(continuation), vec![CExpr::Var(v)]),
                },
            ],
        )),
    )
}

/// `let r = resume x; rest` in an arm of the `with` `abort_ref`: `rest` gets
/// the value of the handled computation and runs before the continuation of
/// the `with`.
pub(super) fn meta_mbind(resumed: CExpr, rest: CExpr, abort_ref: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "mbind",
        vec![resumed, rest, abort_ref],
    )
}

/// `meta_bind` with the identity continuation: a plain value for a caller
/// that is not CPS code.
pub(super) fn meta_run(result: CExpr) -> CExpr {
    cerl_call(EVIDENCE_BRIDGE_MODULE, "run", vec![result])
}

/// The continuation of an arm's tail that does not resume: the abort of the
/// `with` `abort_ref`, from effect `tag`.
pub(super) fn abort_continuation(param: String, abort_ref: CExpr, tag: &str) -> CExpr {
    CExpr::Fun(
        vec![param.clone()],
        Box::new(cerl_call(
            EVIDENCE_BRIDGE_MODULE,
            "abort",
            vec![
                abort_ref,
                CExpr::Lit(CLit::Atom(tag.to_string())),
                CExpr::Var(param),
            ],
        )),
    )
}

/// `resume` in an arm with a `finally` block: the resumed computation
/// `k(value)` is a region whose end runs `cleanup` (a fun of no arguments).
pub(super) fn fin_resume(abort_ref: CExpr, cleanup: CExpr, k: CExpr, value: CExpr) -> CExpr {
    cerl_call(
        EVIDENCE_BRIDGE_MODULE,
        "fin_resume",
        vec![abort_ref, cleanup, k, value],
    )
}

/// The computation of a spawned process, `thunk` a fun of no arguments.
pub(super) fn run_process(thunk: CExpr) -> CExpr {
    cerl_call(EVIDENCE_BRIDGE_MODULE, "run_process", vec![thunk])
}

/// `body` delimited by the `with` whose abort reference is the variable
/// `abort_ref`: its abort becomes the value. `vars` are four fresh names.
pub(super) fn catch_own_abort(body: CExpr, abort_ref: &str, vars: [String; 5]) -> CExpr {
    let [ok, class, reason, trace, value] = vars;
    let owner = format!("{value}Ref");
    let is_own = CArm {
        pat: CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("throw".to_string())),
            CPat::Tuple(vec![
                CPat::Lit(CLit::Atom("$saga_abort".to_string())),
                CPat::Var(owner.clone()),
                CPat::Wildcard,
                CPat::Var(value.clone()),
            ]),
        ]),
        guard: Some(cerl_call(
            "erlang",
            "=:=",
            vec![CExpr::Var(owner), CExpr::Var(abort_ref.to_string())],
        )),
        body: CExpr::Var(value),
    };
    let other = CArm {
        pat: CPat::Wildcard,
        guard: None,
        body: CExpr::PrimOp(
            "raw_raise".to_string(),
            vec![
                CExpr::Var(class.clone()),
                CExpr::Var(reason.clone()),
                CExpr::Var(trace.clone()),
            ],
        ),
    };
    CExpr::Try {
        expr: Box::new(body),
        ok_var: ok.clone(),
        ok_body: Box::new(CExpr::Var(ok)),
        catch_vars: (class.clone(), reason.clone(), trace),
        catch_body: Box::new(CExpr::Case(
            Box::new(CExpr::Tuple(vec![CExpr::Var(class), CExpr::Var(reason)])),
            vec![is_own, other],
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_closure(name: &str) -> CExpr {
        CExpr::Var(name.to_string())
    }

    #[test]
    fn abi_sorts_and_dedups() {
        let abi = EvidenceAbi::closed([
            "Std.IO.Stdio".to_string(),
            "Std.Fail.Fail".to_string(),
            "Std.IO.Stdio".to_string(),
        ]);
        assert_eq!(abi.static_slots(), &["Std.Fail.Fail", "Std.IO.Stdio"]);
    }

    #[test]
    fn installing_an_effect_already_in_the_prefix_keeps_one_slot() {
        let abi = EvidenceAbi::new(["Std.Fail.Fail"], true)
            .plan_install("Std.Fail.Fail")
            .target;
        assert_eq!(abi.static_slots(), &["Std.Fail.Fail"]);
    }

    #[test]
    fn installing_another_effect_adds_a_slot() {
        let abi = EvidenceAbi::new(["Main.UserRepo"], true)
            .plan_install("Main.OrderRepo")
            .target;
        assert_eq!(abi.static_slots(), &["Main.OrderRepo", "Main.UserRepo"]);
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
            false,
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
        let entry = build_evidence_entry("Std.Fail.Fail", vec![dummy_closure("Fail")], false);
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
        let entry = build_evidence_entry("Router.Skip", vec![dummy_closure("Skip")], false);
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
    fn apply_install_executes_the_abi_planned_strategy() {
        let source = EvidenceAbi::new(["Main.Fail"], true);
        let plan = source.plan_install("Main.Fail");
        let entry =
            build_evidence_entry("Main.Fail", vec![dummy_closure("Fail")], false);
        let CExpr::Call(module, function, args) =
            apply_install(CExpr::Var("_Evidence".to_string()), entry, &plan)
        else {
            panic!("expected bridge call")
        };
        assert_eq!(module, "std_evidence_bridge");
        assert_eq!(function, "insert_static");
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
    fn reframe_evidence_preserves_selector_order() {
        let call = reframe_evidence(
            CExpr::Var("_Evidence".to_string()),
            2,
            vec![1],
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
        let CExpr::Tuple(frame_plan) = &args[1] else {
            panic!("expected frame plan tuple")
        };
        assert!(matches!(&frame_plan[0], CExpr::Lit(CLit::Int(2))));
        let CExpr::Cons(forwarded, forwarded_tail) = &frame_plan[1] else {
            panic!("expected forwarded static position list")
        };
        assert!(matches!(forwarded.as_ref(), CExpr::Lit(CLit::Int(1))));
        assert!(matches!(forwarded_tail.as_ref(), CExpr::Nil));
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
            &["Counter".to_string()],
        );
        let CExpr::Call(module, function, args) = call else {
            panic!("expected bridge call")
        };
        assert_eq!(module, "std_evidence_bridge");
        assert_eq!(function, "append_tail");
        assert_eq!(args.len(), 3);
        let CExpr::Cons(tag, rest) = &args[2] else {
            panic!("expected a list of named tags")
        };
        assert!(matches!(tag.as_ref(), CExpr::Lit(CLit::Atom(tag)) if tag == "Counter"));
        assert!(matches!(rest.as_ref(), CExpr::Nil));
    }

    #[test]
    fn build_entry_with_empty_ops_is_legal() {
        // An effect with no live ops at the moment (degenerate but representable).
        let entry = build_evidence_entry("Std.Fail.Fail", vec![], false);
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
        let entry = build_evidence_entry("Std.Fail.Fail", vec![dummy_closure("F")], false);
        let CExpr::Tuple(top) = entry else { panic!() };
        match &top[0] {
            CExpr::Lit(CLit::Atom(a)) => assert_eq!(a, "Std.Fail.Fail"),
            other => panic!("expected unmangled tag atom, got {:?}", other),
        }
    }
}
