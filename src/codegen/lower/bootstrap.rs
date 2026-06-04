//! Module-init bootstrap for BEAM-native default handlers.
//!
//! The slow uniform path on the new lowerer routes every effect call
//! through `find_evidence/2` at runtime. The old lowerer short-circuits
//! BEAM-native effect calls (Process, Actor, Timer, Ref, …) into direct BIF
//! calls at lowering time — there is no runtime-resident handler for
//! them. The new uniform path can't take that shortcut, so it needs
//! default handlers visible in `_Evidence` whenever no user `with` has
//! installed one.
//!
//! ## What this module emits
//!
//! [`build_initial_evidence_fundef`] returns a `__saga_initial_evidence/0`
//! function whose body is the canonical evidence vector containing the
//! BEAM-native handlers. Each entry is `{EffectAtom, OpTuple}`; each
//! closure inside an `OpTuple` has shape
//! `fun(Arg0, …, ArgN, EvidenceAtPerform, K) -> apply K(call '<erl_mod>':'<func>'(args))`.
//! The perform-site evidence parameter is ignored by first-order native
//! ops and used by callback-invoking ops such as `spawn`.
//!
//! The function is emitted as `/0`-arity with no `_Evidence` / `_ReturnK`
//! threading: it's a pure constant-shaped builder consumed once at the
//! entry point. The new-path emit hook threads the result into `main`'s
//! `_Evidence` slot before invoking user code.
//!
//! ## Scope (7g part B)
//!
//! This is the structural scaffolding. The op-body table here covers the
//! Identity / NoArgs / simple argument-transform subset — direct passthrough
//! to a BIF, `spawn` thunk wrapping, `monitor` atom-prepend, and
//! `send_after` argument reordering. Handler-specific Ref/Vec backends live
//! in `bootstrap/stores.rs`. Ops not covered by the entries here emit a
//! `not_implemented` exit stub: the evidence vector has the correct shape,
//! but invoking a stubbed op at runtime crashes with a clear tag.
//!
//! ## Effect / op canonical ordering
//!
//! The runtime evidence-vector helper (`std_evidence_bridge:find_evidence`)
//! and the lowerer's `Yield` path (`exprs.rs::lower_yield`) both assume
//! op-tuples are indexed alphabetically by op name. The
//! [`native_effects::NATIVE_EFFECTS`] enforces that: ops are pre-sorted.

mod native_effects;
mod stores;

use crate::codegen::cerl::{CExpr, CFunDef, CLit};
use crate::codegen::ets_tables::{ETS_REF_TABLE, ETS_VEC_TABLE, wrap_ets_table_init_core};

use self::native_effects::{ArgTransform, NATIVE_EFFECTS, NativeOp};
use self::stores::{RefBackend, build_ref_call, ref_op_tuple, vec_op_tuple};
use super::util::identity_k;

/// Name of the emitted bootstrap function. Arity 0; returns the initial
/// evidence vector value.
pub(super) const BOOTSTRAP_FN_NAME: &str = "__saga_initial_evidence";

/// Build the `__saga_initial_evidence/0` function definition.
///
/// Body: a tuple of `{EffectAtom, OpTuple}` pairs, one per native
/// effect, sorted canonically by effect-tag name (already the order in
/// [`NATIVE_EFFECTS`]). The function takes no params and returns the
/// vector directly — no `_Evidence` / `_ReturnK` threading.
pub(super) fn build_initial_evidence_fundef() -> CFunDef {
    let mut entries: Vec<CExpr> = Vec::with_capacity(NATIVE_EFFECTS.len());
    for effect in NATIVE_EFFECTS {
        let op_closures: Vec<CExpr> = effect
            .ops
            .iter()
            .map(|op| build_op_closure(effect.tag, op))
            .collect();
        let op_tuple = CExpr::Tuple(op_closures);
        let entry = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom(effect.tag.to_string())),
            op_tuple,
        ]);
        entries.push(entry);
    }
    let vector = CExpr::Tuple(entries);
    CFunDef {
        name: BOOTSTRAP_FN_NAME.to_string(),
        arity: 0,
        body: CExpr::Fun(vec![], Box::new(vector)),
    }
}

/// Build a CExpr that calls the bootstrap function to materialise the
/// initial evidence vector. Useful when threading evidence into an
/// entry-point body emitted in the same module.
pub(super) fn call_initial_evidence() -> CExpr {
    CExpr::Apply(
        Box::new(CExpr::FunRef(BOOTSTRAP_FN_NAME.to_string(), 0)),
        vec![],
    )
}

/// Build the synthetic `main/1` entry-point wrapper.
///
/// The BEAM runner spawned by `exec_erl` invokes `Module:main/1` with the
/// atom `'unit'`. The user's `main () = …` is exported as `main/3` under
/// the uniform calling convention (1 user param + `_Evidence` +
/// `_ReturnK`), so the runner can't call it directly. This wrapper bridges
/// the two by materialising the initial evidence vector and supplying an
/// identity return continuation:
///
/// ```text
/// 'main'/1 = fun (_Arg) ->
///   let <_Ev> = apply '__saga_initial_evidence'/0() in
///   let <_K>  = fun (_V) -> _V in
///   apply 'main'/3('unit', _Ev, _K)
/// ```
///
/// The wrapper deliberately ignores its incoming `_Arg` and passes
/// `'unit'` to the user's `main` — `main`'s `()` pattern matches the
/// atom `'unit'`.
pub(super) fn build_main_entry_wrapper() -> CFunDef {
    let arg_param = "_Arg".to_string();
    let ev_var = "_Ev".to_string();
    let k_var = "_K".to_string();
    let v_param = "_V".to_string();

    let evidence_call = call_initial_evidence();
    let identity_k = identity_k(v_param);
    let apply_main = CExpr::Apply(
        Box::new(CExpr::FunRef("main".to_string(), 3)),
        vec![
            CExpr::Lit(CLit::Atom("unit".to_string())),
            CExpr::Var(ev_var.clone()),
            CExpr::Var(k_var.clone()),
        ],
    );
    let let_k = CExpr::Let(k_var, Box::new(identity_k), Box::new(apply_main));
    let let_ev = CExpr::Let(ev_var, Box::new(evidence_call), Box::new(let_k));
    let body = wrap_ets_table_init_core(
        wrap_ets_table_init_core(let_ev, ETS_VEC_TABLE, "_EtsVecInit"),
        ETS_REF_TABLE,
        "_EtsRefInit",
    );

    CFunDef {
        name: "main".to_string(),
        arity: 1,
        body: CExpr::Fun(vec![arg_param], Box::new(body)),
    }
}

/// Build a single op closure for an `OpTuple` slot.
///
/// Shape: `fun(Arg0, …, ArgN, EvidenceAtPerform, K) -> apply K(<body>)` where `<body>` is
/// either `call '<erl_mod>':'<func>'(args)` (Identity stubs) or
/// `erlang:exit({not_implemented_native_op, '<effect>', '<op>'})` for
/// shapes outside the Identity subset.
fn build_op_closure(effect_tag: &str, op: &NativeOp) -> CExpr {
    native_op_closure(op.param_count, |evidence_var| {
        build_default_native_call(effect_tag, op, evidence_var)
    })
}

pub(super) fn native_op_closure(
    param_count: usize,
    result_expr: impl FnOnce(&str) -> CExpr,
) -> CExpr {
    let mut params: Vec<String> = (0..param_count).map(|i| format!("_Arg{}", i)).collect();
    let evidence_var = "_EvidenceAtPerform".to_string();
    let k_var = "_K".to_string();
    params.push(evidence_var.clone());
    params.push(k_var.clone());
    let result_expr = result_expr(&evidence_var);
    let apply_k = CExpr::Apply(Box::new(CExpr::Var(k_var)), vec![result_expr]);
    CExpr::Fun(params, Box::new(apply_k))
}

pub(super) fn not_implemented_native_op(effect_tag: &str, op_name: &str) -> CExpr {
    CExpr::Call(
        "erlang".to_string(),
        "exit".to_string(),
        vec![CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("not_implemented_native_op".to_string())),
            CExpr::Lit(CLit::Atom(effect_tag.to_string())),
            CExpr::Lit(CLit::Atom(op_name.to_string())),
        ])],
    )
}

fn build_default_native_call(effect_tag: &str, op: &NativeOp, evidence_var: &str) -> CExpr {
    if effect_tag == "Std.Ref.Ref" {
        build_ref_call(op, evidence_var, RefBackend::ProcessDictionary)
    } else if op.erl_module.is_empty() {
        not_implemented_native_op(effect_tag, op.name)
    } else {
        let call_args = native_call_args(op, evidence_var);
        CExpr::Call(
            op.erl_module.to_string(),
            op.erl_func.to_string(),
            call_args,
        )
    }
}

pub(super) fn native_handler_op_tuple(effect: &str, handler: &str) -> Option<CExpr> {
    let handler = handler.rsplit('.').next().unwrap_or(handler);
    match (effect, handler) {
        ("Std.Ref.Ref", "beam_ref") => Some(ref_op_tuple(RefBackend::ProcessDictionary)),
        ("Std.Ref.Ref", "ets_ref") => Some(ref_op_tuple(RefBackend::Ets)),
        ("Std.Vec.Vec", "beam_vec") => Some(vec_op_tuple()),
        (_, "beam_actor") => NATIVE_EFFECTS
            .iter()
            .find(|native| native.tag == effect && native.tag.starts_with("Std.Actor."))
            .map(|native| {
                CExpr::Tuple(
                    native
                        .ops
                        .iter()
                        .map(|op| build_op_closure(native.tag, op))
                        .collect(),
                )
            }),
        _ => None,
    }
}

fn native_call_args(op: &NativeOp, evidence_var: &str) -> Vec<CExpr> {
    match &op.arg_transform {
        ArgTransform::Identity => (0..op.param_count)
            .map(|i| CExpr::Var(format!("_Arg{}", i)))
            .collect(),
        ArgTransform::NoArgs => Vec::new(),
        ArgTransform::PrependAtom(atom) => {
            let mut args = vec![CExpr::Lit(CLit::Atom((*atom).to_string()))];
            args.extend((0..op.param_count).map(|i| CExpr::Var(format!("_Arg{}", i))));
            args
        }
        ArgTransform::Reorder(indices) => indices
            .iter()
            .map(|&i| CExpr::Var(format!("_Arg{}", i)))
            .collect(),
        ArgTransform::WrapThunk(idx) => (0..op.param_count)
            .map(|i| {
                if i == *idx {
                    spawn_thunk(format!("_Arg{}", i), evidence_var.to_string())
                } else {
                    CExpr::Var(format!("_Arg{}", i))
                }
            })
            .collect(),
    }
}

/// Build the `fun() -> ...` thunk passed to `erlang:spawn`. The child runs the
/// callback with a *copy* of the perform-site evidence (BEAM copies the closure
/// env into the child's heap). This is correct for process-portable effects
/// (native BIFs, `ets_ref`) but silently forks non-portable ones (user handlers,
/// process-dict `beam_ref`). See `docs/planning/spawn-effect-evidence.md`.
fn spawn_thunk(callback_var: String, evidence_var: String) -> CExpr {
    let k_var = "_SpawnK".to_string();
    let v_var = "_SpawnV".to_string();
    let identity_k = identity_k(v_var);
    let apply_callback = CExpr::Apply(
        Box::new(CExpr::Var(callback_var)),
        vec![
            CExpr::Lit(CLit::Atom("unit".to_string())),
            CExpr::Var(evidence_var),
            CExpr::Var(k_var.clone()),
        ],
    );
    CExpr::Fun(
        vec![],
        Box::new(CExpr::Let(
            k_var,
            Box::new(identity_k),
            Box::new(apply_callback),
        )),
    )
}

/// Number of native effect entries in the bootstrap evidence vector.
/// Public to support structural tests asserting shape without
/// re-counting the table.
pub(super) fn native_effect_count() -> usize {
    NATIVE_EFFECTS.len()
}

/// Canonical tags of the native effects in the bootstrap order. Public
/// for tests asserting evidence-vector layout.
pub(super) fn native_effect_tags() -> Vec<&'static str> {
    NATIVE_EFFECTS.iter().map(|e| e.tag).collect()
}

/// Op names for a given effect tag, in canonical (alphabetical) order.
/// Returns `None` for an unknown tag.
pub(super) fn ops_for_effect(tag: &str) -> Option<Vec<&'static str>> {
    NATIVE_EFFECTS
        .iter()
        .find(|e| e.tag == tag)
        .map(|e| e.ops.iter().map(|o| o.name).collect())
}
