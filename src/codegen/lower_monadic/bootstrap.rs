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
//! `send_after` argument reordering. Handler-specific Ref backends now live
//! in this module too. Ops not covered by the entries here emit a
//! `not_implemented` exit stub: the evidence vector has the correct shape,
//! but invoking a stubbed op at runtime crashes with a clear tag.
//!
//! ## Effect / op canonical ordering
//!
//! The runtime evidence-vector helper (`std_evidence_bridge:find_evidence`)
//! and the lowerer's `Yield` path (`exprs.rs::lower_yield`) both assume
//! op-tuples are indexed alphabetically by op name. The
//! [`NATIVE_EFFECTS`] table here enforces that: ops are pre-sorted.

use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CPat};

/// Name of the emitted bootstrap function. Arity 0; returns the initial
/// evidence vector value.
pub(super) const BOOTSTRAP_FN_NAME: &str = "__saga_initial_evidence";

/// A single BEAM-native op stub entry: how to forward saga-side args to
/// the underlying BIF.
struct NativeOp {
    /// Source op name (matches the Saga effect-decl op name).
    name: &'static str,
    /// Erlang module/function the BIF lives in. Empty `module` ("") means
    /// "not implemented in this scaffold — stub body".
    erl_module: &'static str,
    erl_func: &'static str,
    /// Number of saga-side args this op takes. Closure arity is
    /// `param_count + 2` (perform-site evidence + trailing K continuation).
    param_count: usize,
    arg_transform: ArgTransform,
}

enum ArgTransform {
    Identity,
    NoArgs,
    PrependAtom(&'static str),
    Reorder(&'static [usize]),
    WrapThunk(usize),
}

/// A BEAM-native effect + its ops in canonical (alphabetical) order.
///
/// The effect tag is the canonical effect name as it appears in
/// `find_evidence`'s lookup (`'Std.Actor.Process'`, `'Std.Actor.Timer'`, …).
/// Ops are pre-sorted; the runtime indexes them via `element(op_index,
/// OpTuple)`.
struct NativeEffect {
    tag: &'static str,
    ops: &'static [NativeOp],
}

/// Pre-sorted native effect / op table. Tags and op ordering match the
/// canonical names produced by the typechecker and used by the translator's
/// `EffectOpRef`.
const NATIVE_EFFECTS: &[NativeEffect] = &[
    NativeEffect {
        tag: "Std.Actor.Actor",
        ops: &[NativeOp {
            name: "self",
            erl_module: "erlang",
            erl_func: "self",
            param_count: 1,
            arg_transform: ArgTransform::NoArgs,
        }],
    },
    NativeEffect {
        tag: "Std.Actor.Link",
        ops: &[
            NativeOp {
                name: "link",
                erl_module: "erlang",
                erl_func: "link",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
            NativeOp {
                name: "unlink",
                erl_module: "erlang",
                erl_func: "unlink",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
        ],
    },
    NativeEffect {
        tag: "Std.Actor.Monitor",
        ops: &[
            NativeOp {
                name: "demonitor",
                erl_module: "erlang",
                erl_func: "demonitor",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
            NativeOp {
                name: "monitor",
                erl_module: "erlang",
                erl_func: "monitor",
                param_count: 1,
                arg_transform: ArgTransform::PrependAtom("process"),
            },
        ],
    },
    NativeEffect {
        tag: "Std.Actor.Process",
        // Alphabetical: exit, send, spawn
        ops: &[
            NativeOp {
                name: "exit",
                erl_module: "erlang",
                erl_func: "exit",
                param_count: 2,
                arg_transform: ArgTransform::Identity,
            },
            NativeOp {
                name: "send",
                erl_module: "erlang",
                erl_func: "send",
                param_count: 2,
                arg_transform: ArgTransform::Identity,
            },
            NativeOp {
                name: "spawn",
                erl_module: "erlang",
                erl_func: "spawn",
                param_count: 1,
                arg_transform: ArgTransform::WrapThunk(0),
            },
        ],
    },
    NativeEffect {
        tag: "Std.Actor.Timer",
        // Alphabetical: cancel_timer, send_after, sleep
        ops: &[
            NativeOp {
                name: "cancel_timer",
                erl_module: "erlang",
                erl_func: "cancel_timer",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
            NativeOp {
                name: "send_after",
                erl_module: "erlang",
                erl_func: "send_after",
                param_count: 3,
                arg_transform: ArgTransform::Reorder(&[1, 0, 2]),
            },
            NativeOp {
                name: "sleep",
                erl_module: "timer",
                erl_func: "sleep",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
        ],
    },
    NativeEffect {
        tag: "Std.Process.Signal",
        ops: &[NativeOp {
            name: "await_signal",
            erl_module: "saga_runtime",
            erl_func: "await_signal",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        }],
    },
    NativeEffect {
        tag: "Std.Ref.Ref",
        // Alphabetical: get, modify, new, set
        ops: &[
            NativeOp {
                name: "get",
                erl_module: "erlang",
                erl_func: "get",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
            // modify: handler-specific (procdict vs ETS) → stub
            NativeOp {
                name: "modify",
                erl_module: "",
                erl_func: "get",
                param_count: 2,
                arg_transform: ArgTransform::Identity,
            },
            // new: handler-specific → stub
            NativeOp {
                name: "new",
                erl_module: "",
                erl_func: "make_ref",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            },
            NativeOp {
                name: "set",
                erl_module: "erlang",
                erl_func: "put",
                param_count: 2,
                arg_transform: ArgTransform::Identity,
            },
        ],
    },
];

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
    let identity_k = CExpr::Fun(vec![v_param.clone()], Box::new(CExpr::Var(v_param)));
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
    let body = wrap_table_init(
        wrap_table_init(let_ev, "saga_vec_store", "_EtsVecInit"),
        "saga_ref_store",
        "_EtsRefInit",
    );

    CFunDef {
        name: "main".to_string(),
        arity: 1,
        body: CExpr::Fun(vec![arg_param], Box::new(body)),
    }
}

fn wrap_table_init(body: CExpr, table_name: &str, bind_name: &str) -> CExpr {
    let table = CExpr::Lit(CLit::Atom(table_name.to_string()));
    let init_expr = CExpr::Case(
        Box::new(CExpr::Call(
            "ets".to_string(),
            "info".to_string(),
            vec![table.clone()],
        )),
        vec![
            CArm {
                pat: CPat::Lit(CLit::Atom("undefined".to_string())),
                guard: None,
                body: CExpr::Call(
                    "ets".to_string(),
                    "new".to_string(),
                    vec![table, ets_table_options()],
                ),
            },
            CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: CExpr::Lit(CLit::Atom("unit".to_string())),
            },
        ],
    );
    CExpr::Let(bind_name.to_string(), Box::new(init_expr), Box::new(body))
}

fn ets_table_options() -> CExpr {
    CExpr::Cons(
        Box::new(CExpr::Lit(CLit::Atom("set".to_string()))),
        Box::new(CExpr::Cons(
            Box::new(CExpr::Lit(CLit::Atom("public".to_string()))),
            Box::new(CExpr::Cons(
                Box::new(CExpr::Lit(CLit::Atom("named_table".to_string()))),
                Box::new(CExpr::Nil),
            )),
        )),
    )
}

/// Build a single op closure for an `OpTuple` slot.
///
/// Shape: `fun(Arg0, …, ArgN, EvidenceAtPerform, K) -> apply K(<body>)` where `<body>` is
/// either `call '<erl_mod>':'<func>'(args)` (Identity stubs) or
/// `erlang:exit({not_implemented_native_op, '<effect>', '<op>'})` for
/// shapes outside the Identity subset.
fn build_op_closure(effect_tag: &str, op: &NativeOp) -> CExpr {
    let mut params: Vec<String> = (0..op.param_count).map(|i| format!("_Arg{}", i)).collect();
    let evidence_var = "_EvidenceAtPerform".to_string();
    let k_var = "_K".to_string();
    params.push(evidence_var.clone());
    params.push(k_var.clone());

    let result_expr = if effect_tag == "Std.Ref.Ref" {
        build_ref_call(op, &evidence_var, RefBackend::ProcessDictionary)
    } else if op.erl_module.is_empty() {
        // Stub: not-implemented exit. Tag carries effect + op for
        // debugging when this fires at runtime.
        CExpr::Call(
            "erlang".to_string(),
            "exit".to_string(),
            vec![CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("not_implemented_native_op".to_string())),
                CExpr::Lit(CLit::Atom(effect_tag.to_string())),
                CExpr::Lit(CLit::Atom(op.name.to_string())),
            ])],
        )
    } else {
        let call_args = native_call_args(op, &evidence_var);
        CExpr::Call(
            op.erl_module.to_string(),
            op.erl_func.to_string(),
            call_args,
        )
    };
    let apply_k = CExpr::Apply(Box::new(CExpr::Var(k_var)), vec![result_expr]);
    CExpr::Fun(params, Box::new(apply_k))
}

#[derive(Clone, Copy)]
enum RefBackend {
    ProcessDictionary,
    Ets,
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

fn vec_op_tuple() -> CExpr {
    let ops = [
        NativeOp {
            name: "freeze",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "thaw",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "vec_get",
            erl_module: "",
            erl_func: "",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "vec_len",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "vec_new",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "vec_pop",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "vec_push",
            erl_module: "",
            erl_func: "",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "vec_set",
            erl_module: "",
            erl_func: "",
            param_count: 3,
            arg_transform: ArgTransform::Identity,
        },
    ];
    CExpr::Tuple(ops.iter().map(build_vec_op_closure).collect())
}

fn build_vec_op_closure(op: &NativeOp) -> CExpr {
    let mut params: Vec<String> = (0..op.param_count).map(|i| format!("_Arg{}", i)).collect();
    let evidence_var = "_EvidenceAtPerform".to_string();
    let k_var = "_K".to_string();
    params.push(evidence_var);
    params.push(k_var.clone());
    let result_expr = build_vec_call(op);
    CExpr::Fun(
        params,
        Box::new(CExpr::Apply(Box::new(CExpr::Var(k_var)), vec![result_expr])),
    )
}

fn build_vec_call(op: &NativeOp) -> CExpr {
    let table = CExpr::Lit(CLit::Atom("saga_vec_store".to_string()));
    let length_atom = CExpr::Lit(CLit::Atom("length".to_string()));
    match op.name {
        "vec_new" => {
            let id = "_VecId".to_string();
            let d = "_VecInsert".to_string();
            CExpr::Let(
                id.clone(),
                Box::new(CExpr::Call(
                    "erlang".to_string(),
                    "make_ref".to_string(),
                    vec![],
                )),
                Box::new(CExpr::Let(
                    d,
                    Box::new(CExpr::Call(
                        "ets".to_string(),
                        "insert".to_string(),
                        vec![
                            table,
                            CExpr::Tuple(vec![
                                CExpr::Tuple(vec![CExpr::Var(id.clone()), length_atom]),
                                CExpr::Lit(CLit::Int(0)),
                            ]),
                        ],
                    )),
                    Box::new(CExpr::Var(id)),
                )),
            )
        }
        "vec_len" => vec_lookup_value(
            table,
            CExpr::Tuple(vec![CExpr::Var("_Arg0".to_string()), length_atom]),
            "_VecLenLookup",
            "_VecLen",
        ),
        "vec_get" => vec_lookup_value(
            table,
            CExpr::Tuple(vec![
                CExpr::Var("_Arg0".to_string()),
                CExpr::Var("_Arg1".to_string()),
            ]),
            "_VecGetLookup",
            "_VecValue",
        ),
        "vec_set" => {
            let d = "_VecInsert".to_string();
            CExpr::Let(
                d,
                Box::new(CExpr::Call(
                    "ets".to_string(),
                    "insert".to_string(),
                    vec![
                        table,
                        CExpr::Tuple(vec![
                            CExpr::Tuple(vec![
                                CExpr::Var("_Arg0".to_string()),
                                CExpr::Var("_Arg1".to_string()),
                            ]),
                            CExpr::Var("_Arg2".to_string()),
                        ]),
                    ],
                )),
                Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
            )
        }
        "vec_push" => {
            let lookup = "_VecLenLookup".to_string();
            let len = "_VecLen".to_string();
            let d1 = "_VecInsertValue".to_string();
            let d2 = "_VecInsertLen".to_string();
            CExpr::Let(
                lookup.clone(),
                Box::new(CExpr::Call(
                    "ets".to_string(),
                    "lookup".to_string(),
                    vec![
                        table.clone(),
                        CExpr::Tuple(vec![CExpr::Var("_Arg0".to_string()), length_atom.clone()]),
                    ],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(len.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Let(
                            d1,
                            Box::new(CExpr::Call(
                                "ets".to_string(),
                                "insert".to_string(),
                                vec![
                                    table.clone(),
                                    CExpr::Tuple(vec![
                                        CExpr::Tuple(vec![
                                            CExpr::Var("_Arg0".to_string()),
                                            CExpr::Var(len.clone()),
                                        ]),
                                        CExpr::Var("_Arg1".to_string()),
                                    ]),
                                ],
                            )),
                            Box::new(CExpr::Let(
                                d2,
                                Box::new(CExpr::Call(
                                    "ets".to_string(),
                                    "insert".to_string(),
                                    vec![
                                        table,
                                        CExpr::Tuple(vec![
                                            CExpr::Tuple(vec![
                                                CExpr::Var("_Arg0".to_string()),
                                                length_atom,
                                            ]),
                                            CExpr::Call(
                                                "erlang".to_string(),
                                                "+".to_string(),
                                                vec![CExpr::Var(len), CExpr::Lit(CLit::Int(1))],
                                            ),
                                        ]),
                                    ],
                                )),
                                Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
                            )),
                        ),
                    }],
                )),
            )
        }
        "vec_pop" => {
            let lookup = "_VecLenLookup".to_string();
            let len = "_VecLen".to_string();
            let new_len = "_VecNewLen".to_string();
            let elem_lookup = "_VecElemLookup".to_string();
            let elem = "_VecElem".to_string();
            let d1 = "_VecDelete".to_string();
            let d2 = "_VecSetLen".to_string();
            CExpr::Let(
                lookup.clone(),
                Box::new(CExpr::Call(
                    "ets".to_string(),
                    "lookup".to_string(),
                    vec![
                        table.clone(),
                        CExpr::Tuple(vec![CExpr::Var("_Arg0".to_string()), length_atom.clone()]),
                    ],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(len.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Let(
                            new_len.clone(),
                            Box::new(CExpr::Call(
                                "erlang".to_string(),
                                "-".to_string(),
                                vec![CExpr::Var(len), CExpr::Lit(CLit::Int(1))],
                            )),
                            Box::new(CExpr::Let(
                                elem_lookup.clone(),
                                Box::new(CExpr::Call(
                                    "ets".to_string(),
                                    "lookup".to_string(),
                                    vec![
                                        table.clone(),
                                        CExpr::Tuple(vec![
                                            CExpr::Var("_Arg0".to_string()),
                                            CExpr::Var(new_len.clone()),
                                        ]),
                                    ],
                                )),
                                Box::new(CExpr::Case(
                                    Box::new(CExpr::Var(elem_lookup)),
                                    vec![CArm {
                                        pat: CPat::Cons(
                                            Box::new(CPat::Tuple(vec![
                                                CPat::Wildcard,
                                                CPat::Var(elem.clone()),
                                            ])),
                                            Box::new(CPat::Nil),
                                        ),
                                        guard: None,
                                        body: CExpr::Let(
                                            d1,
                                            Box::new(CExpr::Call(
                                                "ets".to_string(),
                                                "delete".to_string(),
                                                vec![
                                                    table.clone(),
                                                    CExpr::Tuple(vec![
                                                        CExpr::Var("_Arg0".to_string()),
                                                        CExpr::Var(new_len.clone()),
                                                    ]),
                                                ],
                                            )),
                                            Box::new(CExpr::Let(
                                                d2,
                                                Box::new(CExpr::Call(
                                                    "ets".to_string(),
                                                    "insert".to_string(),
                                                    vec![
                                                        table,
                                                        CExpr::Tuple(vec![
                                                            CExpr::Tuple(vec![
                                                                CExpr::Var("_Arg0".to_string()),
                                                                length_atom,
                                                            ]),
                                                            CExpr::Var(new_len),
                                                        ]),
                                                    ],
                                                )),
                                                Box::new(CExpr::Var(elem)),
                                            )),
                                        ),
                                    }],
                                )),
                            )),
                        ),
                    }],
                )),
            )
        }
        "freeze" => {
            let len = "_VecLen".to_string();
            let last = "_VecLast".to_string();
            let indices = "_VecIndices".to_string();
            let idx = "_VecIndex".to_string();
            let lookup = "_VecLookup".to_string();
            let value = "_VecValue".to_string();
            let len_expr = build_vec_call(&NativeOp {
                name: "vec_len",
                erl_module: "",
                erl_func: "",
                param_count: 1,
                arg_transform: ArgTransform::Identity,
            });
            CExpr::Let(
                len.clone(),
                Box::new(len_expr),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(len.clone())),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Int(0)),
                            guard: None,
                            body: CExpr::Nil,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: CExpr::Let(
                                last.clone(),
                                Box::new(CExpr::Call(
                                    "erlang".to_string(),
                                    "-".to_string(),
                                    vec![CExpr::Var(len), CExpr::Lit(CLit::Int(1))],
                                )),
                                Box::new(CExpr::Let(
                                    indices.clone(),
                                    Box::new(CExpr::Call(
                                        "lists".to_string(),
                                        "seq".to_string(),
                                        vec![CExpr::Lit(CLit::Int(0)), CExpr::Var(last)],
                                    )),
                                    Box::new(CExpr::Call(
                                        "lists".to_string(),
                                        "map".to_string(),
                                        vec![
                                            CExpr::Fun(
                                                vec![idx.clone()],
                                                Box::new(CExpr::Let(
                                                    lookup.clone(),
                                                    Box::new(CExpr::Call(
                                                        "ets".to_string(),
                                                        "lookup".to_string(),
                                                        vec![
                                                            table,
                                                            CExpr::Tuple(vec![
                                                                CExpr::Var("_Arg0".to_string()),
                                                                CExpr::Var(idx),
                                                            ]),
                                                        ],
                                                    )),
                                                    Box::new(CExpr::Case(
                                                        Box::new(CExpr::Var(lookup)),
                                                        vec![CArm {
                                                            pat: CPat::Cons(
                                                                Box::new(CPat::Tuple(vec![
                                                                    CPat::Wildcard,
                                                                    CPat::Var(value.clone()),
                                                                ])),
                                                                Box::new(CPat::Nil),
                                                            ),
                                                            guard: None,
                                                            body: CExpr::Var(value),
                                                        }],
                                                    )),
                                                )),
                                            ),
                                            CExpr::Var(indices),
                                        ],
                                    )),
                                )),
                            ),
                        },
                    ],
                )),
            )
        }
        "thaw" => {
            let id = "_VecId".to_string();
            let idx = "_VecIndex".to_string();
            let elem = "_VecElem".to_string();
            let final_len = "_VecFinalLen".to_string();
            let d = "_VecLenInsert".to_string();
            CExpr::Let(
                id.clone(),
                Box::new(CExpr::Call(
                    "erlang".to_string(),
                    "make_ref".to_string(),
                    vec![],
                )),
                Box::new(CExpr::Let(
                    final_len.clone(),
                    Box::new(CExpr::Call(
                        "lists".to_string(),
                        "foldl".to_string(),
                        vec![
                            CExpr::Fun(
                                vec![elem.clone(), idx.clone()],
                                Box::new(CExpr::Let(
                                    "_VecElemInsert".to_string(),
                                    Box::new(CExpr::Call(
                                        "ets".to_string(),
                                        "insert".to_string(),
                                        vec![
                                            table.clone(),
                                            CExpr::Tuple(vec![
                                                CExpr::Tuple(vec![
                                                    CExpr::Var(id.clone()),
                                                    CExpr::Var(idx.clone()),
                                                ]),
                                                CExpr::Var(elem),
                                            ]),
                                        ],
                                    )),
                                    Box::new(CExpr::Call(
                                        "erlang".to_string(),
                                        "+".to_string(),
                                        vec![CExpr::Var(idx), CExpr::Lit(CLit::Int(1))],
                                    )),
                                )),
                            ),
                            CExpr::Lit(CLit::Int(0)),
                            CExpr::Var("_Arg0".to_string()),
                        ],
                    )),
                    Box::new(CExpr::Let(
                        d,
                        Box::new(CExpr::Call(
                            "ets".to_string(),
                            "insert".to_string(),
                            vec![
                                table,
                                CExpr::Tuple(vec![
                                    CExpr::Tuple(vec![CExpr::Var(id.clone()), length_atom]),
                                    CExpr::Var(final_len),
                                ]),
                            ],
                        )),
                        Box::new(CExpr::Var(id)),
                    )),
                )),
            )
        }
        _ => CExpr::Call(
            "erlang".to_string(),
            "exit".to_string(),
            vec![CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("not_implemented_native_op".to_string())),
                CExpr::Lit(CLit::Atom("Std.Vec.Vec".to_string())),
                CExpr::Lit(CLit::Atom(op.name.to_string())),
            ])],
        ),
    }
}

fn vec_lookup_value(table: CExpr, key: CExpr, lookup_name: &str, value_name: &str) -> CExpr {
    CExpr::Let(
        lookup_name.to_string(),
        Box::new(CExpr::Call(
            "ets".to_string(),
            "lookup".to_string(),
            vec![table, key],
        )),
        Box::new(CExpr::Case(
            Box::new(CExpr::Var(lookup_name.to_string())),
            vec![CArm {
                pat: CPat::Cons(
                    Box::new(CPat::Tuple(vec![
                        CPat::Wildcard,
                        CPat::Var(value_name.to_string()),
                    ])),
                    Box::new(CPat::Nil),
                ),
                guard: None,
                body: CExpr::Var(value_name.to_string()),
            }],
        )),
    )
}

fn ref_op_tuple(backend: RefBackend) -> CExpr {
    let ops = [
        NativeOp {
            name: "get",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "modify",
            erl_module: "",
            erl_func: "",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "new",
            erl_module: "",
            erl_func: "",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
        },
        NativeOp {
            name: "set",
            erl_module: "",
            erl_func: "",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
        },
    ];
    CExpr::Tuple(
        ops.iter()
            .map(|op| build_ref_op_closure(op, backend))
            .collect(),
    )
}

fn build_ref_op_closure(op: &NativeOp, backend: RefBackend) -> CExpr {
    let mut params: Vec<String> = (0..op.param_count).map(|i| format!("_Arg{}", i)).collect();
    let evidence_var = "_EvidenceAtPerform".to_string();
    let k_var = "_K".to_string();
    params.push(evidence_var.clone());
    params.push(k_var.clone());
    let result_expr = build_ref_call(op, &evidence_var, backend);
    CExpr::Fun(
        params,
        Box::new(CExpr::Apply(Box::new(CExpr::Var(k_var)), vec![result_expr])),
    )
}

fn build_ref_call(op: &NativeOp, evidence_var: &str, backend: RefBackend) -> CExpr {
    match backend {
        RefBackend::ProcessDictionary => build_ref_procdict_call(op, evidence_var),
        RefBackend::Ets => build_ref_ets_call(op, evidence_var),
    }
}

fn build_ref_procdict_call(op: &NativeOp, evidence_var: &str) -> CExpr {
    match op.name {
        "new" => {
            let key = "_RefKey".to_string();
            let discard = "_RefPut".to_string();
            CExpr::Let(
                key.clone(),
                Box::new(CExpr::Call(
                    "erlang".to_string(),
                    "make_ref".to_string(),
                    vec![],
                )),
                Box::new(CExpr::Let(
                    discard,
                    Box::new(CExpr::Call(
                        "erlang".to_string(),
                        "put".to_string(),
                        vec![CExpr::Var(key.clone()), CExpr::Var("_Arg0".to_string())],
                    )),
                    Box::new(CExpr::Var(key)),
                )),
            )
        }
        "get" => CExpr::Call(
            "erlang".to_string(),
            "get".to_string(),
            vec![CExpr::Var("_Arg0".to_string())],
        ),
        "set" => {
            let discard = "_RefPut".to_string();
            CExpr::Let(
                discard,
                Box::new(CExpr::Call(
                    "erlang".to_string(),
                    "put".to_string(),
                    vec![
                        CExpr::Var("_Arg0".to_string()),
                        CExpr::Var("_Arg1".to_string()),
                    ],
                )),
                Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
            )
        }
        "modify" => {
            let old = "_RefOld".to_string();
            let new_value = "_RefNew".to_string();
            let discard = "_RefPut".to_string();
            let k_var = "_RefK".to_string();
            let v_var = "_RefV".to_string();
            let id_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
            let apply_f = CExpr::Apply(
                Box::new(CExpr::Var("_Arg1".to_string())),
                vec![
                    CExpr::Var(old.clone()),
                    CExpr::Var(evidence_var.to_string()),
                    CExpr::Var(k_var.clone()),
                ],
            );
            CExpr::Let(
                old.clone(),
                Box::new(CExpr::Call(
                    "erlang".to_string(),
                    "get".to_string(),
                    vec![CExpr::Var("_Arg0".to_string())],
                )),
                Box::new(CExpr::Let(
                    k_var,
                    Box::new(id_k),
                    Box::new(CExpr::Let(
                        new_value.clone(),
                        Box::new(apply_f),
                        Box::new(CExpr::Let(
                            discard,
                            Box::new(CExpr::Call(
                                "erlang".to_string(),
                                "put".to_string(),
                                vec![
                                    CExpr::Var("_Arg0".to_string()),
                                    CExpr::Var(new_value.clone()),
                                ],
                            )),
                            Box::new(CExpr::Var(new_value)),
                        )),
                    )),
                )),
            )
        }
        _ => CExpr::Call(
            "erlang".to_string(),
            "exit".to_string(),
            vec![CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("not_implemented_native_op".to_string())),
                CExpr::Lit(CLit::Atom("Std.Ref.Ref".to_string())),
                CExpr::Lit(CLit::Atom(op.name.to_string())),
            ])],
        ),
    }
}

fn build_ref_ets_call(op: &NativeOp, evidence_var: &str) -> CExpr {
    let table = CExpr::Lit(CLit::Atom("saga_ref_store".to_string()));
    match op.name {
        "new" => {
            let key = "_RefKey".to_string();
            let discard = "_RefInsert".to_string();
            CExpr::Let(
                key.clone(),
                Box::new(CExpr::Call(
                    "erlang".to_string(),
                    "make_ref".to_string(),
                    vec![],
                )),
                Box::new(CExpr::Let(
                    discard,
                    Box::new(CExpr::Call(
                        "ets".to_string(),
                        "insert".to_string(),
                        vec![
                            table,
                            CExpr::Tuple(vec![
                                CExpr::Var(key.clone()),
                                CExpr::Var("_Arg0".to_string()),
                            ]),
                        ],
                    )),
                    Box::new(CExpr::Var(key)),
                )),
            )
        }
        "get" => {
            let lookup = "_RefLookup".to_string();
            let value = "_RefValue".to_string();
            CExpr::Let(
                lookup.clone(),
                Box::new(CExpr::Call(
                    "ets".to_string(),
                    "lookup".to_string(),
                    vec![table, CExpr::Var("_Arg0".to_string())],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(value.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Var(value),
                    }],
                )),
            )
        }
        "set" => {
            let discard = "_RefInsert".to_string();
            CExpr::Let(
                discard,
                Box::new(CExpr::Call(
                    "ets".to_string(),
                    "insert".to_string(),
                    vec![
                        table,
                        CExpr::Tuple(vec![
                            CExpr::Var("_Arg0".to_string()),
                            CExpr::Var("_Arg1".to_string()),
                        ]),
                    ],
                )),
                Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
            )
        }
        "modify" => {
            let lookup = "_RefLookup".to_string();
            let old = "_RefOld".to_string();
            let new_value = "_RefNew".to_string();
            let discard = "_RefInsert".to_string();
            let k_var = "_RefK".to_string();
            let v_var = "_RefV".to_string();
            let id_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
            let apply_f = CExpr::Apply(
                Box::new(CExpr::Var("_Arg1".to_string())),
                vec![
                    CExpr::Var(old.clone()),
                    CExpr::Var(evidence_var.to_string()),
                    CExpr::Var(k_var.clone()),
                ],
            );
            CExpr::Let(
                lookup.clone(),
                Box::new(CExpr::Call(
                    "ets".to_string(),
                    "lookup".to_string(),
                    vec![table.clone(), CExpr::Var("_Arg0".to_string())],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(old.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Let(
                            k_var,
                            Box::new(id_k),
                            Box::new(CExpr::Let(
                                new_value.clone(),
                                Box::new(apply_f),
                                Box::new(CExpr::Let(
                                    discard,
                                    Box::new(CExpr::Call(
                                        "ets".to_string(),
                                        "insert".to_string(),
                                        vec![
                                            table,
                                            CExpr::Tuple(vec![
                                                CExpr::Var("_Arg0".to_string()),
                                                CExpr::Var(new_value.clone()),
                                            ]),
                                        ],
                                    )),
                                    Box::new(CExpr::Var(new_value)),
                                )),
                            )),
                        ),
                    }],
                )),
            )
        }
        _ => CExpr::Call(
            "erlang".to_string(),
            "exit".to_string(),
            vec![CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("not_implemented_native_op".to_string())),
                CExpr::Lit(CLit::Atom("Std.Ref.Ref".to_string())),
                CExpr::Lit(CLit::Atom(op.name.to_string())),
            ])],
        ),
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
    let identity_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
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
