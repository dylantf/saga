/// BEAM-native interop: the single source of truth for how saga types and
/// effect operations map to Erlang runtime representations.
///
/// This module defines:
/// - Op->BIF mappings for BEAM-native effect operations (spawn, send, exit, etc.)
/// - Bidirectional ExitReason conversion (saga ADT <-> raw Erlang atoms)
/// - SystemMsg pattern shapes (Down/Exit <-> Erlang tuple layouts)
/// - BEAM-native handler identification
use std::collections::HashMap;

use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::util::{cerl_call, mangle_ctor_atom};

// ---------------------------------------------------------------------------
// BEAM-native handler registry
// ---------------------------------------------------------------------------

/// Registry entry for a handler that skips CPS and lowers effect ops to direct
/// BEAM calls. Resource flags indicate what runtime initialization is needed.
struct BeamNativeHandler {
    source_module: &'static str,
    canonical_name: &'static str,
    needs_ets_table: bool,
    needs_vec_table: bool,
}

const BEAM_NATIVE_HANDLERS: &[BeamNativeHandler] = &[
    BeamNativeHandler {
        source_module: "Std.Actor",
        canonical_name: "Std.Actor.beam_actor",
        needs_ets_table: false,
        needs_vec_table: false,
    },
    BeamNativeHandler {
        source_module: "Std.Ref",
        canonical_name: "Std.Ref.beam_ref",
        needs_ets_table: false,
        needs_vec_table: false,
    },
    BeamNativeHandler {
        source_module: "Std.Ref",
        canonical_name: "Std.Ref.ets_ref",
        needs_ets_table: true,
        needs_vec_table: false,
    },
    BeamNativeHandler {
        source_module: "Std.Vec",
        canonical_name: "Std.Vec.beam_vec",
        needs_ets_table: false,
        needs_vec_table: true,
    },
];

/// Check if a handler is BEAM-native by its source module and canonical name.
pub fn is_beam_native_handler(source_module: &str, canonical_name: &str) -> bool {
    BEAM_NATIVE_HANDLERS
        .iter()
        .any(|h| h.source_module == source_module && h.canonical_name == canonical_name)
}

/// Check if a canonical handler name requires ETS table initialization.
pub fn handler_needs_ets_table(canonical_name: &str) -> bool {
    BEAM_NATIVE_HANDLERS
        .iter()
        .any(|h| h.canonical_name == canonical_name && h.needs_ets_table)
}

/// Check if a canonical handler name requires vec table initialization.
pub fn handler_needs_vec_table(canonical_name: &str) -> bool {
    BEAM_NATIVE_HANDLERS
        .iter()
        .any(|h| h.canonical_name == canonical_name && h.needs_vec_table)
}

// ---------------------------------------------------------------------------
// BEAM-native operation table
// ---------------------------------------------------------------------------

/// How to transform saga-side arguments into BEAM call arguments.
enum ArgTransform {
    /// Pass args through in order.
    Identity,
    /// No args (e.g., `self`).
    NoArgs,
    /// Prepend a literal atom before all args (e.g., monitor gets `'process'`).
    PrependAtom(&'static str),
    /// Reorder args by index (e.g., send_after: `[1, 0, 2]` = pid,ms,msg -> ms,pid,msg).
    Reorder(&'static [usize]),
    /// Wrap the arg at the given index in a zero-arity thunk that calls it with `unit`.
    WrapThunk(usize),
}

/// A BEAM-native effect operation descriptor.
struct BeamNativeOp {
    module: &'static str,
    func: &'static str,
    /// Number of saga-side parameters (before transform).
    param_count: usize,
    arg_transform: ArgTransform,
    /// If Some(index), that argument is an ExitReason ADT that must be
    /// unwrapped to a raw Erlang term before calling the BIF.
    exit_reason_arg: Option<usize>,
}

const BEAM_NATIVE_OPS: &[(&str, BeamNativeOp)] = &[
    (
        "spawn",
        BeamNativeOp {
            module: "erlang",
            func: "spawn",
            param_count: 1,
            arg_transform: ArgTransform::WrapThunk(0),
            exit_reason_arg: None,
        },
    ),
    (
        "self",
        BeamNativeOp {
            module: "erlang",
            func: "self",
            param_count: 0,
            arg_transform: ArgTransform::NoArgs,
            exit_reason_arg: None,
        },
    ),
    (
        "exit",
        BeamNativeOp {
            module: "erlang",
            func: "exit",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: Some(1),
        },
    ),
    (
        "send",
        BeamNativeOp {
            module: "erlang",
            func: "send",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "monitor",
        BeamNativeOp {
            module: "erlang",
            func: "monitor",
            param_count: 1,
            arg_transform: ArgTransform::PrependAtom("process"),
            exit_reason_arg: None,
        },
    ),
    (
        "demonitor",
        BeamNativeOp {
            module: "erlang",
            func: "demonitor",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "link",
        BeamNativeOp {
            module: "erlang",
            func: "link",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "unlink",
        BeamNativeOp {
            module: "erlang",
            func: "unlink",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "sleep",
        BeamNativeOp {
            module: "timer",
            func: "sleep",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "cancel_timer",
        BeamNativeOp {
            module: "erlang",
            func: "cancel_timer",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "send_after",
        BeamNativeOp {
            module: "erlang",
            func: "send_after",
            param_count: 3,
            arg_transform: ArgTransform::Reorder(&[1, 0, 2]),
            exit_reason_arg: None,
        },
    ),
    // Ref ops — param counts only; actual lowering is handler-specific
    // (beam_ref vs ets_ref) and handled by build_ref_native_call.
    (
        "new",
        BeamNativeOp {
            module: "erlang",
            func: "make_ref",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "get",
        BeamNativeOp {
            module: "erlang",
            func: "get",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "set",
        BeamNativeOp {
            module: "erlang",
            func: "put",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "modify",
        BeamNativeOp {
            module: "erlang",
            func: "get",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    // Vec ops — param counts only; actual lowering handled by build_vec_native_call.
    (
        "vec_new",
        BeamNativeOp {
            module: "erlang",
            func: "make_ref",
            param_count: 0,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "vec_push",
        BeamNativeOp {
            module: "ets",
            func: "insert",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "vec_get",
        BeamNativeOp {
            module: "ets",
            func: "lookup",
            param_count: 2,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "vec_set",
        BeamNativeOp {
            module: "ets",
            func: "insert",
            param_count: 3,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "vec_pop",
        BeamNativeOp {
            module: "ets",
            func: "lookup",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "vec_len",
        BeamNativeOp {
            module: "ets",
            func: "lookup",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "freeze",
        BeamNativeOp {
            module: "ets",
            func: "lookup",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
    (
        "thaw",
        BeamNativeOp {
            module: "ets",
            func: "insert",
            param_count: 1,
            arg_transform: ArgTransform::Identity,
            exit_reason_arg: None,
        },
    ),
];

/// Look up a BEAM-native op by name. Returns `(module, func, param_count)`.
pub fn lookup_native_op(op_name: &str) -> Option<(&'static str, &'static str, usize)> {
    BEAM_NATIVE_OPS
        .iter()
        .find(|(name, _)| *name == op_name)
        .map(|(_, op)| (op.module, op.func, op.param_count))
}

/// Build the BEAM call expression for a native op, applying arg transforms
/// and any ExitReason conversion. Returns a `CExpr` that performs the call
/// (possibly wrapped in let-bindings for conversion).
pub fn build_native_call(
    op_name: &str,
    param_vars: &[String],
    constructor_atoms: &HashMap<String, String>,
    fresh: &mut dyn FnMut() -> String,
) -> CExpr {
    let (_, op) = BEAM_NATIVE_OPS
        .iter()
        .find(|(name, _)| *name == op_name)
        .unwrap_or_else(|| panic!("unknown BEAM-native op: {}", op_name));

    // Build the raw arg list according to the transform.
    let raw_args: Vec<CExpr> = match &op.arg_transform {
        ArgTransform::Identity => param_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
        ArgTransform::NoArgs => vec![],
        ArgTransform::PrependAtom(atom) => {
            let mut a = vec![CExpr::Lit(CLit::Atom((*atom).into()))];
            a.extend(param_vars.iter().map(|v| CExpr::Var(v.clone())));
            a
        }
        ArgTransform::Reorder(indices) => indices
            .iter()
            .map(|&i| CExpr::Var(param_vars[i].clone()))
            .collect(),
        ArgTransform::WrapThunk(idx) => param_vars
            .iter()
            .enumerate()
            .map(|(i, v)| {
                if i == *idx {
                    CExpr::Fun(
                        vec![],
                        Box::new(CExpr::Apply(
                            Box::new(CExpr::Var(v.clone())),
                            vec![CExpr::Lit(CLit::Atom("unit".into()))],
                        )),
                    )
                } else {
                    CExpr::Var(v.clone())
                }
            })
            .collect(),
    };

    // If an arg needs ExitReason ADT->Erlang conversion, wrap it.
    if let Some(arg_idx) = op.exit_reason_arg {
        let adt_var = &param_vars[arg_idx];
        let converted_var = fresh();
        let conversion = build_exit_reason_to_erlang(adt_var, constructor_atoms, fresh);
        // Replace that arg position in raw_args with the converted var.
        let call_args: Vec<CExpr> = raw_args
            .into_iter()
            .enumerate()
            .map(|(i, arg)| {
                let is_target = match &op.arg_transform {
                    ArgTransform::Reorder(indices) => indices.get(i) == Some(&arg_idx),
                    ArgTransform::WrapThunk(idx) => *idx == arg_idx && i == arg_idx,
                    _ => i == arg_idx,
                };
                if is_target {
                    CExpr::Var(converted_var.clone())
                } else {
                    arg
                }
            })
            .collect();
        let call = CExpr::Call(op.module.to_string(), op.func.to_string(), call_args);
        CExpr::Let(converted_var, Box::new(conversion), Box::new(call))
    } else {
        CExpr::Call(op.module.to_string(), op.func.to_string(), raw_args)
    }
}

// ---------------------------------------------------------------------------
// Ref: handler-specific lowering
// ---------------------------------------------------------------------------

/// Check if an op is a Ref effect op that needs handler-specific lowering.
pub fn is_ref_op(op_name: &str) -> bool {
    matches!(op_name, "new" | "get" | "set" | "modify")
}

/// Build the CExpr for a Ref op, dispatching on handler identity.
/// `handler_canonical` is e.g. "Std.Ref.beam_ref" or "Std.Ref.ets_ref".
pub fn build_ref_native_call(
    handler_canonical: &str,
    op_name: &str,
    param_vars: &[String],
    fresh: &mut dyn FnMut() -> String,
) -> CExpr {
    if handler_canonical.ends_with("beam_ref") {
        build_ref_procdict(op_name, param_vars, fresh)
    } else {
        build_ref_ets(op_name, param_vars, fresh)
    }
}

/// Process-dictionary-backed Ref ops.
fn build_ref_procdict(
    op_name: &str,
    param_vars: &[String],
    fresh: &mut dyn FnMut() -> String,
) -> CExpr {
    match op_name {
        // new(val) -> let Key = erlang:make_ref() in let _ = erlang:put(Key, Val) in Key
        "new" => {
            let key = fresh();
            let discard = fresh();
            CExpr::Let(
                key.clone(),
                Box::new(cerl_call("erlang", "make_ref", vec![])),
                Box::new(CExpr::Let(
                    discard,
                    Box::new(cerl_call(
                        "erlang",
                        "put",
                        vec![CExpr::Var(key.clone()), CExpr::Var(param_vars[0].clone())],
                    )),
                    Box::new(CExpr::Var(key)),
                )),
            )
        }
        // get(ref) -> erlang:get(Ref)
        "get" => cerl_call("erlang", "get", vec![CExpr::Var(param_vars[0].clone())]),
        // set(ref, val) -> let _ = erlang:put(Ref, Val) in 'unit'
        "set" => {
            let discard = fresh();
            CExpr::Let(
                discard,
                Box::new(cerl_call(
                    "erlang",
                    "put",
                    vec![
                        CExpr::Var(param_vars[0].clone()),
                        CExpr::Var(param_vars[1].clone()),
                    ],
                )),
                Box::new(CExpr::Lit(CLit::Atom("unit".into()))),
            )
        }
        // modify(ref, f) -> let Old = erlang:get(Ref) in let New = apply F(Old) in let _ = erlang:put(Ref, New) in New
        "modify" => {
            let old = fresh();
            let new_val = fresh();
            let discard = fresh();
            CExpr::Let(
                old.clone(),
                Box::new(cerl_call(
                    "erlang",
                    "get",
                    vec![CExpr::Var(param_vars[0].clone())],
                )),
                Box::new(CExpr::Let(
                    new_val.clone(),
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(param_vars[1].clone())),
                        vec![CExpr::Var(old)],
                    )),
                    Box::new(CExpr::Let(
                        discard,
                        Box::new(cerl_call(
                            "erlang",
                            "put",
                            vec![
                                CExpr::Var(param_vars[0].clone()),
                                CExpr::Var(new_val.clone()),
                            ],
                        )),
                        Box::new(CExpr::Var(new_val)),
                    )),
                )),
            )
        }
        _ => panic!("unknown Ref op: {op_name}"),
    }
}

/// ETS-backed Ref ops. Uses a well-known named table `saga_ref_store`.
fn build_ref_ets(op_name: &str, param_vars: &[String], fresh: &mut dyn FnMut() -> String) -> CExpr {
    let table = CExpr::Lit(CLit::Atom("saga_ref_store".into()));

    match op_name {
        // new(val) -> let Key = erlang:make_ref() in let _ = ets:insert(Table, {Key, Val}) in Key
        "new" => {
            let key = fresh();
            let discard = fresh();
            CExpr::Let(
                key.clone(),
                Box::new(cerl_call("erlang", "make_ref", vec![])),
                Box::new(CExpr::Let(
                    discard,
                    Box::new(cerl_call(
                        "ets",
                        "insert",
                        vec![
                            table,
                            CExpr::Tuple(vec![
                                CExpr::Var(key.clone()),
                                CExpr::Var(param_vars[0].clone()),
                            ]),
                        ],
                    )),
                    Box::new(CExpr::Var(key)),
                )),
            )
        }
        // get(ref) -> let [{_, Val}] = ets:lookup(Table, Ref) in Val
        "get" => {
            let lookup_result = fresh();
            let val = fresh();
            CExpr::Let(
                lookup_result.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![table, CExpr::Var(param_vars[0].clone())],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup_result)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(val.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Var(val),
                    }],
                )),
            )
        }
        // set(ref, val) -> let _ = ets:insert(Table, {Ref, Val}) in 'unit'
        "set" => {
            let discard = fresh();
            CExpr::Let(
                discard,
                Box::new(cerl_call(
                    "ets",
                    "insert",
                    vec![
                        table,
                        CExpr::Tuple(vec![
                            CExpr::Var(param_vars[0].clone()),
                            CExpr::Var(param_vars[1].clone()),
                        ]),
                    ],
                )),
                Box::new(CExpr::Lit(CLit::Atom("unit".into()))),
            )
        }
        // modify(ref, f) -> let [{_, Old}] = ets:lookup(...) in let New = apply F(Old) in let _ = ets:insert(..., {Ref, New}) in New
        "modify" => {
            let lookup_result = fresh();
            let old = fresh();
            let new_val = fresh();
            let discard = fresh();
            CExpr::Let(
                lookup_result.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![table.clone(), CExpr::Var(param_vars[0].clone())],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup_result)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(old.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Let(
                            new_val.clone(),
                            Box::new(CExpr::Apply(
                                Box::new(CExpr::Var(param_vars[1].clone())),
                                vec![CExpr::Var(old)],
                            )),
                            Box::new(CExpr::Let(
                                discard,
                                Box::new(cerl_call(
                                    "ets",
                                    "insert",
                                    vec![
                                        table,
                                        CExpr::Tuple(vec![
                                            CExpr::Var(param_vars[0].clone()),
                                            CExpr::Var(new_val.clone()),
                                        ]),
                                    ],
                                )),
                                Box::new(CExpr::Var(new_val)),
                            )),
                        ),
                    }],
                )),
            )
        }
        _ => panic!("unknown Ref op: {op_name}"),
    }
}

// ---------------------------------------------------------------------------
// Vec: ETS-backed mutable vector
// ---------------------------------------------------------------------------

/// Check if an op is a Vec effect op that needs handler-specific lowering.
pub fn is_vec_op(op_name: &str) -> bool {
    matches!(
        op_name,
        "vec_new" | "vec_push" | "vec_get" | "vec_set" | "vec_pop" | "vec_len" | "freeze" | "thaw"
    )
}

/// Build the CExpr for a Vec op. Always ETS-backed (single handler).
pub fn build_vec_native_call(
    op_name: &str,
    param_vars: &[String],
    fresh: &mut dyn FnMut() -> String,
) -> CExpr {
    build_vec_ets(op_name, param_vars, fresh)
}

/// ETS-backed Vec ops. Uses a dedicated named table `saga_vec_store`.
///
/// Storage layout:
/// - `{VecId, 'length'}` -> current length (Int)
/// - `{VecId, 0}` -> element at index 0
/// - `{VecId, 1}` -> element at index 1
/// - etc.
fn build_vec_ets(op_name: &str, param_vars: &[String], fresh: &mut dyn FnMut() -> String) -> CExpr {
    let table = CExpr::Lit(CLit::Atom("saga_vec_store".into()));
    let length_atom = CExpr::Lit(CLit::Atom("length".into()));

    match op_name {
        // vec_new(()) -> let Id = make_ref() in let _ = ets:insert(T, {{Id,length}, 0}) in Id
        "vec_new" => {
            let id = fresh();
            let discard = fresh();
            CExpr::Let(
                id.clone(),
                Box::new(cerl_call("erlang", "make_ref", vec![])),
                Box::new(CExpr::Let(
                    discard,
                    Box::new(cerl_call(
                        "ets",
                        "insert",
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

        // vec_push(vec, val) -> lookup length, insert at {Vec,Len}, bump length, return unit
        "vec_push" => {
            let lookup = fresh();
            let len = fresh();
            let d1 = fresh();
            let d2 = fresh();
            let vec_var = CExpr::Var(param_vars[0].clone());
            let val_var = CExpr::Var(param_vars[1].clone());

            CExpr::Let(
                lookup.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![
                        table.clone(),
                        CExpr::Tuple(vec![vec_var.clone(), length_atom.clone()]),
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
                            Box::new(cerl_call(
                                "ets",
                                "insert",
                                vec![
                                    table.clone(),
                                    CExpr::Tuple(vec![
                                        CExpr::Tuple(vec![
                                            vec_var.clone(),
                                            CExpr::Var(len.clone()),
                                        ]),
                                        val_var,
                                    ]),
                                ],
                            )),
                            Box::new(CExpr::Let(
                                d2,
                                Box::new(cerl_call(
                                    "ets",
                                    "insert",
                                    vec![
                                        table,
                                        CExpr::Tuple(vec![
                                            CExpr::Tuple(vec![vec_var, length_atom]),
                                            cerl_call(
                                                "erlang",
                                                "+",
                                                vec![CExpr::Var(len), CExpr::Lit(CLit::Int(1))],
                                            ),
                                        ]),
                                    ],
                                )),
                                Box::new(CExpr::Lit(CLit::Atom("unit".into()))),
                            )),
                        ),
                    }],
                )),
            )
        }

        // vec_get(vec, index) -> let [{_, Val}] = ets:lookup(T, {Vec, Index}) in Val
        "vec_get" => {
            let lookup = fresh();
            let val = fresh();
            CExpr::Let(
                lookup.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![
                        table,
                        CExpr::Tuple(vec![
                            CExpr::Var(param_vars[0].clone()),
                            CExpr::Var(param_vars[1].clone()),
                        ]),
                    ],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![CPat::Wildcard, CPat::Var(val.clone())])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body: CExpr::Var(val),
                    }],
                )),
            )
        }

        // vec_set(vec, index, val) -> let _ = ets:insert(T, {{Vec,Index}, Val}) in unit
        "vec_set" => {
            let d = fresh();
            CExpr::Let(
                d,
                Box::new(cerl_call(
                    "ets",
                    "insert",
                    vec![
                        table,
                        CExpr::Tuple(vec![
                            CExpr::Tuple(vec![
                                CExpr::Var(param_vars[0].clone()),
                                CExpr::Var(param_vars[1].clone()),
                            ]),
                            CExpr::Var(param_vars[2].clone()),
                        ]),
                    ],
                )),
                Box::new(CExpr::Lit(CLit::Atom("unit".into()))),
            )
        }

        // vec_pop(vec) -> lookup length, read element at len-1, delete it, decrement length, return element
        "vec_pop" => {
            let lookup = fresh();
            let len = fresh();
            let new_len = fresh();
            let elem_lookup = fresh();
            let elem = fresh();
            let d1 = fresh();
            let d2 = fresh();
            let vec_var = CExpr::Var(param_vars[0].clone());

            CExpr::Let(
                lookup.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![
                        table.clone(),
                        CExpr::Tuple(vec![vec_var.clone(), length_atom.clone()]),
                    ],
                )),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(lookup)),
                    vec![CArm {
                        pat: CPat::Cons(
                            Box::new(CPat::Tuple(vec![
                                CPat::Wildcard,
                                CPat::Var(len.clone()),
                            ])),
                            Box::new(CPat::Nil),
                        ),
                        guard: None,
                        body:
                            // new_len = len - 1
                            CExpr::Let(
                                new_len.clone(),
                                Box::new(cerl_call(
                                    "erlang",
                                    "-",
                                    vec![
                                        CExpr::Var(len),
                                        CExpr::Lit(CLit::Int(1)),
                                    ],
                                )),
                                // lookup element at new_len
                                Box::new(CExpr::Let(
                                    elem_lookup.clone(),
                                    Box::new(cerl_call(
                                        "ets",
                                        "lookup",
                                        vec![
                                            table.clone(),
                                            CExpr::Tuple(vec![
                                                vec_var.clone(),
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
                                            body:
                                                // delete the element entry
                                                CExpr::Let(
                                                    d1,
                                                    Box::new(cerl_call(
                                                        "ets",
                                                        "delete",
                                                        vec![
                                                            table.clone(),
                                                            CExpr::Tuple(vec![
                                                                vec_var.clone(),
                                                                CExpr::Var(new_len.clone()),
                                                            ]),
                                                        ],
                                                    )),
                                                    // update length
                                                    Box::new(CExpr::Let(
                                                        d2,
                                                        Box::new(cerl_call(
                                                            "ets",
                                                            "insert",
                                                            vec![
                                                                table,
                                                                CExpr::Tuple(vec![
                                                                    CExpr::Tuple(vec![
                                                                        vec_var,
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

        // vec_len(vec) -> let [{_, Len}] = ets:lookup(T, {Vec, length}) in Len
        "vec_len" => {
            let lookup = fresh();
            let len = fresh();
            CExpr::Let(
                lookup.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![
                        table,
                        CExpr::Tuple(vec![CExpr::Var(param_vars[0].clone()), length_atom]),
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
                        body: CExpr::Var(len),
                    }],
                )),
            )
        }

        // freeze(vec) -> build list from elements 0..len-1
        // Emits a call to a helper: saga_vec_freeze(Table, VecId, Len, Acc)
        // Since we can't emit recursive functions inline, we use lists:reverse
        // on a fold built from ets:lookup calls. We emit an Erlang sequence
        // that iterates via erlang:seq + lists:map + lists:reverse.
        //
        // Actually, simplest approach: use ets:match to get all element entries,
        // then sort by index. But ets:match returns unordered results.
        //
        // Practical approach: build the list backwards from len-1 to 0 using
        // a generated chain of lets. But we don't know len at compile time.
        //
        // Best runtime approach: call a helper BIF sequence:
        //   Indices = lists:seq(0, Len-1)
        //   Elements = lists:map(fun(I) -> [{_, V}] = ets:lookup(T, {Vec, I}), V end, Indices)
        "freeze" => {
            let lookup = fresh();
            let len = fresh();
            let last_idx = fresh();
            let indices = fresh();
            let idx_var = fresh();
            let inner_lookup = fresh();
            let inner_val = fresh();
            let vec_var = CExpr::Var(param_vars[0].clone());

            // Lookup length
            CExpr::Let(
                lookup.clone(),
                Box::new(cerl_call(
                    "ets",
                    "lookup",
                    vec![
                        table.clone(),
                        CExpr::Tuple(vec![vec_var.clone(), length_atom]),
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
                        body: CExpr::Case(
                            Box::new(CExpr::Var(len.clone())),
                            vec![
                                // Length 0 -> empty list
                                CArm {
                                    pat: CPat::Lit(CLit::Int(0)),
                                    guard: None,
                                    body: CExpr::Nil,
                                },
                                // Length > 0 -> lists:seq(0, Len-1) |> lists:map(lookup, _)
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: CExpr::Let(
                                        last_idx.clone(),
                                        Box::new(cerl_call(
                                            "erlang",
                                            "-",
                                            vec![CExpr::Var(len), CExpr::Lit(CLit::Int(1))],
                                        )),
                                        Box::new(CExpr::Let(
                                            indices.clone(),
                                            Box::new(cerl_call(
                                                "lists",
                                                "seq",
                                                vec![
                                                    CExpr::Lit(CLit::Int(0)),
                                                    CExpr::Var(last_idx),
                                                ],
                                            )),
                                            // lists:map(fun(I) -> element(2, hd(ets:lookup(T, {V, I}))) end, Indices)
                                            Box::new(cerl_call(
                                                "lists",
                                                "map",
                                                vec![
                                                    CExpr::Fun(
                                                        vec![idx_var.clone()],
                                                        Box::new(CExpr::Let(
                                                            inner_lookup.clone(),
                                                            Box::new(cerl_call(
                                                                "ets",
                                                                "lookup",
                                                                vec![
                                                                    table,
                                                                    CExpr::Tuple(vec![
                                                                        vec_var,
                                                                        CExpr::Var(idx_var),
                                                                    ]),
                                                                ],
                                                            )),
                                                            Box::new(CExpr::Case(
                                                                Box::new(CExpr::Var(inner_lookup)),
                                                                vec![CArm {
                                                                    pat: CPat::Cons(
                                                                        Box::new(CPat::Tuple(
                                                                            vec![
                                                                                CPat::Wildcard,
                                                                                CPat::Var(
                                                                                    inner_val
                                                                                        .clone(),
                                                                                ),
                                                                            ],
                                                                        )),
                                                                        Box::new(CPat::Nil),
                                                                    ),
                                                                    guard: None,
                                                                    body: CExpr::Var(inner_val),
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
                        ),
                    }],
                )),
            )
        }

        // thaw(list) -> create vec, bulk-insert elements with indices
        // Uses lists:foldl to insert each element with an incrementing index.
        "thaw" => {
            let id = fresh();
            let d_init = fresh();
            let list_var = CExpr::Var(param_vars[0].clone());
            let acc_var = fresh();
            let elem_var = fresh();
            let d_insert = fresh();
            let final_len = fresh();
            let d_len = fresh();

            // Create new vec id and init length to 0
            CExpr::Let(
                id.clone(),
                Box::new(cerl_call("erlang", "make_ref", vec![])),
                Box::new(CExpr::Let(
                    d_init.clone(),
                    Box::new(cerl_call(
                        "ets",
                        "insert",
                        vec![
                            table.clone(),
                            CExpr::Tuple(vec![
                                CExpr::Tuple(vec![CExpr::Var(id.clone()), length_atom.clone()]),
                                CExpr::Lit(CLit::Int(0)),
                            ]),
                        ],
                    )),
                    // Use lists:foldl to insert elements with incrementing index
                    // foldl(fun(Elem, Idx) -> ets:insert(T, {{Id, Idx}, Elem}), Idx+1 end, 0, List)
                    Box::new(CExpr::Let(
                        final_len.clone(),
                        Box::new(cerl_call(
                            "lists",
                            "foldl",
                            vec![
                                CExpr::Fun(
                                    vec![elem_var.clone(), acc_var.clone()],
                                    Box::new(CExpr::Let(
                                        d_insert.clone(),
                                        Box::new(cerl_call(
                                            "ets",
                                            "insert",
                                            vec![
                                                table.clone(),
                                                CExpr::Tuple(vec![
                                                    CExpr::Tuple(vec![
                                                        CExpr::Var(id.clone()),
                                                        CExpr::Var(acc_var.clone()),
                                                    ]),
                                                    CExpr::Var(elem_var),
                                                ]),
                                            ],
                                        )),
                                        Box::new(cerl_call(
                                            "erlang",
                                            "+",
                                            vec![CExpr::Var(acc_var), CExpr::Lit(CLit::Int(1))],
                                        )),
                                    )),
                                ),
                                CExpr::Lit(CLit::Int(0)),
                                list_var,
                            ],
                        )),
                        // Update length to final count
                        Box::new(CExpr::Let(
                            d_len,
                            Box::new(cerl_call(
                                "ets",
                                "insert",
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
                )),
            )
        }

        _ => panic!("unknown Vec op: {op_name}"),
    }
}

// ---------------------------------------------------------------------------
// ExitReason: bidirectional conversion
// ---------------------------------------------------------------------------

/// Nullary ExitReason variants and their corresponding Erlang atoms.
const EXIT_REASON_ATOMS: &[(&str, &str)] = &[
    ("Normal", "normal"),
    ("Shutdown", "shutdown"),
    ("Killed", "killed"),
    ("Noproc", "noproc"),
];

/// If `ctor_name` is a nullary ExitReason variant, return the raw Erlang atom.
/// Used by constructor and pattern lowering to emit bare atoms instead of
/// wrapped tuples.
pub fn exit_reason_bare_atom(ctor_name: &str) -> Option<&'static str> {
    EXIT_REASON_ATOMS
        .iter()
        .find(|(name, _)| *name == ctor_name)
        .map(|(_, atom)| *atom)
}

/// Build a `CExpr` that converts a saga ExitReason ADT value to the raw
/// Erlang term that `erlang:exit/2` expects.
///
/// Nullary variants (Normal, Shutdown, etc.) are already bare atoms from
/// constructor lowering, so they pass through. Payload variants (Error, Other)
/// are unwrapped to their inner value.
pub fn build_exit_reason_to_erlang(
    adt_var: &str,
    constructor_atoms: &HashMap<String, String>,
    fresh: &mut dyn FnMut() -> String,
) -> CExpr {
    let error_atom = mangle_ctor_atom("Error", constructor_atoms);
    let other_atom = mangle_ctor_atom("Other", constructor_atoms);

    let mut arms: Vec<CArm> = Vec::new();

    // Nullary variants: bare atom passes through unchanged.
    for (_, erlang_atom) in EXIT_REASON_ATOMS {
        arms.push(CArm {
            pat: CPat::Lit(CLit::Atom((*erlang_atom).into())),
            guard: None,
            body: CExpr::Lit(CLit::Atom((*erlang_atom).into())),
        });
    }

    // Error(msg) -> msg (unwrap to raw term)
    let error_msg = fresh();
    arms.push(CArm {
        pat: CPat::Tuple(vec![
            CPat::Lit(CLit::Atom(error_atom)),
            CPat::Var(error_msg.clone()),
        ]),
        guard: None,
        body: CExpr::Var(error_msg),
    });

    // Other(msg) -> msg (unwrap to raw term)
    let other_msg = fresh();
    arms.push(CArm {
        pat: CPat::Tuple(vec![
            CPat::Lit(CLit::Atom(other_atom)),
            CPat::Var(other_msg.clone()),
        ]),
        guard: None,
        body: CExpr::Var(other_msg),
    });

    // Fallback: pass through unchanged
    let fallback = fresh();
    arms.push(CArm {
        pat: CPat::Var(fallback.clone()),
        guard: None,
        body: CExpr::Var(fallback),
    });

    CExpr::Case(Box::new(CExpr::Var(adt_var.to_string())), arms)
}

/// Build a `CExpr` that converts a raw Erlang exit reason (from a monitor DOWN
/// or linked EXIT message) into a saga ExitReason ADT value.
pub fn build_exit_reason_from_erlang(
    raw_var: &str,
    constructor_atoms: &HashMap<String, String>,
    fresh: &mut dyn FnMut() -> String,
) -> CExpr {
    let normal = mangle_ctor_atom("Normal", constructor_atoms);
    let shutdown = mangle_ctor_atom("Shutdown", constructor_atoms);
    let killed = mangle_ctor_atom("Killed", constructor_atoms);
    let noproc = mangle_ctor_atom("Noproc", constructor_atoms);
    let error = mangle_ctor_atom("Error", constructor_atoms);
    let other = mangle_ctor_atom("Other", constructor_atoms);

    let other_var = fresh();
    let fmt_var = fresh();
    let stringify = cerl_call(
        "unicode",
        "characters_to_binary",
        vec![cerl_call(
            "io_lib",
            "format",
            vec![
                CExpr::Lit(CLit::Str("~p".into())),
                CExpr::Cons(
                    Box::new(CExpr::Var(other_var.clone())),
                    Box::new(CExpr::Nil),
                ),
            ],
        )],
    );

    let error_msg_var = fresh();
    let error_msg_var2 = fresh();

    let arms = vec![
        CArm {
            pat: CPat::Lit(CLit::Atom("normal".into())),
            guard: None,
            body: CExpr::Lit(CLit::Atom(normal)),
        },
        CArm {
            pat: CPat::Lit(CLit::Atom("shutdown".into())),
            guard: None,
            body: CExpr::Lit(CLit::Atom(shutdown)),
        },
        CArm {
            pat: CPat::Lit(CLit::Atom("killed".into())),
            guard: None,
            body: CExpr::Lit(CLit::Atom(killed)),
        },
        CArm {
            pat: CPat::Lit(CLit::Atom("noproc".into())),
            guard: None,
            body: CExpr::Lit(CLit::Atom(noproc)),
        },
        // {{saga_error, _Kind, Msg, ...}, _Stacktrace} -> Error(Msg)
        CArm {
            pat: CPat::Tuple(vec![
                CPat::Tuple(vec![
                    CPat::Lit(CLit::Atom("saga_error".into())),
                    CPat::Wildcard, // kind
                    CPat::Var(error_msg_var.clone()),
                    CPat::Wildcard, // module
                    CPat::Wildcard, // function
                    CPat::Wildcard, // file
                    CPat::Wildcard, // line
                ]),
                CPat::Wildcard, // stacktrace
            ]),
            guard: None,
            body: CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom(error.clone())),
                CExpr::Var(error_msg_var),
            ]),
        },
        // {Msg, _Stacktrace} when is_binary(Msg) -> Error(Msg)
        CArm {
            pat: CPat::Tuple(vec![
                CPat::Var(error_msg_var2.clone()),
                CPat::Wildcard, // stacktrace
            ]),
            guard: Some(cerl_call(
                "erlang",
                "is_binary",
                vec![CExpr::Var(error_msg_var2.clone())],
            )),
            body: CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom(error)),
                CExpr::Var(error_msg_var2),
            ]),
        },
        // Other -> Other(io_lib:format("~p", [Other]))
        CArm {
            pat: CPat::Var(other_var.clone()),
            guard: None,
            body: CExpr::Let(
                fmt_var.clone(),
                Box::new(stringify),
                Box::new(CExpr::Tuple(vec![
                    CExpr::Lit(CLit::Atom(other)),
                    CExpr::Var(fmt_var),
                ])),
            ),
        },
    ];

    CExpr::Case(Box::new(CExpr::Var(raw_var.to_string())), arms)
}

// ---------------------------------------------------------------------------
// SystemMsg: receive pattern shapes
// ---------------------------------------------------------------------------

/// Check if a constructor name is a known system message pattern for receive.
pub fn is_system_msg(ctor_name: &str) -> bool {
    matches!(ctor_name, "Down" | "Exit")
}

/// Build the Erlang tuple pattern for a system message in a receive arm.
///
/// - `Down(pid, reason)` -> `{'DOWN', _Ref, 'process', PidPat, ReasonPat}`
/// - `Exit(pid, reason)` -> `{'EXIT', PidPat, ReasonPat}`
pub fn build_system_msg_pattern(ctor_name: &str, pid_pat: CPat, reason_pat: CPat) -> CPat {
    match ctor_name {
        "Down" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("DOWN".into())),
            CPat::Wildcard,
            CPat::Lit(CLit::Atom("process".into())),
            pid_pat,
            reason_pat,
        ]),
        "Exit" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("EXIT".into())),
            pid_pat,
            reason_pat,
        ]),
        _ => unreachable!("not a system message: {}", ctor_name),
    }
}
