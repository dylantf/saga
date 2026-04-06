/// BEAM-native interop: the single source of truth for how dylang types and
/// effect operations map to Erlang runtime representations.
///
/// This module defines:
/// - Op->BIF mappings for BEAM-native effect operations (spawn, send, exit, etc.)
/// - Bidirectional ExitReason conversion (dylang ADT <-> raw Erlang atoms)
/// - SystemMsg pattern shapes (Down/Exit <-> Erlang tuple layouts)
/// - BEAM-native handler identification
use std::collections::HashMap;

use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::util::{cerl_call, mangle_ctor_atom};

// ---------------------------------------------------------------------------
// BEAM-native handler registry
// ---------------------------------------------------------------------------

/// (source_module, canonical_handler_name) pairs for handlers that skip CPS
/// and lower effect ops to direct BEAM calls.
const BEAM_NATIVE_HANDLERS: &[(&str, &str)] = &[("Std.Actor", "Std.Actor.beam_actor")];

/// Check if a handler is BEAM-native by its source module and canonical name.
pub fn is_beam_native_handler(source_module: &str, canonical_name: &str) -> bool {
    BEAM_NATIVE_HANDLERS
        .iter()
        .any(|(m, h)| *m == source_module && *h == canonical_name)
}

// ---------------------------------------------------------------------------
// BEAM-native operation table
// ---------------------------------------------------------------------------

/// How to transform dylang-side arguments into BEAM call arguments.
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
    /// Number of dylang-side parameters (before transform).
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

/// Build a `CExpr` that converts a dylang ExitReason ADT value to the raw
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
/// or linked EXIT message) into a dylang ExitReason ADT value.
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
        // {{dylang_error, _Kind, Msg, ...}, _Stacktrace} -> Error(Msg)
        CArm {
            pat: CPat::Tuple(vec![
                CPat::Tuple(vec![
                    CPat::Lit(CLit::Atom("dylang_error".into())),
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
