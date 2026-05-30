//! Static metadata for BEAM-native default handlers.

/// A single BEAM-native op stub entry: how to forward saga-side args to
/// the underlying BIF.
pub(super) struct NativeOp {
    /// Source op name (matches the Saga effect-decl op name).
    pub(super) name: &'static str,
    /// Erlang module/function the BIF lives in. Empty `module` ("") means
    /// "handled by bespoke lowering or not implemented in this scaffold".
    pub(super) erl_module: &'static str,
    pub(super) erl_func: &'static str,
    /// Number of saga-side args this op takes. Closure arity is
    /// `param_count + 2` (perform-site evidence + trailing K continuation).
    pub(super) param_count: usize,
    pub(super) arg_transform: ArgTransform,
}

pub(super) enum ArgTransform {
    Identity,
    NoArgs,
    PrependAtom(&'static str),
    Reorder(&'static [usize]),
    WrapThunk(usize),
}

/// A BEAM-native effect + its ops in canonical (alphabetical) order.
///
/// The effect tag is the canonical effect name as it appears in
/// `find_evidence`'s lookup (`'Std.Actor.Process'`, `'Std.Actor.Timer'`, ...).
/// Ops are pre-sorted; the runtime indexes them via `element(op_index,
/// OpTuple)`.
pub(super) struct NativeEffect {
    pub(super) tag: &'static str,
    pub(super) ops: &'static [NativeOp],
}

/// Pre-sorted native effect / op table. Tags and op ordering match the
/// canonical names produced by the typechecker and used by the translator's
/// `EffectOpRef`.
pub(super) const NATIVE_EFFECTS: &[NativeEffect] = &[
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
            // modify: handler-specific (procdict vs ETS)
            NativeOp {
                name: "modify",
                erl_module: "",
                erl_func: "get",
                param_count: 2,
                arg_transform: ArgTransform::Identity,
            },
            // new: handler-specific
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
