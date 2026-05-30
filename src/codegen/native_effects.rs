//! Backend-neutral metadata for BEAM-native effect handlers.
//!
//! This table describes the pure shape of native operations. Lowering uses it
//! to build bootstrap evidence closures; optimization uses it to identify the
//! small subset of native yields that can be rewritten to direct `ForeignCall`s.

/// A single BEAM-native op entry: how source-side Saga args map to the
/// underlying Erlang/runtime call.
pub(crate) struct NativeOpSpec {
    /// Source op name (matches the Saga effect-decl op name).
    pub(crate) name: &'static str,
    /// Erlang module/function the native call lives in. Empty module means the
    /// op is handled by bespoke lowering or is not direct-call eligible.
    pub(crate) erl_module: &'static str,
    pub(crate) erl_func: &'static str,
    /// Number of saga-side args this op takes.
    pub(crate) param_count: usize,
    pub(crate) arg_transform: NativeArgTransform,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NativeArgTransform {
    Identity,
    NoArgs,
    PrependAtom(&'static str),
    Reorder(&'static [usize]),
    WrapThunk(usize),
}

/// A BEAM-native effect + its ops in canonical (alphabetical) order.
pub(crate) struct NativeEffectSpec {
    pub(crate) tag: &'static str,
    pub(crate) ops: &'static [NativeOpSpec],
}

/// Pre-sorted native effect / op table. Tags and op ordering match the
/// canonical names produced by the typechecker and used by `EffectOpRef`.
pub(crate) const NATIVE_EFFECTS: &[NativeEffectSpec] = &[
    NativeEffectSpec {
        tag: "Std.Actor.Actor",
        ops: &[NativeOpSpec {
            name: "self",
            erl_module: "erlang",
            erl_func: "self",
            param_count: 1,
            arg_transform: NativeArgTransform::NoArgs,
        }],
    },
    NativeEffectSpec {
        tag: "Std.Actor.Link",
        ops: &[
            NativeOpSpec {
                name: "link",
                erl_module: "erlang",
                erl_func: "link",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "unlink",
                erl_module: "erlang",
                erl_func: "unlink",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
        ],
    },
    NativeEffectSpec {
        tag: "Std.Actor.Monitor",
        ops: &[
            NativeOpSpec {
                name: "demonitor",
                erl_module: "erlang",
                erl_func: "demonitor",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "monitor",
                erl_module: "erlang",
                erl_func: "monitor",
                param_count: 1,
                arg_transform: NativeArgTransform::PrependAtom("process"),
            },
        ],
    },
    NativeEffectSpec {
        tag: "Std.Actor.Process",
        ops: &[
            NativeOpSpec {
                name: "exit",
                erl_module: "erlang",
                erl_func: "exit",
                param_count: 2,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "send",
                erl_module: "erlang",
                erl_func: "send",
                param_count: 2,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "spawn",
                erl_module: "erlang",
                erl_func: "spawn",
                param_count: 1,
                arg_transform: NativeArgTransform::WrapThunk(0),
            },
        ],
    },
    NativeEffectSpec {
        tag: "Std.Actor.Timer",
        ops: &[
            NativeOpSpec {
                name: "cancel_timer",
                erl_module: "erlang",
                erl_func: "cancel_timer",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "send_after",
                erl_module: "erlang",
                erl_func: "send_after",
                param_count: 3,
                arg_transform: NativeArgTransform::Reorder(&[1, 0, 2]),
            },
            NativeOpSpec {
                name: "sleep",
                erl_module: "timer",
                erl_func: "sleep",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
        ],
    },
    NativeEffectSpec {
        tag: "Std.Process.Signal",
        ops: &[NativeOpSpec {
            name: "await_signal",
            erl_module: "saga_runtime",
            erl_func: "await_signal",
            param_count: 1,
            arg_transform: NativeArgTransform::Identity,
        }],
    },
    NativeEffectSpec {
        tag: "Std.Ref.Ref",
        ops: &[
            NativeOpSpec {
                name: "get",
                erl_module: "erlang",
                erl_func: "get",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "modify",
                erl_module: "",
                erl_func: "get",
                param_count: 2,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "new",
                erl_module: "",
                erl_func: "make_ref",
                param_count: 1,
                arg_transform: NativeArgTransform::Identity,
            },
            NativeOpSpec {
                name: "set",
                erl_module: "erlang",
                erl_func: "put",
                param_count: 2,
                arg_transform: NativeArgTransform::Identity,
            },
        ],
    },
];

pub(crate) fn native_effect(tag: &str) -> Option<&'static NativeEffectSpec> {
    NATIVE_EFFECTS.iter().find(|effect| effect.tag == tag)
}

pub(crate) fn native_op(effect: &str, op: &str) -> Option<&'static NativeOpSpec> {
    native_effect(effect)?
        .ops
        .iter()
        .find(|entry| entry.name == op)
}
