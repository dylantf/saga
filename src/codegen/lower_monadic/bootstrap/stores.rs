//! Bespoke native handler bodies for Ref and Vec bootstrap entries.

use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::native_effects::{ArgTransform, NativeOp};
use super::{native_op_closure, not_implemented_native_op};
use crate::codegen::lower_monadic::util::identity_k;

#[derive(Clone, Copy)]
pub(super) enum RefBackend {
    ProcessDictionary,
    Ets,
}

pub(super) fn vec_op_tuple() -> CExpr {
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
    native_op_closure(op.param_count, |_| build_vec_call(op))
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
        _ => not_implemented_native_op("Std.Vec.Vec", op.name),
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

pub(super) fn ref_op_tuple(backend: RefBackend) -> CExpr {
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
    native_op_closure(op.param_count, |evidence_var| {
        build_ref_call(op, evidence_var, backend)
    })
}

pub(super) fn build_ref_call(op: &NativeOp, evidence_var: &str, backend: RefBackend) -> CExpr {
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
            let id_k = identity_k(v_var);
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
        _ => not_implemented_native_op("Std.Ref.Ref", op.name),
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
            let id_k = identity_k(v_var);
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
        _ => not_implemented_native_op("Std.Ref.Ref", op.name),
    }
}
