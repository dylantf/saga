use super::*;

pub(super) fn native_direct_call_expr(
    handler: &str,
    op: &crate::codegen::monadic::ir::EffectOpRef,
    args: &[Atom],
    source: crate::ast::NodeId,
) -> Option<MExpr> {
    let handler_name = handler.rsplit('.').next().unwrap_or(handler);
    if handler_name == "beam_ref" && op.effect == "Std.Ref.Ref" {
        return beam_ref_direct_call_expr(&op.op, args, source);
    }
    if handler_name == "ets_ref" && op.effect == "Std.Ref.Ref" {
        return ets_ref_direct_call_expr(&op.op, args, source);
    }

    if !native_handler_allows_first_order_direct_call(handler, &op.effect) {
        return None;
    }
    let spec = native_op(&op.effect, &op.op)?;
    if spec.erl_module.is_empty() || args.len() != spec.param_count {
        return None;
    }

    let args = match spec.arg_transform {
        NativeArgTransform::Identity => args.to_vec(),
        NativeArgTransform::NoArgs => Vec::new(),
        NativeArgTransform::PrependAtom(atom) => {
            let mut out = Vec::with_capacity(args.len() + 1);
            out.push(backend_atom_at(atom, source));
            out.extend(args.iter().cloned());
            out
        }
        NativeArgTransform::Reorder(indices) => {
            let mut out = Vec::with_capacity(indices.len());
            for &idx in indices {
                out.push(args.get(idx)?.clone());
            }
            out
        }
        NativeArgTransform::WrapThunk(idx) => {
            if op.effect != "Std.Actor.Process" || op.op != "spawn" {
                return None;
            }
            let callback = args.get(idx)?.clone();
            (0..spec.param_count)
                .map(|i| {
                    if i == idx {
                        Some(backend_spawn_thunk_at(callback.clone(), source))
                    } else {
                        args.get(i).cloned()
                    }
                })
                .collect::<Option<Vec<_>>>()?
        }
    };

    Some(MExpr::ForeignCall {
        module: spec.erl_module.to_string(),
        func: spec.erl_func.to_string(),
        args,
        source,
    })
}

pub(super) fn native_handler_allows_first_order_direct_call(handler: &str, effect: &str) -> bool {
    let handler = handler.rsplit('.').next().unwrap_or(handler);
    handler == "beam_actor" && effect.starts_with("Std.Actor.")
}

pub(super) fn beam_ref_direct_call_expr(
    op: &str,
    args: &[Atom],
    source: crate::ast::NodeId,
) -> Option<MExpr> {
    match op {
        "get" if args.len() == 1 => Some(MExpr::ForeignCall {
            module: "erlang".to_string(),
            func: "get".to_string(),
            args: args.to_vec(),
            source,
        }),
        "set" if args.len() == 2 => {
            let discard = generated_native_var("__native_ref_set", source, 0);
            Some(MExpr::Bind {
                var: discard,
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "put".to_string(),
                    args: args.to_vec(),
                    source,
                }),
                body: Box::new(MExpr::Pure(unit_atom_at(source))),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        "new" if args.len() == 1 => {
            let key = generated_native_var("__native_ref_key", source, 0);
            let discard = generated_native_var("__native_ref_put", source, 1);
            Some(MExpr::Bind {
                var: key.clone(),
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "make_ref".to_string(),
                    args: Vec::new(),
                    source,
                }),
                body: Box::new(MExpr::Bind {
                    var: discard,
                    value: Box::new(MExpr::ForeignCall {
                        module: "erlang".to_string(),
                        func: "put".to_string(),
                        args: vec![
                            Atom::Var {
                                name: key.clone(),
                                source,
                            },
                            args[0].clone(),
                        ],
                        source,
                    }),
                    body: Box::new(MExpr::Pure(Atom::Var { name: key, source })),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        _ => None,
    }
}

pub(super) fn ets_ref_direct_call_expr(
    op: &str,
    args: &[Atom],
    source: crate::ast::NodeId,
) -> Option<MExpr> {
    let expr = match op {
        "get" if args.len() == 1 => ets_ref_lookup_expr(args[0].clone(), source),
        "set" if args.len() == 2 => {
            let discard = generated_native_var("__native_ref_insert", source, 0);
            Some(MExpr::Bind {
                var: discard,
                value: Box::new(MExpr::ForeignCall {
                    module: "ets".to_string(),
                    func: "insert".to_string(),
                    args: vec![
                        ets_ref_table_atom(source),
                        Atom::Tuple {
                            elements: args.to_vec(),
                            source,
                        },
                    ],
                    source,
                }),
                body: Box::new(MExpr::Pure(unit_atom_at(source))),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        "new" if args.len() == 1 => {
            let key = generated_native_var("__native_ref_key", source, 0);
            let discard = generated_native_var("__native_ref_insert", source, 1);
            Some(MExpr::Bind {
                var: key.clone(),
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "make_ref".to_string(),
                    args: Vec::new(),
                    source,
                }),
                body: Box::new(MExpr::Bind {
                    var: discard,
                    value: Box::new(MExpr::ForeignCall {
                        module: "ets".to_string(),
                        func: "insert".to_string(),
                        args: vec![
                            ets_ref_table_atom(source),
                            Atom::Tuple {
                                elements: vec![
                                    Atom::Var {
                                        name: key.clone(),
                                        source,
                                    },
                                    args[0].clone(),
                                ],
                                source,
                            },
                        ],
                        source,
                    }),
                    body: Box::new(MExpr::Pure(Atom::Var { name: key, source })),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        "modify" if args.len() == 2 => {
            let old = generated_native_var("__native_ref_old", source, 0);
            let new_value = generated_native_var("__native_ref_new", source, 1);
            let discard = generated_native_var("__native_ref_insert", source, 2);
            let callback = args[1].clone();
            let lookup = ets_ref_lookup_expr(args[0].clone(), source)?;
            Some(MExpr::Bind {
                var: old.clone(),
                value: Box::new(lookup),
                body: Box::new(MExpr::Bind {
                    var: new_value.clone(),
                    value: Box::new(MExpr::App {
                        head: callback,
                        args: vec![Atom::Var { name: old, source }],
                        source,
                    }),
                    body: Box::new(MExpr::Bind {
                        var: discard,
                        value: Box::new(MExpr::ForeignCall {
                            module: "ets".to_string(),
                            func: "insert".to_string(),
                            args: vec![
                                ets_ref_table_atom(source),
                                Atom::Tuple {
                                    elements: vec![
                                        args[0].clone(),
                                        Atom::Var {
                                            name: new_value.clone(),
                                            source,
                                        },
                                    ],
                                    source,
                                },
                            ],
                            source,
                        }),
                        body: Box::new(MExpr::Pure(Atom::Var {
                            name: new_value,
                            source,
                        })),
                        mode: crate::codegen::monadic::ir::BindMode::Sequence,
                    }),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        _ => None,
    };
    expr.map(|expr| with_ets_ref_table_init(expr, source))
}

fn ets_ref_lookup_expr(key: Atom, source: crate::ast::NodeId) -> Option<MExpr> {
    let lookup = generated_native_var("__native_ref_lookup", source, 0);
    let value = generated_native_var("__native_ref_value", source, 1);
    Some(MExpr::Bind {
        var: lookup.clone(),
        value: Box::new(MExpr::ForeignCall {
            module: "ets".to_string(),
            func: "lookup".to_string(),
            args: vec![ets_ref_table_atom(source), key],
            source,
        }),
        body: Box::new(MExpr::Case {
            scrutinee: Atom::Var {
                name: lookup,
                source,
            },
            arms: vec![MArm {
                pattern: single_ets_lookup_result_pat(value.clone(), source),
                guard: None,
                body: MExpr::Pure(Atom::Var {
                    name: value,
                    source,
                }),
                span: zero_span(),
            }],
            source,
        }),
        mode: crate::codegen::monadic::ir::BindMode::Sequence,
    })
}

fn single_ets_lookup_result_pat(value: MVar, source: crate::ast::NodeId) -> Pat {
    let span = zero_span();
    Pat::Constructor {
        id: source,
        name: "Cons".to_string(),
        args: vec![
            Pat::Tuple {
                id: source,
                elements: vec![
                    Pat::Wildcard { id: source, span },
                    Pat::Var {
                        id: source,
                        name: value.name,
                        span,
                    },
                ],
                span,
            },
            Pat::Constructor {
                id: source,
                name: "Nil".to_string(),
                args: Vec::new(),
                span,
            },
        ],
        span,
    }
}

fn ets_ref_table_atom(source: crate::ast::NodeId) -> Atom {
    backend_atom_at("saga_ref_store", source)
}

fn with_ets_ref_table_init(body: MExpr, source: crate::ast::NodeId) -> MExpr {
    let whereis = generated_native_var("__native_ref_table", source, 0);
    let missing = generated_native_var("__native_ref_table_missing", source, 0);
    let init = generated_native_var("__native_ref_table_init", source, 0);
    MExpr::Bind {
        var: whereis.clone(),
        value: Box::new(MExpr::ForeignCall {
            module: "ets".to_string(),
            func: "whereis".to_string(),
            args: vec![ets_ref_table_atom(source)],
            source,
        }),
        body: Box::new(MExpr::Bind {
            var: missing.clone(),
            value: Box::new(MExpr::ForeignCall {
                module: "erlang".to_string(),
                func: "=:=".to_string(),
                args: vec![
                    Atom::Var {
                        name: whereis,
                        source,
                    },
                    backend_atom_at("undefined", source),
                ],
                source,
            }),
            body: Box::new(MExpr::Bind {
                var: init,
                value: Box::new(MExpr::If {
                    cond: Atom::Var {
                        name: missing,
                        source,
                    },
                    then_branch: Box::new(MExpr::ForeignCall {
                        module: "ets".to_string(),
                        func: "new".to_string(),
                        args: vec![ets_ref_table_atom(source), ets_ref_table_options(source)],
                        source,
                    }),
                    else_branch: Box::new(MExpr::Pure(unit_atom_at(source))),
                    source,
                }),
                body: Box::new(body),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            }),
            mode: crate::codegen::monadic::ir::BindMode::Sequence,
        }),
        mode: crate::codegen::monadic::ir::BindMode::Sequence,
    }
}

fn ets_ref_table_options(source: crate::ast::NodeId) -> Atom {
    list_atom(
        vec![
            backend_atom_at("set", source),
            backend_atom_at("public", source),
            backend_atom_at("named_table", source),
        ],
        source,
    )
}

fn list_atom(elements: Vec<Atom>, source: crate::ast::NodeId) -> Atom {
    elements.into_iter().rev().fold(
        Atom::Ctor {
            name: "Nil".to_string(),
            args: Vec::new(),
            source,
        },
        |tail, head| Atom::Ctor {
            name: "Cons".to_string(),
            args: vec![head, tail],
            source,
        },
    )
}

fn zero_span() -> crate::token::Span {
    crate::token::Span { start: 0, end: 0 }
}

pub(super) fn generated_native_var(prefix: &str, source: crate::ast::NodeId, salt: u32) -> MVar {
    MVar {
        name: format!("{prefix}_{}", source.0),
        id: source.0.saturating_add(salt),
    }
}

pub(super) fn unit_atom_at(source: crate::ast::NodeId) -> Atom {
    Atom::Lit {
        value: crate::ast::Lit::Unit,
        source,
    }
}

pub(super) fn backend_atom_at(atom: &str, source: crate::ast::NodeId) -> Atom {
    Atom::BackendAtom {
        atom: atom.to_string(),
        source,
    }
}

pub(super) fn backend_spawn_thunk_at(callback: Atom, source: crate::ast::NodeId) -> Atom {
    Atom::BackendSpawnThunk {
        callback: Box::new(callback),
        source,
    }
}
