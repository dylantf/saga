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
