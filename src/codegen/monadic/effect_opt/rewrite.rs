use super::*;

pub(super) fn rewrite_direct_calls_to_name(
    expr: MExpr,
    old_name: &str,
    new_name: &str,
    new_source: crate::ast::NodeId,
) -> MExpr {
    match expr {
        MExpr::App { head, args, source } => MExpr::App {
            head: rewrite_direct_call_atom_to_name(head, old_name, new_name, new_source),
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        MExpr::Pure(atom) => MExpr::Pure(rewrite_non_call_atom_refs(atom)),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op,
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let value = rewrite_direct_calls_to_name(*value, old_name, new_name, new_source);
            let body = if var.name == old_name {
                *body
            } else {
                rewrite_direct_calls_to_name(*body, old_name, new_name, new_source)
            };
            MExpr::Bind {
                var,
                value: Box::new(value),
                body: Box::new(body),
                mode,
            }
        }
        MExpr::Let { var, value, body } => {
            let value = rewrite_direct_calls_to_name(*value, old_name, new_name, new_source);
            let body = if var.name == old_name {
                *body
            } else {
                rewrite_direct_calls_to_name(*body, old_name, new_name, new_source)
            };
            MExpr::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            }
        }
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(rewrite_direct_calls_to_name(
                *body, old_name, new_name, new_source,
            )),
            cleanup: Box::new(rewrite_direct_calls_to_name(
                *cleanup, old_name, new_name, new_source,
            )),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => MExpr::Case {
            scrutinee: rewrite_non_call_atom_refs(scrutinee),
            arms: arms
                .into_iter()
                .map(|arm| rewrite_call_arm_refs(arm, old_name, new_name, new_source))
                .collect(),
            source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => MExpr::If {
            cond: rewrite_non_call_atom_refs(cond),
            then_branch: Box::new(rewrite_direct_calls_to_name(
                *then_branch,
                old_name,
                new_name,
                new_source,
            )),
            else_branch: Box::new(rewrite_direct_calls_to_name(
                *else_branch,
                old_name,
                new_name,
                new_source,
            )),
            source,
        },
        // A nested handler changes the evidence context. Keep recursive calls
        // inside it on the original slow path unless a later optimizer pass
        // deliberately specializes that inner context too.
        MExpr::With { .. } => expr,
        MExpr::Resume { value, source } => MExpr::Resume {
            value: rewrite_non_call_atom_refs(value),
            source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => MExpr::FieldAccess {
            record: rewrite_non_call_atom_refs(record),
            field,
            record_name,
            anon_fields,
            source,
        },
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source,
        } => MExpr::RecordUpdate {
            record: rewrite_non_call_atom_refs(record),
            fields: fields
                .into_iter()
                .map(|(field, atom)| (field, rewrite_non_call_atom_refs(atom)))
                .collect(),
            record_name,
            anon_fields,
            source,
        },
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => MExpr::DictMethodAccess {
            dict: rewrite_non_call_atom_refs(dict),
            trait_name,
            method_index,
            source,
        },
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => MExpr::ForeignCall {
            module,
            func,
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => MExpr::BinOp {
            op,
            left: rewrite_non_call_atom_refs(left),
            right: rewrite_non_call_atom_refs(right),
            source,
        },
        MExpr::UnaryMinus { value, source } => MExpr::UnaryMinus {
            value: rewrite_non_call_atom_refs(value),
            source,
        },
        MExpr::BitString { segments, source } => MExpr::BitString {
            segments: segments
                .into_iter()
                .map(|mut seg| {
                    seg.value = rewrite_non_call_atom_refs(seg.value);
                    seg.size = seg.size.map(rewrite_non_call_atom_refs);
                    seg
                })
                .collect(),
            source,
        },
        MExpr::Receive {
            arms,
            after,
            source,
        } => MExpr::Receive {
            arms: arms
                .into_iter()
                .map(|arm| rewrite_call_arm_refs(arm, old_name, new_name, new_source))
                .collect(),
            after: after.map(|(timeout, body)| {
                (
                    rewrite_non_call_atom_refs(timeout),
                    Box::new(rewrite_direct_calls_to_name(
                        *body, old_name, new_name, new_source,
                    )),
                )
            }),
            source,
        },
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source,
        } => {
            let body = if name == old_name || pats_bind_name(&params, old_name) {
                *body
            } else {
                rewrite_direct_calls_to_name(*body, old_name, new_name, new_source)
            };
            let rest = if name == old_name {
                *rest
            } else {
                rewrite_direct_calls_to_name(*rest, old_name, new_name, new_source)
            };
            MExpr::LetFun {
                name,
                params,
                body: Box::new(body),
                rest: Box::new(rest),
                source,
            }
        }
        MExpr::HandlerValue { .. } => expr,
    }
}

pub(super) fn append_args_to_direct_calls(
    expr: MExpr,
    target_name: &str,
    captures: &[String],
    source: crate::ast::NodeId,
) -> MExpr {
    let capture_args = || {
        captures
            .iter()
            .map(|capture| Atom::Var {
                name: MVar {
                    name: capture.clone(),
                    id: source.0,
                },
                source,
            })
            .collect::<Vec<_>>()
    };

    match expr {
        MExpr::App {
            head:
                Atom::Var {
                    name,
                    source: head_source,
                },
            mut args,
            source: app_source,
        } if name.name == target_name => {
            args.extend(capture_args());
            MExpr::App {
                head: Atom::Var {
                    name,
                    source: head_source,
                },
                args,
                source: app_source,
            }
        }
        MExpr::App { head, args, source } => MExpr::App {
            head: append_args_to_direct_call_atom(head, target_name, captures, source),
            args: args
                .into_iter()
                .map(|arg| append_args_to_direct_call_atom(arg, target_name, captures, source))
                .collect(),
            source,
        },
        MExpr::Pure(atom) => MExpr::Pure(append_args_to_direct_call_atom(
            atom,
            target_name,
            captures,
            source,
        )),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op,
            args: args
                .into_iter()
                .map(|arg| append_args_to_direct_call_atom(arg, target_name, captures, source))
                .collect(),
            source,
        },
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => MExpr::ForeignCall {
            module,
            func,
            args: args
                .into_iter()
                .map(|arg| append_args_to_direct_call_atom(arg, target_name, captures, source))
                .collect(),
            source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => MExpr::Bind {
            var,
            value: Box::new(append_args_to_direct_calls(
                *value,
                target_name,
                captures,
                source,
            )),
            body: Box::new(append_args_to_direct_calls(
                *body,
                target_name,
                captures,
                source,
            )),
            mode,
        },
        MExpr::Let { var, value, body } => MExpr::Let {
            var,
            value: Box::new(append_args_to_direct_calls(
                *value,
                target_name,
                captures,
                source,
            )),
            body: Box::new(append_args_to_direct_calls(
                *body,
                target_name,
                captures,
                source,
            )),
        },
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(append_args_to_direct_calls(
                *body,
                target_name,
                captures,
                source,
            )),
            cleanup: Box::new(append_args_to_direct_calls(
                *cleanup,
                target_name,
                captures,
                source,
            )),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source: case_source,
        } => MExpr::Case {
            scrutinee: append_args_to_direct_call_atom(scrutinee, target_name, captures, source),
            arms: arms
                .into_iter()
                .map(|arm| MArm {
                    guard: arm.guard.map(|guard| {
                        append_args_to_direct_calls(guard, target_name, captures, source)
                    }),
                    body: append_args_to_direct_calls(arm.body, target_name, captures, source),
                    ..arm
                })
                .collect(),
            source: case_source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source: if_source,
        } => MExpr::If {
            cond: append_args_to_direct_call_atom(cond, target_name, captures, source),
            then_branch: Box::new(append_args_to_direct_calls(
                *then_branch,
                target_name,
                captures,
                source,
            )),
            else_branch: Box::new(append_args_to_direct_calls(
                *else_branch,
                target_name,
                captures,
                source,
            )),
            source: if_source,
        },
        MExpr::With {
            handler,
            body,
            source: with_source,
        } => MExpr::With {
            handler: append_args_to_direct_call_handler(handler, target_name, captures, source),
            body: Box::new(append_args_to_direct_calls(
                *body,
                target_name,
                captures,
                source,
            )),
            source: with_source,
        },
        MExpr::Resume {
            value,
            source: resume_source,
        } => MExpr::Resume {
            value: append_args_to_direct_call_atom(value, target_name, captures, source),
            source: resume_source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source: field_source,
        } => MExpr::FieldAccess {
            record: append_args_to_direct_call_atom(record, target_name, captures, source),
            field,
            record_name,
            anon_fields,
            source: field_source,
        },
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source: update_source,
        } => MExpr::RecordUpdate {
            record: append_args_to_direct_call_atom(record, target_name, captures, source),
            fields: fields
                .into_iter()
                .map(|(field, atom)| {
                    (
                        field,
                        append_args_to_direct_call_atom(atom, target_name, captures, source),
                    )
                })
                .collect(),
            record_name,
            anon_fields,
            source: update_source,
        },
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source: access_source,
        } => MExpr::DictMethodAccess {
            dict: append_args_to_direct_call_atom(dict, target_name, captures, source),
            trait_name,
            method_index,
            source: access_source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source: bin_source,
        } => MExpr::BinOp {
            op,
            left: append_args_to_direct_call_atom(left, target_name, captures, source),
            right: append_args_to_direct_call_atom(right, target_name, captures, source),
            source: bin_source,
        },
        MExpr::UnaryMinus {
            value,
            source: unary_source,
        } => MExpr::UnaryMinus {
            value: append_args_to_direct_call_atom(value, target_name, captures, source),
            source: unary_source,
        },
        MExpr::BitString {
            segments,
            source: bit_source,
        } => MExpr::BitString {
            segments: segments
                .into_iter()
                .map(|mut seg| {
                    seg.value =
                        append_args_to_direct_call_atom(seg.value, target_name, captures, source);
                    seg.size = seg.size.map(|size| {
                        append_args_to_direct_call_atom(size, target_name, captures, source)
                    });
                    seg
                })
                .collect(),
            source: bit_source,
        },
        MExpr::Receive {
            arms,
            after,
            source: receive_source,
        } => MExpr::Receive {
            arms: arms
                .into_iter()
                .map(|arm| MArm {
                    guard: arm.guard.map(|guard| {
                        append_args_to_direct_calls(guard, target_name, captures, source)
                    }),
                    body: append_args_to_direct_calls(arm.body, target_name, captures, source),
                    ..arm
                })
                .collect(),
            after: after.map(|(timeout, body)| {
                (
                    append_args_to_direct_call_atom(timeout, target_name, captures, source),
                    Box::new(append_args_to_direct_calls(
                        *body,
                        target_name,
                        captures,
                        source,
                    )),
                )
            }),
            source: receive_source,
        },
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source: letfun_source,
        } => {
            let body = if name == target_name {
                *body
            } else {
                append_args_to_direct_calls(*body, target_name, captures, source)
            };
            let rest = if name == target_name {
                *rest
            } else {
                append_args_to_direct_calls(*rest, target_name, captures, source)
            };
            MExpr::LetFun {
                name,
                params,
                body: Box::new(body),
                rest: Box::new(rest),
                source: letfun_source,
            }
        }
        MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source: handler_source,
        } => MExpr::HandlerValue {
            effects,
            arms: arms
                .into_iter()
                .map(|arm| {
                    append_args_to_direct_call_handler_arm(arm, target_name, captures, source)
                })
                .collect(),
            return_clause: return_clause.map(|arm| {
                Box::new(append_args_to_direct_call_handler_arm(
                    *arm,
                    target_name,
                    captures,
                    source,
                ))
            }),
            source: handler_source,
        },
    }
}

#[allow(clippy::only_used_in_recursion)]
pub(super) fn append_args_to_direct_call_atom(
    atom: Atom,
    target_name: &str,
    captures: &[String],
    source: crate::ast::NodeId,
) -> Atom {
    match atom {
        Atom::Ctor {
            name,
            args,
            source: ctor_source,
        } => Atom::Ctor {
            name,
            args: args
                .into_iter()
                .map(|arg| append_args_to_direct_call_atom(arg, target_name, captures, source))
                .collect(),
            source: ctor_source,
        },
        Atom::Tuple {
            elements,
            source: tuple_source,
        } => Atom::Tuple {
            elements: elements
                .into_iter()
                .map(|arg| append_args_to_direct_call_atom(arg, target_name, captures, source))
                .collect(),
            source: tuple_source,
        },
        Atom::AnonRecord {
            fields,
            source: record_source,
        } => Atom::AnonRecord {
            fields: fields
                .into_iter()
                .map(|(field, atom)| {
                    (
                        field,
                        append_args_to_direct_call_atom(atom, target_name, captures, source),
                    )
                })
                .collect(),
            source: record_source,
        },
        Atom::Record {
            name,
            fields,
            source: record_source,
        } => Atom::Record {
            name,
            fields: fields
                .into_iter()
                .map(|(field, atom)| {
                    (
                        field,
                        append_args_to_direct_call_atom(atom, target_name, captures, source),
                    )
                })
                .collect(),
            source: record_source,
        },
        Atom::BackendSpawnThunk {
            callback,
            source: thunk_source,
        } => Atom::BackendSpawnThunk {
            callback: Box::new(append_args_to_direct_call_atom(
                *callback,
                target_name,
                captures,
                source,
            )),
            source: thunk_source,
        },
        Atom::Lambda { .. }
        | Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => atom,
    }
}

pub(super) fn append_args_to_direct_call_handler(
    handler: MHandler,
    target_name: &str,
    captures: &[String],
    source: crate::ast::NodeId,
) -> MHandler {
    match handler {
        MHandler::Static {
            effects,
            arms,
            return_clause,
            source: handler_source,
        } => MHandler::Static {
            effects,
            arms: arms
                .into_iter()
                .map(|arm| {
                    append_args_to_direct_call_handler_arm(arm, target_name, captures, source)
                })
                .collect(),
            return_clause: return_clause.map(|arm| {
                append_args_to_direct_call_handler_arm(arm, target_name, captures, source)
            }),
            source: handler_source,
        },
        MHandler::Composite {
            handlers,
            source: handler_source,
        } => MHandler::Composite {
            handlers: handlers
                .into_iter()
                .map(|handler| {
                    append_args_to_direct_call_handler(handler, target_name, captures, source)
                })
                .collect(),
            source: handler_source,
        },
        MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source: handler_source,
        } => MHandler::Dynamic {
            effects,
            op_tuple: append_args_to_direct_call_atom(op_tuple, target_name, captures, source),
            return_lambda: return_lambda
                .map(|atom| append_args_to_direct_call_atom(atom, target_name, captures, source)),
            source: handler_source,
        },
        MHandler::Native { .. } => handler,
    }
}

pub(super) fn append_args_to_direct_call_handler_arm(
    arm: MHandlerArm,
    target_name: &str,
    captures: &[String],
    source: crate::ast::NodeId,
) -> MHandlerArm {
    MHandlerArm {
        body: Box::new(append_args_to_direct_calls(
            *arm.body,
            target_name,
            captures,
            source,
        )),
        finally_block: arm.finally_block.map(|cleanup| {
            Box::new(append_args_to_direct_calls(
                *cleanup,
                target_name,
                captures,
                source,
            ))
        }),
        ..arm
    }
}

pub(super) fn rewrite_direct_call_atom_to_name(
    atom: Atom,
    old_name: &str,
    new_name: &str,
    new_source: crate::ast::NodeId,
) -> Atom {
    match atom {
        Atom::Var { mut name, .. } if name.name == old_name => {
            name.name = new_name.to_string();
            Atom::Var {
                name,
                source: new_source,
            }
        }
        other => rewrite_non_call_atom_refs(other),
    }
}

pub(super) fn rewrite_non_call_atom_refs(atom: Atom) -> Atom {
    match atom {
        Atom::Ctor { name, args, source } => Atom::Ctor {
            name,
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        Atom::Tuple { elements, source } => Atom::Tuple {
            elements: elements
                .into_iter()
                .map(rewrite_non_call_atom_refs)
                .collect(),
            source,
        },
        Atom::AnonRecord { fields, source } => Atom::AnonRecord {
            fields: fields
                .into_iter()
                .map(|(field, atom)| (field, rewrite_non_call_atom_refs(atom)))
                .collect(),
            source,
        },
        Atom::Record {
            name,
            fields,
            source,
        } => Atom::Record {
            name,
            fields: fields
                .into_iter()
                .map(|(field, atom)| (field, rewrite_non_call_atom_refs(atom)))
                .collect(),
            source,
        },
        Atom::BackendSpawnThunk { callback, source } => Atom::BackendSpawnThunk {
            callback: Box::new(rewrite_non_call_atom_refs(*callback)),
            source,
        },
        // Lambda bodies run in their own call context. Do not rewrite recursive
        // calls inside them as part of this generated function variant.
        Atom::Lambda { .. }
        | Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => atom,
    }
}

pub(super) fn rewrite_direct_callback_calls(
    expr: MExpr,
    target: &MVar,
    candidate: &InlineCandidate,
) -> Option<MExpr> {
    match expr {
        MExpr::App { head, args, source } => {
            if matches!(&head, Atom::Var { name, .. } if var_matches(name, target)) {
                return inline_helper_candidate(candidate, &args);
            }
            Some(MExpr::App {
                head: rewrite_callback_atom_refs(head, target, candidate)?,
                args: rewrite_callback_atoms(args, target, candidate)?,
                source,
            })
        }
        MExpr::Pure(atom) => Some(MExpr::Pure(rewrite_callback_atom_refs(
            atom, target, candidate,
        )?)),
        MExpr::Yield { op, args, source } => Some(MExpr::Yield {
            op,
            args: rewrite_callback_atoms(args, target, candidate)?,
            source,
        }),
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => Some(MExpr::ForeignCall {
            module,
            func,
            args: rewrite_callback_atoms(args, target, candidate)?,
            source,
        }),
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let value = rewrite_direct_callback_calls(*value, target, candidate)?;
            let body = if var_matches(&var, target) {
                *body
            } else {
                rewrite_direct_callback_calls(*body, target, candidate)?
            };
            Some(MExpr::Bind {
                var,
                value: Box::new(value),
                body: Box::new(body),
                mode,
            })
        }
        MExpr::Let { var, value, body } => {
            let value = rewrite_direct_callback_calls(*value, target, candidate)?;
            let body = if var_matches(&var, target) {
                *body
            } else {
                rewrite_direct_callback_calls(*body, target, candidate)?
            };
            Some(MExpr::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            })
        }
        MExpr::Ensure { body, cleanup } => Some(MExpr::Ensure {
            body: Box::new(rewrite_direct_callback_calls(*body, target, candidate)?),
            cleanup: Box::new(rewrite_direct_callback_calls(*cleanup, target, candidate)?),
        }),
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => Some(MExpr::Case {
            scrutinee: rewrite_callback_atom_refs(scrutinee, target, candidate)?,
            arms: arms
                .into_iter()
                .map(|arm| rewrite_callback_arm_refs(arm, target, candidate))
                .collect::<Option<Vec<_>>>()?,
            source,
        }),
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => Some(MExpr::If {
            cond: rewrite_callback_atom_refs(cond, target, candidate)?,
            then_branch: Box::new(rewrite_direct_callback_calls(
                *then_branch,
                target,
                candidate,
            )?),
            else_branch: Box::new(rewrite_direct_callback_calls(
                *else_branch,
                target,
                candidate,
            )?),
            source,
        }),
        MExpr::With {
            handler,
            body,
            source,
        } => Some(MExpr::With {
            handler: rewrite_callback_handler_refs(handler, target, candidate)?,
            body: Box::new(rewrite_direct_callback_calls(*body, target, candidate)?),
            source,
        }),
        MExpr::Resume { value, source } => Some(MExpr::Resume {
            value: rewrite_callback_atom_refs(value, target, candidate)?,
            source,
        }),
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => Some(MExpr::FieldAccess {
            record: rewrite_callback_atom_refs(record, target, candidate)?,
            field,
            record_name,
            anon_fields,
            source,
        }),
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source,
        } => Some(MExpr::RecordUpdate {
            record: rewrite_callback_atom_refs(record, target, candidate)?,
            fields: fields
                .into_iter()
                .map(|(field, atom)| {
                    Some((field, rewrite_callback_atom_refs(atom, target, candidate)?))
                })
                .collect::<Option<Vec<_>>>()?,
            record_name,
            anon_fields,
            source,
        }),
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => Some(MExpr::DictMethodAccess {
            dict: rewrite_callback_atom_refs(dict, target, candidate)?,
            trait_name,
            method_index,
            source,
        }),
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => Some(MExpr::BinOp {
            op,
            left: rewrite_callback_atom_refs(left, target, candidate)?,
            right: rewrite_callback_atom_refs(right, target, candidate)?,
            source,
        }),
        MExpr::UnaryMinus { value, source } => Some(MExpr::UnaryMinus {
            value: rewrite_callback_atom_refs(value, target, candidate)?,
            source,
        }),
        MExpr::BitString { segments, source } => Some(MExpr::BitString {
            segments: segments
                .into_iter()
                .map(|mut seg| {
                    seg.value = rewrite_callback_atom_refs(seg.value, target, candidate)?;
                    seg.size = match seg.size {
                        Some(size) => Some(rewrite_callback_atom_refs(size, target, candidate)?),
                        None => None,
                    };
                    Some(seg)
                })
                .collect::<Option<Vec<_>>>()?,
            source,
        }),
        MExpr::Receive {
            arms,
            after,
            source,
        } => Some(MExpr::Receive {
            arms: arms
                .into_iter()
                .map(|arm| rewrite_callback_arm_refs(arm, target, candidate))
                .collect::<Option<Vec<_>>>()?,
            after: match after {
                Some((timeout, body)) => Some((
                    rewrite_callback_atom_refs(timeout, target, candidate)?,
                    Box::new(rewrite_direct_callback_calls(*body, target, candidate)?),
                )),
                None => None,
            },
            source,
        }),
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source,
        } => {
            let body = if name == target.name || pats_bind_name(&params, &target.name) {
                *body
            } else {
                rewrite_direct_callback_calls(*body, target, candidate)?
            };
            let rest = if name == target.name {
                *rest
            } else {
                rewrite_direct_callback_calls(*rest, target, candidate)?
            };
            Some(MExpr::LetFun {
                name,
                params,
                body: Box::new(body),
                rest: Box::new(rest),
                source,
            })
        }
        MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source,
        } => Some(MExpr::HandlerValue {
            effects,
            arms: arms
                .into_iter()
                .map(|arm| rewrite_callback_handler_arm_refs(arm, target, candidate))
                .collect::<Option<Vec<_>>>()?,
            return_clause: match return_clause {
                Some(arm) => Some(Box::new(rewrite_callback_handler_arm_refs(
                    *arm, target, candidate,
                )?)),
                None => None,
            },
            source,
        }),
    }
}

pub(super) fn rewrite_callback_atoms(
    atoms: Vec<Atom>,
    target: &MVar,
    candidate: &InlineCandidate,
) -> Option<Vec<Atom>> {
    atoms
        .into_iter()
        .map(|atom| rewrite_callback_atom_refs(atom, target, candidate))
        .collect()
}

pub(super) fn rewrite_callback_atom_refs(
    atom: Atom,
    target: &MVar,
    candidate: &InlineCandidate,
) -> Option<Atom> {
    match atom {
        Atom::Ctor { name, args, source } => Some(Atom::Ctor {
            name,
            args: rewrite_callback_atoms(args, target, candidate)?,
            source,
        }),
        Atom::Tuple { elements, source } => Some(Atom::Tuple {
            elements: rewrite_callback_atoms(elements, target, candidate)?,
            source,
        }),
        Atom::AnonRecord { fields, source } => Some(Atom::AnonRecord {
            fields: fields
                .into_iter()
                .map(|(field, atom)| {
                    Some((field, rewrite_callback_atom_refs(atom, target, candidate)?))
                })
                .collect::<Option<Vec<_>>>()?,
            source,
        }),
        Atom::Record {
            name,
            fields,
            source,
        } => Some(Atom::Record {
            name,
            fields: fields
                .into_iter()
                .map(|(field, atom)| {
                    Some((field, rewrite_callback_atom_refs(atom, target, candidate)?))
                })
                .collect::<Option<Vec<_>>>()?,
            source,
        }),
        Atom::Lambda {
            params,
            body,
            source,
        } => {
            let body = if pats_bind_name(&params, &target.name) {
                *body
            } else {
                rewrite_direct_callback_calls(*body, target, candidate)?
            };
            Some(Atom::Lambda {
                params,
                body: Box::new(body),
                source,
            })
        }
        Atom::BackendSpawnThunk { callback, source } => Some(Atom::BackendSpawnThunk {
            callback: Box::new(rewrite_callback_atom_refs(*callback, target, candidate)?),
            source,
        }),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => Some(atom),
    }
}

pub(super) fn rewrite_callback_arm_refs(
    arm: MArm,
    target: &MVar,
    candidate: &InlineCandidate,
) -> Option<MArm> {
    if pat_binds_name(&arm.pattern, &target.name) {
        return Some(arm);
    }
    Some(MArm {
        guard: match arm.guard {
            Some(guard) => Some(rewrite_direct_callback_calls(guard, target, candidate)?),
            None => None,
        },
        body: rewrite_direct_callback_calls(arm.body, target, candidate)?,
        ..arm
    })
}

pub(super) fn rewrite_callback_handler_refs(
    handler: MHandler,
    target: &MVar,
    candidate: &InlineCandidate,
) -> Option<MHandler> {
    match handler {
        MHandler::Static {
            effects,
            arms,
            return_clause,
            source,
        } => Some(MHandler::Static {
            effects,
            arms: arms
                .into_iter()
                .map(|arm| rewrite_callback_handler_arm_refs(arm, target, candidate))
                .collect::<Option<Vec<_>>>()?,
            return_clause: match return_clause {
                Some(arm) => Some(rewrite_callback_handler_arm_refs(arm, target, candidate)?),
                None => None,
            },
            source,
        }),
        MHandler::Composite { handlers, source } => Some(MHandler::Composite {
            handlers: handlers
                .into_iter()
                .map(|handler| rewrite_callback_handler_refs(handler, target, candidate))
                .collect::<Option<Vec<_>>>()?,
            source,
        }),
        MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } => Some(MHandler::Dynamic {
            effects,
            op_tuple: rewrite_callback_atom_refs(op_tuple, target, candidate)?,
            return_lambda: match return_lambda {
                Some(atom) => Some(rewrite_callback_atom_refs(atom, target, candidate)?),
                None => None,
            },
            source,
        }),
        MHandler::Native { .. } => Some(handler),
    }
}

pub(super) fn rewrite_callback_handler_arm_refs(
    arm: MHandlerArm,
    target: &MVar,
    candidate: &InlineCandidate,
) -> Option<MHandlerArm> {
    if pats_bind_name(&arm.params, &target.name) {
        return Some(arm);
    }
    Some(MHandlerArm {
        body: Box::new(rewrite_direct_callback_calls(*arm.body, target, candidate)?),
        finally_block: match arm.finally_block {
            Some(cleanup) => Some(Box::new(rewrite_direct_callback_calls(
                *cleanup, target, candidate,
            )?)),
            None => None,
        },
        ..arm
    })
}

pub(super) fn rewrite_call_arm_refs(
    arm: MArm,
    old_name: &str,
    new_name: &str,
    new_source: crate::ast::NodeId,
) -> MArm {
    if pat_binds_name(&arm.pattern, old_name) {
        return arm;
    }
    MArm {
        guard: arm
            .guard
            .map(|guard| rewrite_direct_calls_to_name(guard, old_name, new_name, new_source)),
        body: rewrite_direct_calls_to_name(arm.body, old_name, new_name, new_source),
        ..arm
    }
}

pub(super) fn helper_params_are_supported(params: &[Pat]) -> bool {
    params.iter().all(supported_inline_param)
}

pub(super) fn dict_method_params_are_supported(params: &[Pat]) -> bool {
    params.iter().all(|param| {
        supported_inline_param(param)
            || matches!(param, Pat::Constructor { .. } | Pat::Tuple { .. })
    })
}

pub(super) fn immediate_lambda_app_is_supported(
    params: &[Pat],
    body: &MExpr,
    arg_len: usize,
) -> bool {
    arg_len == params.len() && helper_params_are_supported(params) && expr_is_pure(body)
}

pub(super) fn supported_inline_param(param: &Pat) -> bool {
    matches!(
        param,
        Pat::Var { .. }
            | Pat::Wildcard { .. }
            | Pat::Lit {
                value: crate::ast::Lit::Unit,
                ..
            }
    )
}

pub(super) fn inline_helper_candidate(candidate: &InlineCandidate, args: &[Atom]) -> Option<MExpr> {
    if args.len() != candidate.params.len() {
        return None;
    }

    let mut body = candidate.body.clone();
    for (param, arg) in candidate.params.iter().zip(args).rev() {
        match param {
            Pat::Var { name, id, .. } => {
                let target = MVar {
                    name: name.clone(),
                    id: id.0,
                };
                let free_names = free_atom_names(arg);
                let substituted = subst_expr(body, &target, arg, &free_names);
                if substituted.blocked {
                    return None;
                }
                body = substituted.value;
            }
            Pat::Wildcard { .. }
            | Pat::Lit {
                value: crate::ast::Lit::Unit,
                ..
            } => {}
            Pat::Constructor { .. } | Pat::Tuple { .. } => {
                body = MExpr::Case {
                    scrutinee: arg.clone(),
                    arms: vec![MArm {
                        pattern: param.clone(),
                        guard: None,
                        body,
                        span: param.span(),
                    }],
                    source: param.id(),
                };
            }
            _ => return None,
        }
    }
    Some(body)
}
