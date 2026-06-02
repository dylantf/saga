use super::*;

pub(super) struct InlinedArm {
    pub(super) body: MExpr,
    pub(super) finally_block: Option<MExpr>,
}

pub(super) fn inline_tail_resumptive_arm(arm: &MHandlerArm, args: &[Atom]) -> Option<InlinedArm> {
    if args.len() != arm.params.len() {
        return None;
    }

    let mut body = (*arm.body).clone();
    let mut finally_block = arm.finally_block.as_deref().cloned();
    for (param, arg) in arm.params.iter().zip(args) {
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
                if let Some(cleanup) = finally_block {
                    let substituted = subst_expr(cleanup, &target, arg, &free_names);
                    if substituted.blocked {
                        return None;
                    }
                    finally_block = Some(substituted.value);
                }
            }
            Pat::Wildcard { .. }
            | Pat::Lit {
                value: crate::ast::Lit::Unit,
                ..
            } => {}
            _ => return None,
        }
    }
    Some(InlinedArm {
        body,
        finally_block,
    })
}

pub(super) fn rewrite_resumes_to_pure(expr: MExpr) -> MExpr {
    match expr {
        MExpr::Resume { value, .. } => MExpr::Pure(value),
        MExpr::Pure(atom) => MExpr::Pure(rewrite_resumes_in_atom(atom)),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op,
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => MExpr::Bind {
            var,
            value: Box::new(rewrite_resumes_to_pure(*value)),
            body: Box::new(rewrite_resumes_to_pure(*body)),
            mode,
        },
        MExpr::Let { var, value, body } => MExpr::Let {
            var,
            value: Box::new(rewrite_resumes_to_pure(*value)),
            body: Box::new(rewrite_resumes_to_pure(*body)),
        },
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(rewrite_resumes_to_pure(*body)),
            cleanup: Box::new(rewrite_resumes_to_pure(*cleanup)),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => MExpr::Case {
            scrutinee: rewrite_resumes_in_atom(scrutinee),
            arms: arms
                .into_iter()
                .map(|arm| MArm {
                    guard: arm.guard.map(rewrite_resumes_to_pure),
                    body: rewrite_resumes_to_pure(arm.body),
                    ..arm
                })
                .collect(),
            source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => MExpr::If {
            cond: rewrite_resumes_in_atom(cond),
            then_branch: Box::new(rewrite_resumes_to_pure(*then_branch)),
            else_branch: Box::new(rewrite_resumes_to_pure(*else_branch)),
            source,
        },
        MExpr::App { head, args, source } => MExpr::App {
            head: rewrite_resumes_in_atom(head),
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        MExpr::With {
            handler,
            body,
            source,
        } => MExpr::With {
            handler,
            body: Box::new(rewrite_resumes_to_pure(*body)),
            source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => MExpr::FieldAccess {
            record: rewrite_resumes_in_atom(record),
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
            record: rewrite_resumes_in_atom(record),
            fields: fields
                .into_iter()
                .map(|(name, atom)| (name, rewrite_resumes_in_atom(atom)))
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
            dict: rewrite_resumes_in_atom(dict),
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
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => MExpr::BinOp {
            op,
            left: rewrite_resumes_in_atom(left),
            right: rewrite_resumes_in_atom(right),
            source,
        },
        MExpr::UnaryMinus { value, source } => MExpr::UnaryMinus {
            value: rewrite_resumes_in_atom(value),
            source,
        },
        MExpr::BitString { segments, source } => MExpr::BitString {
            segments: segments
                .into_iter()
                .map(|mut seg| {
                    seg.value = rewrite_resumes_in_atom(seg.value);
                    seg.size = seg.size.map(rewrite_resumes_in_atom);
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
                .map(|arm| MArm {
                    guard: arm.guard.map(rewrite_resumes_to_pure),
                    body: rewrite_resumes_to_pure(arm.body),
                    ..arm
                })
                .collect(),
            after: after.map(|(timeout, body)| {
                (
                    rewrite_resumes_in_atom(timeout),
                    Box::new(rewrite_resumes_to_pure(*body)),
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
        } => MExpr::LetFun {
            name,
            params,
            // A nested local function has its own resume context; only the
            // surrounding continuation remains part of the inlined arm body.
            body,
            rest: Box::new(rewrite_resumes_to_pure(*rest)),
            source,
        },
        MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source,
        } => MExpr::HandlerValue {
            effects,
            // Handler-value arms introduce their own resume context.
            arms,
            return_clause,
            source,
        },
    }
}

pub(super) fn rewrite_resumes_in_atom(atom: Atom) -> Atom {
    match atom {
        Atom::Ctor { name, args, source } => Atom::Ctor {
            name,
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        Atom::Tuple { elements, source } => Atom::Tuple {
            elements: elements.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        Atom::AnonRecord { fields, source } => Atom::AnonRecord {
            fields: fields
                .into_iter()
                .map(|(name, atom)| (name, rewrite_resumes_in_atom(atom)))
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
                .map(|(name, atom)| (name, rewrite_resumes_in_atom(atom)))
                .collect(),
            source,
        },
        Atom::Lambda { .. } => atom,
        Atom::BackendSpawnThunk { .. } => atom,
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => atom,
    }
}
