use super::*;

pub(super) fn map_subst<T, U>(out: SubstOutcome<T>, f: impl FnOnce(T) -> U) -> SubstOutcome<U> {
    SubstOutcome {
        value: f(out.value),
        changed: out.changed,
        blocked: out.blocked,
    }
}

pub(super) fn combine_pair<A, B, U>(
    a: SubstOutcome<A>,
    b: SubstOutcome<B>,
    f: impl FnOnce(A, B) -> U,
) -> SubstOutcome<U> {
    SubstOutcome {
        value: f(a.value, b.value),
        changed: a.changed || b.changed,
        blocked: a.blocked || b.blocked,
    }
}

pub(super) fn combine_triple<A, B, C, U>(
    a: SubstOutcome<A>,
    b: SubstOutcome<B>,
    c: SubstOutcome<C>,
    f: impl FnOnce(A, B, C) -> U,
) -> SubstOutcome<U> {
    SubstOutcome {
        value: f(a.value, b.value, c.value),
        changed: a.changed || b.changed || c.changed,
        blocked: a.blocked || b.blocked || c.blocked,
    }
}

pub(super) fn subst_expr(
    expr: MExpr,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MExpr> {
    match expr {
        MExpr::Pure(atom) => {
            let out = subst_atom(atom, target, replacement, replacement_free_names);
            map_subst(out, MExpr::Pure)
        }
        MExpr::Yield { op, args, source } => {
            let out = subst_atoms(args, target, replacement, replacement_free_names);
            map_subst(out, |args| MExpr::Yield { op, args, source })
        }
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let value_out = subst_expr(*value, target, replacement, replacement_free_names);
            if var == *target || var.name == target.name {
                return SubstOutcome {
                    value: MExpr::Bind {
                        var,
                        value: Box::new(value_out.value),
                        body,
                        mode,
                    },
                    changed: value_out.changed,
                    blocked: value_out.blocked,
                };
            }
            if replacement_free_names.contains(&var.name) && expr_contains_target(&body, target) {
                return SubstOutcome::blocked(MExpr::Bind {
                    var,
                    value: Box::new(value_out.value),
                    body,
                    mode,
                });
            }
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            combine_pair(value_out, body_out, |value, body| MExpr::Bind {
                var,
                value: Box::new(value),
                body: Box::new(body),
                mode,
            })
        }
        MExpr::Let { var, value, body } => {
            let value_out = subst_expr(*value, target, replacement, replacement_free_names);
            if var == *target || var.name == target.name {
                return SubstOutcome {
                    value: MExpr::Let {
                        var,
                        value: Box::new(value_out.value),
                        body,
                    },
                    changed: value_out.changed,
                    blocked: value_out.blocked,
                };
            }
            if replacement_free_names.contains(&var.name) && expr_contains_target(&body, target) {
                return SubstOutcome::blocked(MExpr::Let {
                    var,
                    value: Box::new(value_out.value),
                    body,
                });
            }
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            combine_pair(value_out, body_out, |value, body| MExpr::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            })
        }
        MExpr::Ensure { body, cleanup } => {
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            let cleanup_out = subst_expr(*cleanup, target, replacement, replacement_free_names);
            combine_pair(body_out, cleanup_out, |body, cleanup| MExpr::Ensure {
                body: Box::new(body),
                cleanup: Box::new(cleanup),
            })
        }
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => {
            let scrutinee_out = subst_atom(scrutinee, target, replacement, replacement_free_names);
            let arms_out = subst_arms(arms, target, replacement, replacement_free_names);
            combine_pair(scrutinee_out, arms_out, |scrutinee, arms| MExpr::Case {
                scrutinee,
                arms,
                source,
            })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => {
            let cond_out = subst_atom(cond, target, replacement, replacement_free_names);
            let then_out = subst_expr(*then_branch, target, replacement, replacement_free_names);
            let else_out = subst_expr(*else_branch, target, replacement, replacement_free_names);
            combine_triple(
                cond_out,
                then_out,
                else_out,
                |cond, then_branch, else_branch| MExpr::If {
                    cond,
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                    source,
                },
            )
        }
        MExpr::App { head, args, source } => {
            let head_out = subst_atom(head, target, replacement, replacement_free_names);
            let args_out = subst_atoms(args, target, replacement, replacement_free_names);
            combine_pair(head_out, args_out, |head, args| MExpr::App {
                head,
                args,
                source,
            })
        }
        MExpr::With {
            handler,
            body,
            source,
        } => {
            let handler_out = subst_handler(handler, target, replacement, replacement_free_names);
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            combine_pair(handler_out, body_out, |handler, body| MExpr::With {
                handler,
                body: Box::new(body),
                source,
            })
        }
        MExpr::Resume { value, source } => {
            let out = subst_atom(value, target, replacement, replacement_free_names);
            map_subst(out, |value| MExpr::Resume { value, source })
        }
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => {
            let out = subst_atom(record, target, replacement, replacement_free_names);
            map_subst(out, |record| MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                source,
            })
        }
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source,
        } => {
            let record_out = subst_atom(record, target, replacement, replacement_free_names);
            let fields_out = subst_field_atoms(fields, target, replacement, replacement_free_names);
            combine_pair(record_out, fields_out, |record, fields| {
                MExpr::RecordUpdate {
                    record,
                    fields,
                    record_name,
                    anon_fields,
                    source,
                }
            })
        }
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => {
            let out = subst_atom(dict, target, replacement, replacement_free_names);
            map_subst(out, |dict| MExpr::DictMethodAccess {
                dict,
                trait_name,
                method_index,
                source,
            })
        }
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => {
            let out = subst_atoms(args, target, replacement, replacement_free_names);
            map_subst(out, |args| MExpr::ForeignCall {
                module,
                func,
                args,
                source,
            })
        }
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => {
            let left_out = subst_atom(left, target, replacement, replacement_free_names);
            let right_out = subst_atom(right, target, replacement, replacement_free_names);
            combine_pair(left_out, right_out, |left, right| MExpr::BinOp {
                op,
                left,
                right,
                source,
            })
        }
        MExpr::UnaryMinus { value, source } => {
            let out = subst_atom(value, target, replacement, replacement_free_names);
            map_subst(out, |value| MExpr::UnaryMinus { value, source })
        }
        MExpr::BitString { segments, source } => {
            let mut changed = false;
            let mut blocked = false;
            let segments = segments
                .into_iter()
                .map(|mut seg| {
                    let value_out =
                        subst_atom(seg.value, target, replacement, replacement_free_names);
                    changed |= value_out.changed;
                    blocked |= value_out.blocked;
                    seg.value = value_out.value;
                    if let Some(size) = seg.size {
                        let size_out =
                            subst_atom(size, target, replacement, replacement_free_names);
                        changed |= size_out.changed;
                        blocked |= size_out.blocked;
                        seg.size = Some(size_out.value);
                    }
                    seg
                })
                .collect();
            SubstOutcome {
                value: MExpr::BitString { segments, source },
                changed,
                blocked,
            }
        }
        MExpr::Receive {
            arms,
            after,
            source,
        } => {
            let arms_out = subst_arms(arms, target, replacement, replacement_free_names);
            let after_out = match after {
                Some((timeout, body)) => {
                    let timeout_out =
                        subst_atom(timeout, target, replacement, replacement_free_names);
                    let body_out = subst_expr(*body, target, replacement, replacement_free_names);
                    let combined = combine_pair(timeout_out, body_out, |timeout, body| {
                        (timeout, Box::new(body))
                    });
                    SubstOutcome {
                        value: Some(combined.value),
                        changed: combined.changed,
                        blocked: combined.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(arms_out, after_out, |arms, after| MExpr::Receive {
                arms,
                after,
                source,
            })
        }
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source,
        } => {
            let body_out = if pats_bind_name(&params, &target.name)
                || (pats_capture_replacement(&params, replacement_free_names)
                    && expr_contains_target(&body, target))
            {
                if pats_bind_name(&params, &target.name) {
                    SubstOutcome::unchanged(*body)
                } else {
                    SubstOutcome::blocked(*body)
                }
            } else {
                subst_expr(*body, target, replacement, replacement_free_names)
            };
            let rest_out = subst_expr(*rest, target, replacement, replacement_free_names);
            combine_pair(body_out, rest_out, |body, rest| MExpr::LetFun {
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
        } => {
            let arms_out = subst_handler_arms(arms, target, replacement, replacement_free_names);
            let return_out = match return_clause {
                Some(arm) => {
                    let out = subst_handler_arm(*arm, target, replacement, replacement_free_names);
                    SubstOutcome {
                        value: Some(Box::new(out.value)),
                        changed: out.changed,
                        blocked: out.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(arms_out, return_out, |arms, return_clause| {
                MExpr::HandlerValue {
                    effects,
                    arms,
                    return_clause,
                    source,
                }
            })
        }
    }
}

pub(super) fn subst_atom(
    atom: Atom,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Atom> {
    match atom {
        Atom::Var { name, .. } if var_matches(&name, target) => {
            SubstOutcome::changed(replacement.clone())
        }
        Atom::Ctor { name, args, source } => {
            let out = subst_atoms(args, target, replacement, replacement_free_names);
            map_subst(out, |args| Atom::Ctor { name, args, source })
        }
        Atom::Tuple { elements, source } => {
            let out = subst_atoms(elements, target, replacement, replacement_free_names);
            map_subst(out, |elements| Atom::Tuple { elements, source })
        }
        Atom::AnonRecord { fields, source } => {
            let out = subst_field_atoms(fields, target, replacement, replacement_free_names);
            map_subst(out, |fields| Atom::AnonRecord { fields, source })
        }
        Atom::Record {
            name,
            fields,
            source,
        } => {
            let out = subst_field_atoms(fields, target, replacement, replacement_free_names);
            map_subst(out, |fields| Atom::Record {
                name,
                fields,
                source,
            })
        }
        Atom::Lambda {
            params,
            body,
            source,
        } => {
            if pats_bind_name(&params, &target.name) {
                return SubstOutcome::unchanged(Atom::Lambda {
                    params,
                    body,
                    source,
                });
            }
            if pats_capture_replacement(&params, replacement_free_names)
                && expr_contains_target(&body, target)
            {
                return SubstOutcome::blocked(Atom::Lambda {
                    params,
                    body,
                    source,
                });
            }
            let out = subst_expr(*body, target, replacement, replacement_free_names);
            map_subst(out, |body| Atom::Lambda {
                params,
                body: Box::new(body),
                source,
            })
        }
        Atom::BackendSpawnThunk { callback, source } => {
            let out = subst_atom(*callback, target, replacement, replacement_free_names);
            map_subst(out, |callback| Atom::BackendSpawnThunk {
                callback: Box::new(callback),
                source,
            })
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => SubstOutcome::unchanged(atom),
    }
}

pub(super) fn subst_atoms(
    atoms: Vec<Atom>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<Atom>> {
    let mut changed = false;
    let mut blocked = false;
    let atoms = atoms
        .into_iter()
        .map(|atom| {
            let out = subst_atom(atom, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            out.value
        })
        .collect();
    SubstOutcome {
        value: atoms,
        changed,
        blocked,
    }
}

pub(super) fn subst_field_atoms(
    fields: Vec<(String, Atom)>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<(String, Atom)>> {
    let mut changed = false;
    let mut blocked = false;
    let fields = fields
        .into_iter()
        .map(|(name, atom)| {
            let out = subst_atom(atom, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            (name, out.value)
        })
        .collect();
    SubstOutcome {
        value: fields,
        changed,
        blocked,
    }
}

pub(super) fn subst_arms(
    arms: Vec<MArm>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<MArm>> {
    let mut changed = false;
    let mut blocked = false;
    let arms = arms
        .into_iter()
        .map(|arm| {
            let out = subst_arm(arm, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            out.value
        })
        .collect();
    SubstOutcome {
        value: arms,
        changed,
        blocked,
    }
}

pub(super) fn subst_arm(
    arm: MArm,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MArm> {
    if pat_has_nonbinding_ref(&arm.pattern, &target.name) {
        return SubstOutcome::blocked(arm);
    }
    if pat_binds_name(&arm.pattern, &target.name) {
        return SubstOutcome::unchanged(arm);
    }
    let target_in_arm = arm
        .guard
        .as_ref()
        .is_some_and(|g| expr_contains_target(g, target))
        || expr_contains_target(&arm.body, target);
    if pat_captures_replacement(&arm.pattern, replacement_free_names) && target_in_arm {
        return SubstOutcome::blocked(arm);
    }

    let guard_out = match arm.guard {
        Some(guard) => {
            let out = subst_expr(guard, target, replacement, replacement_free_names);
            SubstOutcome {
                value: Some(out.value),
                changed: out.changed,
                blocked: out.blocked,
            }
        }
        None => SubstOutcome::unchanged(None),
    };
    let body_out = subst_expr(arm.body, target, replacement, replacement_free_names);
    combine_pair(guard_out, body_out, |guard, body| MArm {
        guard,
        body,
        ..arm
    })
}

pub(super) fn subst_handler(
    handler: MHandler,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MHandler> {
    match handler {
        MHandler::Static {
            effects,
            arms,
            return_clause,
            source,
        } => {
            let arms_out = subst_handler_arms(arms, target, replacement, replacement_free_names);
            let return_out = match return_clause {
                Some(arm) => {
                    let out = subst_handler_arm(arm, target, replacement, replacement_free_names);
                    SubstOutcome {
                        value: Some(out.value),
                        changed: out.changed,
                        blocked: out.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(arms_out, return_out, |arms, return_clause| {
                MHandler::Static {
                    effects,
                    arms,
                    return_clause,
                    source,
                }
            })
        }
        MHandler::Native { .. } => SubstOutcome::unchanged(handler),
        MHandler::Composite { handlers, source } => {
            let mut changed = false;
            let mut blocked = false;
            let handlers = handlers
                .into_iter()
                .map(|handler| {
                    let out = subst_handler(handler, target, replacement, replacement_free_names);
                    changed |= out.changed;
                    blocked |= out.blocked;
                    out.value
                })
                .collect();
            SubstOutcome {
                value: MHandler::Composite { handlers, source },
                changed,
                blocked,
            }
        }
        MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } => {
            let op_out = subst_atom(op_tuple, target, replacement, replacement_free_names);
            let return_out = match return_lambda {
                Some(atom) => {
                    let out = subst_atom(atom, target, replacement, replacement_free_names);
                    SubstOutcome {
                        value: Some(out.value),
                        changed: out.changed,
                        blocked: out.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(op_out, return_out, |op_tuple, return_lambda| {
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                }
            })
        }
    }
}

pub(super) fn subst_handler_arms(
    arms: Vec<MHandlerArm>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<MHandlerArm>> {
    let mut changed = false;
    let mut blocked = false;
    let arms = arms
        .into_iter()
        .map(|arm| {
            let out = subst_handler_arm(arm, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            out.value
        })
        .collect();
    SubstOutcome {
        value: arms,
        changed,
        blocked,
    }
}

pub(super) fn subst_handler_arm(
    arm: MHandlerArm,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MHandlerArm> {
    if pats_bind_name(&arm.params, &target.name) {
        return SubstOutcome::unchanged(arm);
    }
    let target_in_arm = expr_contains_target(&arm.body, target)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|f| expr_contains_target(f, target));
    if pats_capture_replacement(&arm.params, replacement_free_names) && target_in_arm {
        return SubstOutcome::blocked(arm);
    }

    let body_out = subst_expr(*arm.body, target, replacement, replacement_free_names);
    let finally_out = match arm.finally_block {
        Some(finally_block) => {
            let out = subst_expr(*finally_block, target, replacement, replacement_free_names);
            SubstOutcome {
                value: Some(Box::new(out.value)),
                changed: out.changed,
                blocked: out.blocked,
            }
        }
        None => SubstOutcome::unchanged(None),
    };
    combine_pair(body_out, finally_out, |body, finally_block| MHandlerArm {
        body: Box::new(body),
        finally_block,
        ..arm
    })
}

pub(super) fn free_atom_names(atom: &Atom) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_atom_free_names(atom, &mut out, &HashSet::new());
    out
}

pub(super) fn collect_atom_free_names(
    atom: &Atom,
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    match atom {
        Atom::Var { name, .. } => {
            if !bound.contains(&name.name) {
                out.insert(name.name.clone());
            }
        }
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            for arg in args {
                collect_atom_free_names(arg, out, bound);
            }
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_free_names(atom, out, bound);
            }
        }
        Atom::Lambda { params, body, .. } => {
            let mut scoped = bound.clone();
            scoped.extend(bound_names_in_pats(params));
            collect_expr_free_names(body, out, &scoped);
        }
        Atom::BackendSpawnThunk { callback, .. } => {
            collect_atom_free_names(callback, out, bound);
        }
        Atom::QualifiedRef { name, .. } => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

pub(super) fn collect_atom_list_free_names(
    atoms: &[Atom],
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    for atom in atoms {
        collect_atom_free_names(atom, out, bound);
    }
}

pub(super) fn collect_expr_free_names(
    expr: &MExpr,
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    match expr {
        MExpr::Pure(atom) => collect_atom_free_names(atom, out, bound),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_free_names(args, out, bound);
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            collect_expr_free_names(value, out, bound);
            let mut scoped = bound.clone();
            scoped.insert(var.name.clone());
            collect_expr_free_names(body, out, &scoped);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_expr_free_names(body, out, bound);
            collect_expr_free_names(cleanup, out, bound);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_free_names(scrutinee, out, bound);
            for arm in arms {
                let mut scoped = bound.clone();
                scoped.extend(bound_names_in_pat(&arm.pattern));
                if let Some(guard) = &arm.guard {
                    collect_expr_free_names(guard, out, &scoped);
                }
                collect_expr_free_names(&arm.body, out, &scoped);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_free_names(cond, out, bound);
            collect_expr_free_names(then_branch, out, bound);
            collect_expr_free_names(else_branch, out, bound);
        }
        MExpr::App { head, args, .. } => {
            collect_atom_free_names(head, out, bound);
            collect_atom_list_free_names(args, out, bound);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_free_names(handler, out, bound);
            collect_expr_free_names(body, out, bound);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_free_names(value, out, bound),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_free_names(record, out, bound);
            for (_, atom) in fields {
                collect_atom_free_names(atom, out, bound);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_free_names(left, out, bound);
            collect_atom_free_names(right, out, bound);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_free_names(&seg.value, out, bound);
                if let Some(size) = &seg.size {
                    collect_atom_free_names(size, out, bound);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                let mut scoped = bound.clone();
                scoped.extend(bound_names_in_pat(&arm.pattern));
                if let Some(guard) = &arm.guard {
                    collect_expr_free_names(guard, out, &scoped);
                }
                collect_expr_free_names(&arm.body, out, &scoped);
            }
            if let Some((timeout, body)) = after {
                collect_atom_free_names(timeout, out, bound);
                collect_expr_free_names(body, out, bound);
            }
        }
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            ..
        } => {
            let mut body_scope = bound.clone();
            body_scope.insert(name.clone());
            body_scope.extend(bound_names_in_pats(params));
            collect_expr_free_names(body, out, &body_scope);

            let mut rest_scope = bound.clone();
            rest_scope.insert(name.clone());
            collect_expr_free_names(rest, out, &rest_scope);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_free_names(arm, out, bound);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_free_names(arm, out, bound);
            }
        }
    }
}

pub(super) fn collect_handler_free_names(
    handler: &MHandler,
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_free_names(arm, out, bound);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_free_names(arm, out, bound);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_free_names(handler, out, bound);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_free_names(op_tuple, out, bound);
            if let Some(atom) = return_lambda {
                collect_atom_free_names(atom, out, bound);
            }
        }
    }
}

pub(super) fn collect_handler_arm_free_names(
    arm: &MHandlerArm,
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    let mut scoped = bound.clone();
    scoped.extend(bound_names_in_pats(&arm.params));
    collect_expr_free_names(&arm.body, out, &scoped);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_free_names(finally_block, out, &scoped);
    }
}

pub(super) fn var_matches(actual: &MVar, target: &MVar) -> bool {
    actual == target || actual.name == target.name
}
