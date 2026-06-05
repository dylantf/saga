use std::collections::HashMap;

use crate::ast::Pat;
use crate::codegen::monadic::ir::{Atom, MArm, MExpr, MHandler, MHandlerArm, MVar};

pub(super) fn rename_expr_vars(expr: &MExpr, renames: &HashMap<String, String>) -> MExpr {
    match expr {
        MExpr::Pure(atom) => MExpr::Pure(rename_atom_vars(atom, renames)),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op: op.clone(),
            args: rename_atoms(args, renames),
            source: *source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let body_renames = without_var(renames, var);
            MExpr::Bind {
                var: var.clone(),
                value: Box::new(rename_expr_vars(value, renames)),
                body: Box::new(rename_expr_vars(body, &body_renames)),
                mode: *mode,
            }
        }
        MExpr::Let { var, value, body } => {
            let body_renames = without_var(renames, var);
            MExpr::Let {
                var: var.clone(),
                value: Box::new(rename_expr_vars(value, renames)),
                body: Box::new(rename_expr_vars(body, &body_renames)),
            }
        }
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(rename_expr_vars(body, renames)),
            cleanup: Box::new(rename_expr_vars(cleanup, renames)),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => MExpr::Case {
            scrutinee: rename_atom_vars(scrutinee, renames),
            arms: arms
                .iter()
                .map(|arm| rename_arm_vars(arm, renames))
                .collect(),
            source: *source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => MExpr::If {
            cond: rename_atom_vars(cond, renames),
            then_branch: Box::new(rename_expr_vars(then_branch, renames)),
            else_branch: Box::new(rename_expr_vars(else_branch, renames)),
            source: *source,
        },
        MExpr::App { head, args, source } => MExpr::App {
            head: rename_atom_vars(head, renames),
            args: rename_atoms(args, renames),
            source: *source,
        },
        MExpr::With {
            handler,
            body,
            source,
        } => MExpr::With {
            handler: rename_handler_vars(handler, renames),
            body: Box::new(rename_expr_vars(body, renames)),
            source: *source,
        },
        MExpr::Resume { value, source } => MExpr::Resume {
            value: rename_atom_vars(value, renames),
            source: *source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => MExpr::FieldAccess {
            record: rename_atom_vars(record, renames),
            field: field.clone(),
            record_name: record_name.clone(),
            anon_fields: anon_fields.clone(),
            source: *source,
        },
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source,
        } => MExpr::RecordUpdate {
            record: rename_atom_vars(record, renames),
            fields: fields
                .iter()
                .map(|(field, value)| (field.clone(), rename_atom_vars(value, renames)))
                .collect(),
            record_name: record_name.clone(),
            anon_fields: anon_fields.clone(),
            source: *source,
        },
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => MExpr::DictMethodAccess {
            dict: rename_atom_vars(dict, renames),
            trait_name: trait_name.clone(),
            method_index: *method_index,
            source: *source,
        },
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => MExpr::ForeignCall {
            module: module.clone(),
            func: func.clone(),
            args: rename_atoms(args, renames),
            source: *source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => MExpr::BinOp {
            op: op.clone(),
            left: rename_atom_vars(left, renames),
            right: rename_atom_vars(right, renames),
            source: *source,
        },
        MExpr::UnaryMinus { value, source } => MExpr::UnaryMinus {
            value: rename_atom_vars(value, renames),
            source: *source,
        },
        MExpr::BitString { segments, source } => MExpr::BitString {
            segments: segments
                .iter()
                .map(|segment| {
                    let mut segment = segment.clone();
                    segment.value = rename_atom_vars(&segment.value, renames);
                    segment
                })
                .collect(),
            source: *source,
        },
        MExpr::Receive {
            arms,
            after,
            source,
        } => MExpr::Receive {
            arms: arms
                .iter()
                .map(|arm| rename_arm_vars(arm, renames))
                .collect(),
            after: after.as_ref().map(|(timeout, body)| {
                (
                    rename_atom_vars(timeout, renames),
                    Box::new(rename_expr_vars(body, renames)),
                )
            }),
            source: *source,
        },
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source,
        } => {
            let body_renames = without_pats(renames, params);
            let rest_renames = without_name(renames, name);
            MExpr::LetFun {
                name: name.clone(),
                params: params.clone(),
                body: Box::new(rename_expr_vars(body, &body_renames)),
                rest: Box::new(rename_expr_vars(rest, &rest_renames)),
                source: *source,
            }
        }
        MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source,
        } => MExpr::HandlerValue {
            effects: effects.clone(),
            arms: arms
                .iter()
                .map(|arm| rename_handler_arm_vars(arm, renames))
                .collect(),
            return_clause: return_clause
                .as_ref()
                .map(|arm| Box::new(rename_handler_arm_vars(arm, renames))),
            source: *source,
        },
    }
}

fn rename_atom_vars(atom: &Atom, renames: &HashMap<String, String>) -> Atom {
    match atom {
        Atom::Var { name, source } => {
            let mut name = name.clone();
            if let Some(replacement) = renames.get(&name.name) {
                name.name.clone_from(replacement);
            }
            Atom::Var {
                name,
                source: *source,
            }
        }
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => atom.clone(),
        Atom::Ctor { name, args, source } => Atom::Ctor {
            name: name.clone(),
            args: rename_atoms(args, renames),
            source: *source,
        },
        Atom::Tuple { elements, source } => Atom::Tuple {
            elements: rename_atoms(elements, renames),
            source: *source,
        },
        Atom::AnonRecord { fields, source } => Atom::AnonRecord {
            fields: rename_fields(fields, renames),
            source: *source,
        },
        Atom::Record {
            name,
            fields,
            source,
        } => Atom::Record {
            name: name.clone(),
            fields: rename_fields(fields, renames),
            source: *source,
        },
        Atom::Lambda {
            params,
            body,
            source,
        } => Atom::Lambda {
            params: params.clone(),
            body: Box::new(rename_expr_vars(body, &without_pats(renames, params))),
            source: *source,
        },
        Atom::BackendSpawnThunk { callback, source } => Atom::BackendSpawnThunk {
            callback: Box::new(rename_atom_vars(callback, renames)),
            source: *source,
        },
    }
}

fn rename_atoms(atoms: &[Atom], renames: &HashMap<String, String>) -> Vec<Atom> {
    atoms
        .iter()
        .map(|atom| rename_atom_vars(atom, renames))
        .collect()
}

fn rename_fields(
    fields: &[(String, Atom)],
    renames: &HashMap<String, String>,
) -> Vec<(String, Atom)> {
    fields
        .iter()
        .map(|(field, value)| (field.clone(), rename_atom_vars(value, renames)))
        .collect()
}

fn rename_arm_vars(arm: &MArm, renames: &HashMap<String, String>) -> MArm {
    let arm_renames = without_pat(renames, &arm.pattern);
    MArm {
        pattern: arm.pattern.clone(),
        guard: arm
            .guard
            .as_ref()
            .map(|guard| rename_expr_vars(guard, &arm_renames)),
        body: rename_expr_vars(&arm.body, &arm_renames),
        span: arm.span,
    }
}

fn rename_handler_vars(handler: &MHandler, renames: &HashMap<String, String>) -> MHandler {
    match handler {
        MHandler::Static {
            effects,
            arms,
            return_clause,
            source,
        } => MHandler::Static {
            effects: effects.clone(),
            arms: arms
                .iter()
                .map(|arm| rename_handler_arm_vars(arm, renames))
                .collect(),
            return_clause: return_clause
                .as_ref()
                .map(|arm| rename_handler_arm_vars(arm, renames)),
            source: *source,
        },
        MHandler::Native {
            effects,
            handler,
            source,
        } => MHandler::Native {
            effects: effects.clone(),
            handler: handler.clone(),
            source: *source,
        },
        MHandler::Composite { handlers, source } => MHandler::Composite {
            handlers: handlers
                .iter()
                .map(|handler| rename_handler_vars(handler, renames))
                .collect(),
            source: *source,
        },
        MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } => MHandler::Dynamic {
            effects: effects.clone(),
            op_tuple: rename_atom_vars(op_tuple, renames),
            return_lambda: return_lambda
                .as_ref()
                .map(|lambda| rename_atom_vars(lambda, renames)),
            source: *source,
        },
    }
}

fn rename_handler_arm_vars(arm: &MHandlerArm, renames: &HashMap<String, String>) -> MHandlerArm {
    let arm_renames = without_pats(renames, &arm.params);
    MHandlerArm {
        id: arm.id,
        op: arm.op.clone(),
        params: arm.params.clone(),
        body: Box::new(rename_expr_vars(&arm.body, &arm_renames)),
        finally_block: arm
            .finally_block
            .as_ref()
            .map(|body| Box::new(rename_expr_vars(body, &arm_renames))),
        span: arm.span,
    }
}

fn without_var(renames: &HashMap<String, String>, var: &MVar) -> HashMap<String, String> {
    without_name(renames, &var.name)
}

fn without_name(renames: &HashMap<String, String>, name: &str) -> HashMap<String, String> {
    let mut renames = renames.clone();
    renames.remove(name);
    renames
}

fn without_pat(renames: &HashMap<String, String>, pat: &Pat) -> HashMap<String, String> {
    let mut renames = renames.clone();
    remove_pat_bindings(&mut renames, pat);
    renames
}

fn without_pats(renames: &HashMap<String, String>, pats: &[Pat]) -> HashMap<String, String> {
    let mut renames = renames.clone();
    for pat in pats {
        remove_pat_bindings(&mut renames, pat);
    }
    renames
}

fn remove_pat_bindings(renames: &mut HashMap<String, String>, pat: &Pat) {
    match pat {
        Pat::Var { name, .. } => {
            renames.remove(name);
        }
        Pat::Constructor { args, .. } => {
            for arg in args {
                remove_pat_bindings(renames, arg);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            for (field, value) in fields {
                if let Some(value) = value {
                    remove_pat_bindings(renames, value);
                } else {
                    renames.remove(field);
                }
            }
            if let Some(as_name) = as_name {
                renames.remove(as_name);
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (field, value) in fields {
                if let Some(value) = value {
                    remove_pat_bindings(renames, value);
                } else {
                    renames.remove(field);
                }
            }
        }
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            for element in elements {
                remove_pat_bindings(renames, element);
            }
        }
        Pat::StringPrefix { rest, .. } => remove_pat_bindings(renames, rest),
        Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                remove_pat_bindings(renames, &segment.value);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            remove_pat_bindings(renames, head);
            remove_pat_bindings(renames, tail);
        }
        Pat::Or { patterns, .. } => {
            for pattern in patterns {
                remove_pat_bindings(renames, pattern);
            }
        }
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
    }
}
