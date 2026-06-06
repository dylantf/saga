use std::collections::HashMap;

use crate::ast::Pat;
use crate::codegen::monadic::ir::{Atom, MArm, MExpr, MHandler, MHandlerArm, MVar};

pub(super) fn freshen_lambda_for_inline<F>(
    params: &[Pat],
    body: &MExpr,
    fresh: &mut F,
) -> (Vec<Pat>, MExpr)
where
    F: FnMut(&str) -> String,
{
    let mut renames = HashMap::new();
    let params = params
        .iter()
        .map(|param| freshen_pat_binders(param, &mut renames, fresh))
        .collect();
    let body = freshen_expr_binders(body, &renames, fresh);
    (params, body)
}

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

fn freshen_expr_binders<F>(
    expr: &MExpr,
    renames: &HashMap<String, String>,
    fresh: &mut F,
) -> MExpr
where
    F: FnMut(&str) -> String,
{
    match expr {
        MExpr::Pure(atom) => MExpr::Pure(freshen_atom_binders(atom, renames, fresh)),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op: op.clone(),
            args: args
                .iter()
                .map(|atom| freshen_atom_binders(atom, renames, fresh))
                .collect(),
            source: *source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let value = freshen_expr_binders(value, renames, fresh);
            let mut body_renames = renames.clone();
            let var = freshen_mvar(var, &mut body_renames, fresh);
            MExpr::Bind {
                var,
                value: Box::new(value),
                body: Box::new(freshen_expr_binders(body, &body_renames, fresh)),
                mode: *mode,
            }
        }
        MExpr::Let { var, value, body } => {
            let value = freshen_expr_binders(value, renames, fresh);
            let mut body_renames = renames.clone();
            let var = freshen_mvar(var, &mut body_renames, fresh);
            MExpr::Let {
                var,
                value: Box::new(value),
                body: Box::new(freshen_expr_binders(body, &body_renames, fresh)),
            }
        }
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(freshen_expr_binders(body, renames, fresh)),
            cleanup: Box::new(freshen_expr_binders(cleanup, renames, fresh)),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => MExpr::Case {
            scrutinee: freshen_atom_binders(scrutinee, renames, fresh),
            arms: arms
                .iter()
                .map(|arm| freshen_arm_binders(arm, renames, fresh))
                .collect(),
            source: *source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => MExpr::If {
            cond: freshen_atom_binders(cond, renames, fresh),
            then_branch: Box::new(freshen_expr_binders(then_branch, renames, fresh)),
            else_branch: Box::new(freshen_expr_binders(else_branch, renames, fresh)),
            source: *source,
        },
        MExpr::App { head, args, source } => MExpr::App {
            head: freshen_atom_binders(head, renames, fresh),
            args: args
                .iter()
                .map(|atom| freshen_atom_binders(atom, renames, fresh))
                .collect(),
            source: *source,
        },
        MExpr::With {
            handler,
            body,
            source,
        } => MExpr::With {
            handler: freshen_handler_binders(handler, renames, fresh),
            body: Box::new(freshen_expr_binders(body, renames, fresh)),
            source: *source,
        },
        MExpr::Resume { value, source } => MExpr::Resume {
            value: freshen_atom_binders(value, renames, fresh),
            source: *source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => MExpr::FieldAccess {
            record: freshen_atom_binders(record, renames, fresh),
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
            record: freshen_atom_binders(record, renames, fresh),
            fields: fields
                .iter()
                .map(|(field, value)| (field.clone(), freshen_atom_binders(value, renames, fresh)))
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
            dict: freshen_atom_binders(dict, renames, fresh),
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
            args: args
                .iter()
                .map(|atom| freshen_atom_binders(atom, renames, fresh))
                .collect(),
            source: *source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => MExpr::BinOp {
            op: op.clone(),
            left: freshen_atom_binders(left, renames, fresh),
            right: freshen_atom_binders(right, renames, fresh),
            source: *source,
        },
        MExpr::UnaryMinus { value, source } => MExpr::UnaryMinus {
            value: freshen_atom_binders(value, renames, fresh),
            source: *source,
        },
        MExpr::BitString { segments, source } => MExpr::BitString {
            segments: segments
                .iter()
                .map(|segment| {
                    let mut segment = segment.clone();
                    segment.value = freshen_atom_binders(&segment.value, renames, fresh);
                    segment.size = segment
                        .size
                        .as_ref()
                        .map(|size| freshen_atom_binders(size, renames, fresh));
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
                .map(|arm| freshen_arm_binders(arm, renames, fresh))
                .collect(),
            after: after.as_ref().map(|(timeout, body)| {
                (
                    freshen_atom_binders(timeout, renames, fresh),
                    Box::new(freshen_expr_binders(body, renames, fresh)),
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
            let fresh_name = fresh(name);
            let mut fn_renames = renames.clone();
            fn_renames.insert(name.clone(), fresh_name.clone());

            let mut body_renames = fn_renames.clone();
            let params = params
                .iter()
                .map(|param| freshen_pat_binders(param, &mut body_renames, fresh))
                .collect();

            MExpr::LetFun {
                name: fresh_name,
                params,
                body: Box::new(freshen_expr_binders(body, &body_renames, fresh)),
                rest: Box::new(freshen_expr_binders(rest, &fn_renames, fresh)),
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
                .map(|arm| freshen_handler_arm_binders(arm, renames, fresh))
                .collect(),
            return_clause: return_clause
                .as_ref()
                .map(|arm| Box::new(freshen_handler_arm_binders(arm, renames, fresh))),
            source: *source,
        },
    }
}

fn freshen_atom_binders<F>(
    atom: &Atom,
    renames: &HashMap<String, String>,
    fresh: &mut F,
) -> Atom
where
    F: FnMut(&str) -> String,
{
    match rename_atom_vars(atom, renames) {
        Atom::Ctor { name, args, source } => Atom::Ctor {
            name,
            args: args
                .iter()
                .map(|atom| freshen_atom_binders(atom, renames, fresh))
                .collect(),
            source,
        },
        Atom::Tuple { elements, source } => Atom::Tuple {
            elements: elements
                .iter()
                .map(|atom| freshen_atom_binders(atom, renames, fresh))
                .collect(),
            source,
        },
        Atom::AnonRecord { fields, source } => Atom::AnonRecord {
            fields: fields
                .iter()
                .map(|(field, value)| (field.clone(), freshen_atom_binders(value, renames, fresh)))
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
                .iter()
                .map(|(field, value)| (field.clone(), freshen_atom_binders(value, renames, fresh)))
                .collect(),
            source,
        },
        Atom::Lambda {
            params,
            body,
            source,
        } => {
            let mut body_renames = renames.clone();
            let params = params
                .iter()
                .map(|param| freshen_pat_binders(param, &mut body_renames, fresh))
                .collect();
            Atom::Lambda {
                params,
                body: Box::new(freshen_expr_binders(&body, &body_renames, fresh)),
                source,
            }
        }
        Atom::BackendSpawnThunk { callback, source } => Atom::BackendSpawnThunk {
            callback: Box::new(freshen_atom_binders(&callback, renames, fresh)),
            source,
        },
        atom => atom,
    }
}

fn freshen_arm_binders<F>(arm: &MArm, renames: &HashMap<String, String>, fresh: &mut F) -> MArm
where
    F: FnMut(&str) -> String,
{
    let mut arm_renames = renames.clone();
    let pattern = freshen_pat_binders(&arm.pattern, &mut arm_renames, fresh);
    MArm {
        pattern,
        guard: arm
            .guard
            .as_ref()
            .map(|guard| freshen_expr_binders(guard, &arm_renames, fresh)),
        body: freshen_expr_binders(&arm.body, &arm_renames, fresh),
        span: arm.span,
    }
}

fn freshen_handler_binders<F>(
    handler: &MHandler,
    renames: &HashMap<String, String>,
    fresh: &mut F,
) -> MHandler
where
    F: FnMut(&str) -> String,
{
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
                .map(|arm| freshen_handler_arm_binders(arm, renames, fresh))
                .collect(),
            return_clause: return_clause
                .as_ref()
                .map(|arm| freshen_handler_arm_binders(arm, renames, fresh)),
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
                .map(|handler| freshen_handler_binders(handler, renames, fresh))
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
            op_tuple: freshen_atom_binders(op_tuple, renames, fresh),
            return_lambda: return_lambda
                .as_ref()
                .map(|lambda| freshen_atom_binders(lambda, renames, fresh)),
            source: *source,
        },
    }
}

fn freshen_handler_arm_binders<F>(
    arm: &MHandlerArm,
    renames: &HashMap<String, String>,
    fresh: &mut F,
) -> MHandlerArm
where
    F: FnMut(&str) -> String,
{
    let mut arm_renames = renames.clone();
    let params = arm
        .params
        .iter()
        .map(|param| freshen_pat_binders(param, &mut arm_renames, fresh))
        .collect();
    MHandlerArm {
        id: arm.id,
        op: arm.op.clone(),
        params,
        body: Box::new(freshen_expr_binders(&arm.body, &arm_renames, fresh)),
        finally_block: arm
            .finally_block
            .as_ref()
            .map(|body| Box::new(freshen_expr_binders(body, &arm_renames, fresh))),
        span: arm.span,
    }
}

fn freshen_mvar<F>(var: &MVar, renames: &mut HashMap<String, String>, fresh: &mut F) -> MVar
where
    F: FnMut(&str) -> String,
{
    let mut var = var.clone();
    let fresh_name = fresh(&var.name);
    renames.insert(var.name.clone(), fresh_name.clone());
    var.name = fresh_name;
    var
}

fn freshen_pat_binders<F>(
    pat: &Pat,
    renames: &mut HashMap<String, String>,
    fresh: &mut F,
) -> Pat
where
    F: FnMut(&str) -> String,
{
    match pat {
        Pat::Var { id, name, span } => {
            let fresh_name = fresh(name);
            renames.insert(name.clone(), fresh_name.clone());
            Pat::Var {
                id: *id,
                name: fresh_name,
                span: *span,
            }
        }
        Pat::Constructor {
            id,
            name,
            args,
            span,
        } => Pat::Constructor {
            id: *id,
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| freshen_pat_binders(arg, renames, fresh))
                .collect(),
            span: *span,
        },
        Pat::Record {
            id,
            name,
            fields,
            rest,
            as_name,
            span,
        } => {
            let fields = fields
                .iter()
                .map(|(field, value)| {
                    let value = value
                        .as_ref()
                        .map(|value| freshen_pat_binders(value, renames, fresh));
                    if value.is_none() {
                        let fresh_name = fresh(field);
                        renames.insert(field.clone(), fresh_name.clone());
                        (field.clone(), Some(Pat::Var {
                            id: *id,
                            name: fresh_name,
                            span: *span,
                        }))
                    } else {
                        (field.clone(), value)
                    }
                })
                .collect();
            let as_name = as_name.as_ref().map(|name| {
                let fresh_name = fresh(name);
                renames.insert(name.clone(), fresh_name.clone());
                fresh_name
            });
            Pat::Record {
                id: *id,
                name: name.clone(),
                fields,
                rest: *rest,
                as_name,
                span: *span,
            }
        }
        Pat::AnonRecord {
            id,
            fields,
            rest,
            span,
        } => {
            let fields = fields
                .iter()
                .map(|(field, value)| {
                    let value = value
                        .as_ref()
                        .map(|value| freshen_pat_binders(value, renames, fresh));
                    if value.is_none() {
                        let fresh_name = fresh(field);
                        renames.insert(field.clone(), fresh_name.clone());
                        (field.clone(), Some(Pat::Var {
                            id: *id,
                            name: fresh_name,
                            span: *span,
                        }))
                    } else {
                        (field.clone(), value)
                    }
                })
                .collect();
            Pat::AnonRecord {
                id: *id,
                fields,
                rest: *rest,
                span: *span,
            }
        }
        Pat::Tuple { id, elements, span } => Pat::Tuple {
            id: *id,
            elements: elements
                .iter()
                .map(|element| freshen_pat_binders(element, renames, fresh))
                .collect(),
            span: *span,
        },
        Pat::StringPrefix {
            id,
            prefix,
            rest,
            span,
        } => Pat::StringPrefix {
            id: *id,
            prefix: prefix.clone(),
            rest: Box::new(freshen_pat_binders(rest, renames, fresh)),
            span: *span,
        },
        Pat::BitStringPat { id, segments, span } => Pat::BitStringPat {
            id: *id,
            segments: segments
                .iter()
                .map(|segment| {
                    let mut segment = segment.clone();
                    segment.value = freshen_pat_binders(&segment.value, renames, fresh);
                    segment
                })
                .collect(),
            span: *span,
        },
        Pat::ListPat { id, elements, span } => Pat::ListPat {
            id: *id,
            elements: elements
                .iter()
                .map(|element| freshen_pat_binders(element, renames, fresh))
                .collect(),
            span: *span,
        },
        Pat::ConsPat {
            id,
            head,
            tail,
            span,
        } => Pat::ConsPat {
            id: *id,
            head: Box::new(freshen_pat_binders(head, renames, fresh)),
            tail: Box::new(freshen_pat_binders(tail, renames, fresh)),
            span: *span,
        },
        Pat::Or { id, patterns, span } => Pat::Or {
            id: *id,
            patterns: patterns
                .iter()
                .map(|pattern| freshen_pat_binders(pattern, renames, fresh))
                .collect(),
            span: *span,
        },
        Pat::Wildcard { .. } | Pat::Lit { .. } => pat.clone(),
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
