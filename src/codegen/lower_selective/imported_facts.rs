use crate::ast::{Lit, NodeId, Pat};
use crate::codegen::monadic::ir::{
    Atom, MDecl, MDictConstructor, MExpr, MFunBinding, MHandler, MHandlerArm, MProgram,
};
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use crate::typechecker::ModuleCodegenInfo;
use std::collections::{HashMap, HashSet};

const FUNCTION_BODY_BUDGET: usize = 220;
const NATIVE_VARIANT_PREFIX: &str = "__saga_native_variant";
const STATIC_VARIANT_PREFIX: &str = "__saga_static_variant";

pub fn collect_imported_dict_constructors(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
    cloneable_private_helpers: &HashSet<String>,
) -> HashMap<String, MDictConstructor> {
    let debug_filter = std::env::var("SAGA_DEBUG_IMPORTED_DICTS").ok();
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::DictConstructor(dc) = decl else {
            continue;
        };
        if let Some(reason) = imported_dict_constructor_unsupported_reason(dc, resolution) {
            if debug_imported_dict_enabled(debug_filter.as_deref(), source_module, &dc.name) {
                eprintln!(
                    "xmod dict reject unsupported: {source_module}.{}: {reason}",
                    dc.name
                );
            }
            continue;
        }
        if dc.methods.iter().any(|method| {
            expr_has_private_same_module_refs_except_allowing_externals(
                method,
                source_module,
                &dc.name,
                &public_names,
                resolution,
                cloneable_private_helpers,
            )
        }) {
            if debug_imported_dict_enabled(debug_filter.as_deref(), source_module, &dc.name) {
                eprintln!(
                    "xmod dict reject private non-external refs: {source_module}.{}",
                    dc.name
                );
            }
            continue;
        }
        if debug_imported_dict_enabled(debug_filter.as_deref(), source_module, &dc.name) {
            eprintln!("xmod dict accept: {source_module}.{}", dc.name);
        }
        candidates.insert(dc.name.clone(), dc.clone());
    }

    candidates
}

pub fn collect_imported_private_helper_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, MFunBinding> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && !f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut raw_candidates: HashMap<String, MFunBinding> = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if f.public
            || public_names.contains(&f.name)
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || expr_node_count(&f.body) > FUNCTION_BODY_BUDGET
            || xmod_forbidden_shape_reason(&f.body, "body", Some(resolution)).is_some()
        {
            continue;
        }
        raw_candidates.insert(f.name.clone(), f.clone());
    }

    let mut cloneable = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for (name, f) in &raw_candidates {
            if cloneable.contains(name) {
                continue;
            }
            if expr_has_private_same_module_refs_except(
                &f.body,
                source_module,
                name,
                &public_names,
                resolution,
                &cloneable,
            ) {
                continue;
            }
            cloneable.insert(name.clone());
            changed = true;
        }
    }

    cloneable
        .into_iter()
        .filter_map(|name| {
            raw_candidates
                .get(&name)
                .cloned()
                .map(|binding| (format!("{source_module}.{name}"), binding))
        })
        .collect()
}

fn imported_dict_constructor_unsupported_reason(
    dc: &MDictConstructor,
    resolution: &ResolutionMap,
) -> Option<String> {
    for (index, method) in dc.methods.iter().enumerate() {
        let MExpr::Pure(Atom::Lambda { body, .. }) = method else {
            return Some(format!("method {index} is not a pure lambda"));
        };
        let node_count = expr_node_count(body);
        if node_count > FUNCTION_BODY_BUDGET {
            return Some(format!(
                "method {index} body has {node_count} nodes, budget is {FUNCTION_BODY_BUDGET}"
            ));
        }
        if let Some(reason) = xmod_forbidden_shape_reason(body, "body", Some(resolution)) {
            return Some(format!(
                "method {index} contains a forbidden xmod shape: {reason}"
            ));
        }
    }
    None
}

fn xmod_forbidden_shape_reason(
    expr: &MExpr,
    path: &str,
    resolution: Option<&ResolutionMap>,
) -> Option<String> {
    match expr {
        MExpr::LetFun { .. } => Some(format!("{path}: let-fun")),
        MExpr::HandlerValue { .. } => Some(format!("{path}: handler value")),
        MExpr::Pure(atom) => xmod_forbidden_atom_reason(atom, &format!("{path}.pure")),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => args
            .iter()
            .enumerate()
            .find_map(|(i, atom)| xmod_forbidden_atom_reason(atom, &format!("{path}.arg{i}"))),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            xmod_forbidden_shape_reason(value, &format!("{path}.value"), resolution)
                .or_else(|| xmod_forbidden_shape_reason(body, &format!("{path}.body"), resolution))
        }
        MExpr::Ensure { body, cleanup } => {
            xmod_forbidden_shape_reason(body, &format!("{path}.body"), resolution).or_else(|| {
                xmod_forbidden_shape_reason(cleanup, &format!("{path}.cleanup"), resolution)
            })
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => xmod_forbidden_atom_reason(scrutinee, &format!("{path}.scrutinee")).or_else(|| {
            arms.iter().enumerate().find_map(|(i, arm)| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| {
                        xmod_forbidden_shape_reason(
                            guard,
                            &format!("{path}.arm{i}.guard"),
                            resolution,
                        )
                    })
                    .or_else(|| {
                        xmod_forbidden_shape_reason(
                            &arm.body,
                            &format!("{path}.arm{i}.body"),
                            resolution,
                        )
                    })
            })
        }),
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => xmod_forbidden_atom_reason(cond, &format!("{path}.cond"))
            .or_else(|| {
                xmod_forbidden_shape_reason(then_branch, &format!("{path}.then"), resolution)
            })
            .or_else(|| {
                xmod_forbidden_shape_reason(else_branch, &format!("{path}.else"), resolution)
            }),
        MExpr::App { head, args, .. } => match head {
            Atom::Lambda { params, body, .. }
                if immediate_lambda_app_is_supported(params, body, args.len()) =>
            {
                args.iter()
                    .enumerate()
                    .find_map(|(i, atom)| {
                        xmod_forbidden_atom_reason(atom, &format!("{path}.arg{i}"))
                    })
                    .or_else(|| {
                        xmod_forbidden_shape_reason(
                            body,
                            &format!("{path}.lambda_body"),
                            resolution,
                        )
                    })
            }
            _ => xmod_forbidden_atom_reason(head, &format!("{path}.head")).or_else(|| {
                args.iter().enumerate().find_map(|(i, atom)| {
                    if app_head_allows_lambda_arg(head, resolution)
                        && matches!(atom, Atom::Lambda { .. })
                    {
                        None
                    } else {
                        xmod_forbidden_atom_reason(atom, &format!("{path}.arg{i}"))
                    }
                })
            }),
        },
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => xmod_forbidden_atom_reason(value, path),
        MExpr::RecordUpdate { record, fields, .. } => {
            xmod_forbidden_atom_reason(record, &format!("{path}.record")).or_else(|| {
                fields.iter().enumerate().find_map(|(i, (_, atom))| {
                    xmod_forbidden_atom_reason(atom, &format!("{path}.field{i}"))
                })
            })
        }
        MExpr::BinOp { left, right, .. } => {
            xmod_forbidden_atom_reason(left, &format!("{path}.left"))
                .or_else(|| xmod_forbidden_atom_reason(right, &format!("{path}.right")))
        }
        MExpr::BitString { segments, .. } => segments.iter().enumerate().find_map(|(i, seg)| {
            xmod_forbidden_atom_reason(&seg.value, &format!("{path}.segment{i}.value")).or_else(
                || {
                    seg.size.as_ref().and_then(|size| {
                        xmod_forbidden_atom_reason(size, &format!("{path}.segment{i}.size"))
                    })
                },
            )
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter()
                .enumerate()
                .find_map(|(i, arm)| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| {
                            xmod_forbidden_shape_reason(
                                guard,
                                &format!("{path}.arm{i}.guard"),
                                resolution,
                            )
                        })
                        .or_else(|| {
                            xmod_forbidden_shape_reason(
                                &arm.body,
                                &format!("{path}.arm{i}.body"),
                                resolution,
                            )
                        })
                })
                .or_else(|| {
                    after.as_ref().and_then(|(timeout, body)| {
                        xmod_forbidden_atom_reason(timeout, &format!("{path}.after.timeout"))
                            .or_else(|| {
                                xmod_forbidden_shape_reason(
                                    body,
                                    &format!("{path}.after.body"),
                                    resolution,
                                )
                            })
                    })
                })
        }
        MExpr::With { handler, body, .. } => {
            xmod_forbidden_handler_reason(handler, &format!("{path}.handler"), resolution)
                .or_else(|| xmod_forbidden_shape_reason(body, &format!("{path}.body"), resolution))
        }
    }
}

fn xmod_forbidden_handler_reason(
    handler: &MHandler,
    path: &str,
    resolution: Option<&ResolutionMap>,
) -> Option<String> {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => arms
            .iter()
            .enumerate()
            .find_map(|(i, arm)| {
                xmod_forbidden_handler_arm_reason(arm, &format!("{path}.arm{i}"), resolution)
            })
            .or_else(|| {
                return_clause.as_ref().and_then(|arm| {
                    xmod_forbidden_handler_arm_reason(arm, &format!("{path}.return"), resolution)
                })
            }),
        MHandler::Dynamic { .. } => Some(format!("{path}: dynamic handler")),
        MHandler::Native { .. } => Some(format!("{path}: native handler")),
        MHandler::Composite { .. } => Some(format!("{path}: composite handler")),
    }
}

fn xmod_forbidden_handler_arm_reason(
    arm: &MHandlerArm,
    path: &str,
    resolution: Option<&ResolutionMap>,
) -> Option<String> {
    if arm.finally_block.is_some() {
        return Some(format!("{path}: finally"));
    }
    xmod_forbidden_shape_reason(&arm.body, &format!("{path}.body"), resolution)
}

fn xmod_forbidden_atom_reason(atom: &Atom, path: &str) -> Option<String> {
    match atom {
        Atom::Lambda { .. } => Some(format!("{path}: lambda atom")),
        Atom::Ctor { args, .. } => args
            .iter()
            .enumerate()
            .find_map(|(i, arg)| xmod_forbidden_atom_reason(arg, &format!("{path}.ctor_arg{i}"))),
        Atom::Tuple { elements, .. } => elements
            .iter()
            .enumerate()
            .find_map(|(i, arg)| xmod_forbidden_atom_reason(arg, &format!("{path}.tuple_arg{i}"))),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().enumerate().find_map(|(i, (_, atom))| {
                xmod_forbidden_atom_reason(atom, &format!("{path}.field{i}"))
            })
        }
        Atom::BackendSpawnThunk { callback, .. } => {
            xmod_forbidden_atom_reason(callback, &format!("{path}.spawn_callback"))
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => None,
    }
}

fn app_head_allows_lambda_arg(head: &Atom, resolution: Option<&ResolutionMap>) -> bool {
    let Some(resolution) = resolution else {
        return false;
    };
    let source = match head {
        Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
        _ => return false,
    };
    resolution
        .get(&source)
        .is_some_and(|resolved| matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }))
}

fn immediate_lambda_app_is_supported(params: &[Pat], body: &MExpr, arg_len: usize) -> bool {
    arg_len == params.len() && params.iter().all(supported_inline_param) && expr_is_pure(body)
}

fn supported_inline_param(param: &Pat) -> bool {
    matches!(
        param,
        Pat::Var { .. }
            | Pat::Wildcard { .. }
            | Pat::Lit {
                value: Lit::Unit,
                ..
            }
    )
}

fn expr_is_pure(expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(_) => true,
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_is_pure(value) && expr_is_pure(body)
        }
        MExpr::Case { arms, .. } => arms
            .iter()
            .all(|arm| arm.guard.as_ref().is_none_or(expr_is_pure) && expr_is_pure(&arm.body)),
        MExpr::If {
            then_branch,
            else_branch,
            ..
        } => expr_is_pure(then_branch) && expr_is_pure(else_branch),
        MExpr::FieldAccess { .. }
        | MExpr::RecordUpdate { .. }
        | MExpr::DictMethodAccess { .. }
        | MExpr::BinOp { .. }
        | MExpr::UnaryMinus { .. }
        | MExpr::BitString { .. } => true,
        MExpr::App {
            head: Atom::DictRef { .. },
            ..
        } => true,
        MExpr::Yield { .. }
        | MExpr::App { .. }
        | MExpr::Ensure { .. }
        | MExpr::With { .. }
        | MExpr::Resume { .. }
        | MExpr::ForeignCall { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => false,
    }
}

fn expr_has_private_same_module_refs_except(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
    allowed_private_names: &HashSet<String>,
) -> bool {
    expr_has_private_same_module_refs_except_with_policy(
        expr,
        source_module,
        self_name,
        public_names,
        resolution,
        allowed_private_names,
        PrivateRefPolicy::RejectPrivateExternals,
    )
}

pub(super) fn expr_has_private_same_module_refs_except_allowing_externals(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
    allowed_private_names: &HashSet<String>,
) -> bool {
    expr_has_private_same_module_refs_except_with_policy(
        expr,
        source_module,
        self_name,
        public_names,
        resolution,
        allowed_private_names,
        PrivateRefPolicy::AllowPrivateExternals,
    )
}

#[derive(Clone, Copy)]
enum PrivateRefPolicy {
    RejectPrivateExternals,
    AllowPrivateExternals,
}

fn expr_has_private_same_module_refs_except_with_policy(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
    allowed_private_names: &HashSet<String>,
    policy: PrivateRefPolicy,
) -> bool {
    let mut refs = Vec::new();
    collect_app_head_refs(expr, &mut refs);
    refs.into_iter().any(|(name, source)| {
        let Some(resolved) = resolution.get(&source) else {
            return false;
        };
        if !matches!(
            resolved.kind,
            ResolvedCodegenKind::BeamFunction { .. }
                | ResolvedCodegenKind::ExternalFunction { .. }
                | ResolvedCodegenKind::Intrinsic { .. }
        ) {
            return false;
        }
        let same_module = resolved
            .source_module
            .as_deref()
            .is_none_or(|module| module == source_module);
        if same_module
            && matches!(policy, PrivateRefPolicy::AllowPrivateExternals)
            && matches!(resolved.kind, ResolvedCodegenKind::ExternalFunction { .. })
        {
            return false;
        }
        same_module
            && name != self_name
            && !public_names.contains(&name)
            && !allowed_private_names.contains(&name)
    })
}

fn collect_app_head_refs(expr: &MExpr, out: &mut Vec<(String, NodeId)>) {
    match expr {
        MExpr::App { head, args, .. } => {
            if let Atom::Var { name, source } = head {
                out.push((name.name.clone(), *source));
            }
            collect_atom_list_app_refs(args, out);
        }
        MExpr::Pure(atom) => collect_atom_app_refs(atom, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_app_refs(args, out)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_app_head_refs(value, out);
            collect_app_head_refs(body, out);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_app_head_refs(body, out);
            collect_app_head_refs(cleanup, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_app_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_app_head_refs(guard, out);
                }
                collect_app_head_refs(&arm.body, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_app_refs(cond, out);
            collect_app_head_refs(then_branch, out);
            collect_app_head_refs(else_branch, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_app_refs(handler, out);
            collect_app_head_refs(body, out);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_app_refs(value, out),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_app_refs(record, out);
            for (_, atom) in fields {
                collect_atom_app_refs(atom, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_app_refs(left, out);
            collect_atom_app_refs(right, out);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_app_refs(&seg.value, out);
                if let Some(size) = &seg.size {
                    collect_atom_app_refs(size, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_app_head_refs(guard, out);
                }
                collect_app_head_refs(&arm.body, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_app_refs(timeout, out);
                collect_app_head_refs(body, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_app_head_refs(body, out);
            collect_app_head_refs(rest, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_app_refs(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_app_refs(arm, out);
            }
        }
    }
}

fn collect_atom_app_refs(atom: &Atom, out: &mut Vec<(String, NodeId)>) {
    match atom {
        Atom::Lambda { body, .. } => collect_app_head_refs(body, out),
        Atom::Ctor { args, .. } => collect_atom_list_app_refs(args, out),
        Atom::Tuple { elements, .. } => collect_atom_list_app_refs(elements, out),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_app_refs(atom, out);
            }
        }
        Atom::BackendSpawnThunk { callback, .. } => collect_atom_app_refs(callback, out),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

fn collect_atom_list_app_refs(atoms: &[Atom], out: &mut Vec<(String, NodeId)>) {
    for atom in atoms {
        collect_atom_app_refs(atom, out);
    }
}

fn collect_handler_app_refs(handler: &MHandler, out: &mut Vec<(String, NodeId)>) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_app_refs(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_app_refs(arm, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_app_refs(handler, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_app_refs(op_tuple, out);
            if let Some(atom) = return_lambda {
                collect_atom_app_refs(atom, out);
            }
        }
    }
}

fn collect_handler_arm_app_refs(arm: &MHandlerArm, out: &mut Vec<(String, NodeId)>) {
    collect_app_head_refs(&arm.body, out);
    if let Some(cleanup) = &arm.finally_block {
        collect_app_head_refs(cleanup, out);
    }
}

pub(super) fn expr_node_count(expr: &MExpr) -> usize {
    match expr {
        MExpr::Pure(atom) => 1 + atom_node_count(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => 1 + atoms_node_count(args),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            1 + expr_node_count(value) + expr_node_count(body)
        }
        MExpr::Ensure { body, cleanup } => 1 + expr_node_count(body) + expr_node_count(cleanup),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            1 + atom_node_count(scrutinee)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            1 + atom_node_count(cond) + expr_node_count(then_branch) + expr_node_count(else_branch)
        }
        MExpr::App { head, args, .. } => 1 + atom_node_count(head) + atoms_node_count(args),
        MExpr::With { handler, body, .. } => {
            1 + handler_node_count(handler) + expr_node_count(body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => 1 + atom_node_count(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            1 + atom_node_count(record)
                + fields
                    .iter()
                    .map(|(_, atom)| atom_node_count(atom))
                    .sum::<usize>()
        }
        MExpr::BinOp { left, right, .. } => 1 + atom_node_count(left) + atom_node_count(right),
        MExpr::BitString { segments, .. } => {
            1 + segments
                .iter()
                .map(|seg| {
                    atom_node_count(&seg.value) + seg.size.as_ref().map_or(0, atom_node_count)
                })
                .sum::<usize>()
        }
        MExpr::Receive { arms, after, .. } => {
            1 + arms
                .iter()
                .map(|arm| {
                    arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                })
                .sum::<usize>()
                + after.as_ref().map_or(0, |(timeout, body)| {
                    atom_node_count(timeout) + expr_node_count(body)
                })
        }
        MExpr::LetFun { body, rest, .. } => 1 + expr_node_count(body) + expr_node_count(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            1 + arms.iter().map(handler_arm_node_count).sum::<usize>()
                + return_clause
                    .as_ref()
                    .map_or(0, |arm| handler_arm_node_count(arm))
        }
    }
}

fn atom_node_count(atom: &Atom) -> usize {
    match atom {
        Atom::Ctor { args, .. } => 1 + atoms_node_count(args),
        Atom::Tuple { elements, .. } => 1 + atoms_node_count(elements),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            1 + fields
                .iter()
                .map(|(_, atom)| atom_node_count(atom))
                .sum::<usize>()
        }
        Atom::Lambda { body, .. } => 1 + expr_node_count(body),
        Atom::BackendSpawnThunk { callback, .. } => 1 + atom_node_count(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => 1,
    }
}

fn atoms_node_count(atoms: &[Atom]) -> usize {
    atoms.iter().map(atom_node_count).sum()
}

fn handler_node_count(handler: &MHandler) -> usize {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            1 + arms.iter().map(handler_arm_node_count).sum::<usize>()
                + return_clause.as_ref().map_or(0, handler_arm_node_count)
        }
        MHandler::Native { .. } => 1,
        MHandler::Composite { handlers, .. } => {
            1 + handlers.iter().map(handler_node_count).sum::<usize>()
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => 1 + atom_node_count(op_tuple) + return_lambda.as_ref().map_or(0, atom_node_count),
    }
}

fn handler_arm_node_count(arm: &MHandlerArm) -> usize {
    expr_node_count(&arm.body)
        + arm
            .finally_block
            .as_ref()
            .map_or(0, |cleanup| expr_node_count(cleanup))
}

fn is_generated_variant_name(name: &str) -> bool {
    name.starts_with(NATIVE_VARIANT_PREFIX) || name.starts_with(STATIC_VARIANT_PREFIX)
}

fn debug_imported_dict_enabled(filter: Option<&str>, source_module: &str, name: &str) -> bool {
    if let Some(selective_filter) = std::env::var_os("SAGA_DEBUG_SELECTIVE") {
        let selective_filter = selective_filter.to_string_lossy();
        let target = format!("imported-dict:{source_module}.{name}");
        if selective_filter.is_empty()
            || target.contains(selective_filter.as_ref())
            || source_module.contains(selective_filter.as_ref())
            || name.contains(selective_filter.as_ref())
        {
            return true;
        }
    }
    let Some(filter) = filter else {
        return false;
    };
    filter.is_empty()
        || source_module.contains(filter)
        || name.contains(filter)
        || format!("{source_module}.{name}").contains(filter)
}
