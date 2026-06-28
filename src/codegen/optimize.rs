//! Post-classifier optimizer facts.
//!
//! This phase is deliberately metadata-first. It records facts that lowering
//! may consume for narrow fast paths, while default lowering remains correct
//! when no optimization fact is present.

use crate::ast::{self, Decl, Expr, ExprKind, Pat, Stmt};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct HelperFact {
    pub params: Vec<Pat>,
    pub body: Expr,
    pub source_module: String,
}

#[derive(Clone, Debug, Default)]
pub struct OptimizationFacts {
    pub handler_analysis: super::handler_analysis::HandlerAnalysis,
    /// Single-clause helper bodies. Importing modules filter these through
    /// `ModuleCodegenInfo.exports` before considering cross-module variants;
    /// the optimizer fact pass runs after elaboration/normalization, where
    /// source `pub` signatures are no longer the best publicness authority.
    pub public_helpers: HashMap<String, HelperFact>,
    /// Higher-order functions with a generated direct entry that may be used
    /// when callback arguments are externally direct.
    pub hof_direct_specializations: HashMap<String, HofDirectSpecialization>,
    /// Trait dictionary dispatch facts, keyed by `DictMethodAccess` App node.
    /// A `Dynamic` (or absent) entry keeps the normal `element/2` dispatch.
    pub dict_dispatch: super::trait_dispatch::DictDispatchMap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HofDirectSpecialization {
    pub entry_name: String,
    pub source_arity: usize,
    pub callback_params: Vec<HofCallbackParam>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HofCallbackParam {
    pub index: usize,
    pub source_arity: usize,
}

pub fn analyze(
    module_name: &str,
    program: &ast::Program,
    resolution: &super::resolve::ResolutionMap,
) -> OptimizationFacts {
    OptimizationFacts {
        handler_analysis: super::handler_analysis::analyze(program),
        public_helpers: collect_public_helper_facts(module_name, program),
        hof_direct_specializations: collect_hof_direct_specializations(module_name, program),
        dict_dispatch: super::trait_dispatch::analyze(module_name, program, resolution),
    }
}

fn source_module_name(module_name: &str, program: &ast::Program) -> String {
    program
        .iter()
        .find_map(|decl| match decl {
            Decl::ModuleDecl { path, .. } => Some(path.join(".")),
            _ => None,
        })
        .unwrap_or_else(|| module_name.to_string())
}

fn helper_params_supported(params: &[Pat]) -> bool {
    params.iter().all(|param| {
        matches!(
            param,
            Pat::Var { .. }
                | Pat::Wildcard { .. }
                | Pat::Lit {
                    value: ast::Lit::Unit,
                    ..
                }
        )
    })
}

fn collect_public_helper_facts(
    module_name: &str,
    program: &ast::Program,
) -> HashMap<String, HelperFact> {
    let source_module = source_module_name(module_name, program);
    let mut seen: HashSet<String> = HashSet::new();
    let mut duplicate_names: HashSet<String> = HashSet::new();
    let mut helpers = HashMap::new();

    for decl in program {
        let Decl::FunBinding {
            name,
            params,
            guard,
            body,
            ..
        } = decl
        else {
            continue;
        };
        if !seen.insert(name.clone()) {
            duplicate_names.insert(name.clone());
            helpers.remove(name);
            helpers.remove(&format!("{}.{}", source_module, name));
            continue;
        }
        if guard.is_some() || !helper_params_supported(params) {
            continue;
        }

        let fact = HelperFact {
            params: params.clone(),
            body: body.clone(),
            source_module: source_module.clone(),
        };
        helpers.insert(name.clone(), fact.clone());
        helpers.insert(format!("{}.{}", source_module, name), fact);
    }

    for name in duplicate_names {
        helpers.remove(&name);
        helpers.remove(&format!("{}.{}", source_module, name));
    }

    helpers
}

fn collect_hof_direct_specializations(
    module_name: &str,
    program: &ast::Program,
) -> HashMap<String, HofDirectSpecialization> {
    let source_module = source_module_name(module_name, program);
    let mut seen: HashSet<String> = HashSet::new();
    let mut duplicate_names: HashSet<String> = HashSet::new();
    let mut facts = HashMap::new();

    for decl in program {
        let Decl::FunBinding {
            name,
            params,
            guard,
            body,
            ..
        } = decl
        else {
            continue;
        };
        if !seen.insert(name.clone()) {
            duplicate_names.insert(name.clone());
            facts.remove(name);
            facts.remove(&format!("{}.{}", source_module, name));
            continue;
        }
        if guard.is_some() || !helper_params_supported(params) || !hof_body_supported(body) {
            continue;
        }
        let Some(callback_params) = hof_callback_params(params, body) else {
            continue;
        };
        let fact = HofDirectSpecialization {
            entry_name: format!("__saga_direct_hof_{}", name),
            source_arity: params.len(),
            callback_params,
        };
        facts.insert(name.clone(), fact.clone());
        facts.insert(format!("{}.{}", source_module, name), fact);
    }

    for name in duplicate_names {
        facts.remove(&name);
        facts.remove(&format!("{}.{}", source_module, name));
    }

    facts
}

fn hof_callback_params(params: &[Pat], body: &Expr) -> Option<Vec<HofCallbackParam>> {
    let param_names: HashMap<&str, usize> = params
        .iter()
        .enumerate()
        .filter_map(|(idx, param)| match param {
            Pat::Var { name, .. } => Some((name.as_str(), idx)),
            _ => None,
        })
        .collect();
    if param_names.is_empty() {
        return None;
    }

    let mut calls: HashMap<usize, usize> = HashMap::new();
    collect_hof_callback_calls(body, &param_names, &mut calls);
    if calls.is_empty() {
        return None;
    }

    let mut callback_params: Vec<HofCallbackParam> = calls
        .into_iter()
        .map(|(index, source_arity)| HofCallbackParam {
            index,
            source_arity,
        })
        .collect();
    callback_params.sort_by_key(|param| param.index);
    Some(callback_params)
}

fn collect_hof_callback_calls(
    expr: &Expr,
    param_names: &HashMap<&str, usize>,
    calls: &mut HashMap<usize, usize>,
) {
    if let Some((head, arity)) = app_head_and_arity(expr)
        && let ExprKind::Var { name, .. } = &head.kind
        && let Some(index) = param_names.get(name.as_str())
    {
        calls
            .entry(*index)
            .and_modify(|existing| {
                if *existing != arity {
                    *existing = usize::MAX;
                }
            })
            .or_insert(arity);
        collect_app_args(expr, &mut |arg| {
            collect_hof_callback_calls(arg, param_names, calls);
        });
        calls.retain(|_, arity| *arity != usize::MAX);
        return;
    }

    walk_expr(expr, &mut |child| {
        collect_hof_callback_calls(child, param_names, calls);
    });
    calls.retain(|_, arity| *arity != usize::MAX);
}

fn collect_app_args(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    let mut current = expr;
    let mut args = Vec::new();
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func;
    }
    for arg in args.into_iter().rev() {
        visit(arg);
    }
}

fn app_head_and_arity(expr: &Expr) -> Option<(&Expr, usize)> {
    let mut current = expr;
    let mut arity = 0;
    while let ExprKind::App { func, .. } = &current.kind {
        arity += 1;
        current = func;
    }
    (arity > 0).then_some((current, arity))
}

fn hof_body_supported(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::EffectCall { .. } | ExprKind::Resume { .. } => false,
        ExprKind::Lambda { .. } => false,
        _ => {
            let mut supported = true;
            walk_expr(expr, &mut |child| {
                supported &= hof_body_supported(child);
            });
            supported
        }
    }
}

/// Visit an expression's immediate sub-expressions. Shared with sibling
/// optimizer-fact passes (e.g. `trait_dispatch`) so AST traversal stays in one
/// place rather than drifting across copies.
pub(super) fn walk_expr(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    match &expr.kind {
        ExprKind::App { func, arg } => {
            visit(func);
            visit(arg);
        }
        ExprKind::BinOp { left, right, .. } => {
            visit(left);
            visit(right);
        }
        ExprKind::UnaryMinus { expr } | ExprKind::Ascription { expr, .. } => visit(expr),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            visit(cond);
            visit(then_branch);
            visit(else_branch);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            visit(scrutinee);
            for arm in arms {
                if let Some(guard) = &arm.node.guard {
                    visit(guard);
                }
                visit(&arm.node.body);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                match &stmt.node {
                    Stmt::Let { value, .. } => visit(value),
                    Stmt::LetFun { body, guard, .. } => {
                        if let Some(guard) = guard {
                            visit(guard);
                        }
                        visit(body);
                    }
                    Stmt::Expr(expr) => visit(expr),
                }
            }
        }
        ExprKind::With { expr, handler } => {
            visit(expr);
            for arm in handler.inline_arms() {
                visit(&arm.body);
                if let Some(finally_block) = &arm.finally_block {
                    visit(finally_block);
                }
            }
            if let Some(return_clause) = handler.return_clause() {
                visit(&return_clause.body);
            }
        }
        ExprKind::HandlerExpr { body } => {
            for arm in &body.arms {
                visit(&arm.node.body);
                if let Some(finally_block) = &arm.node.finally_block {
                    visit(finally_block);
                }
            }
            if let Some(return_clause) = &body.return_clause {
                visit(&return_clause.body);
            }
        }
        ExprKind::Tuple { elements, .. } | ExprKind::ListLit { elements } => {
            for element in elements {
                visit(element);
            }
        }
        ExprKind::RecordCreate { fields, .. }
        | ExprKind::ProjectionLiteral { fields, .. }
        | ExprKind::AnonRecordCreate { fields } => {
            for (_, _, field) in fields {
                visit(field);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            visit(record);
            for (_, _, field) in fields {
                visit(field);
            }
        }
        ExprKind::FieldAccess { expr, .. } => visit(expr),
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                visit(arg);
            }
        }
        ExprKind::Resume { value } => visit(value),
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, value) in bindings {
                visit(value);
            }
            visit(success);
            for arm in else_arms {
                if let Some(guard) = &arm.node.guard {
                    visit(guard);
                }
                visit(&arm.node.body);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                if let Some(guard) = &arm.node.guard {
                    visit(guard);
                }
                visit(&arm.node.body);
            }
            if let Some((timeout, body)) = after_clause {
                visit(timeout);
                visit(body);
            }
        }
        ExprKind::BitString { segments } => {
            for segment in segments {
                visit(&segment.value);
                if let Some(size) = &segment.size {
                    visit(size);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for segment in segments {
                visit(&segment.node);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for segment in segments {
                visit(&segment.node);
            }
        }
        ExprKind::Cons { head, tail } => {
            visit(head);
            visit(tail);
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(expr) = part {
                    visit(expr);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            visit(body);
            for qualifier in qualifiers {
                match qualifier {
                    ast::ComprehensionQualifier::Generator(_, expr)
                    | ast::ComprehensionQualifier::Let(_, expr)
                    | ast::ComprehensionQualifier::Guard(expr) => visit(expr),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                visit(arg);
            }
        }
        ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
            visit(dict)
        }
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}
        ExprKind::Lambda { body, .. } => visit(body),
    }
}
