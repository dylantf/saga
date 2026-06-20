use super::*;

/// A resolution kind referenced by a plain `Var` (a function), as opposed to a
/// constructor or intrinsic. Only these are indexed by name for the cross-module
/// carry — they're the ones an inlined body refers to unqualifiedly.
pub(crate) fn is_fn_ref(kind: &ResolvedCodegenKind) -> bool {
    matches!(
        kind,
        ResolvedCodegenKind::BeamFunction { .. } | ResolvedCodegenKind::ExternalFunction { .. }
    )
}


/// Collect every module's parameterized `DictConstructor`s as external ctors,
/// borrowing each producer's resolution map for carrying. Used at consumer emit
/// time, where `ctx.modules` holds all other compiled modules.
pub fn external_ctors_from_modules(
    modules: &HashMap<String, crate::codegen::CompiledModule>,
) -> ExternalCtors<'_> {
    let mut map = ExternalCtors::new();
    for (source_module, compiled) in modules {
        for decl in &compiled.elaborated {
            if let Decl::DictConstructor {
                name,
                dict_params,
                methods,
                ..
            } = decl
            {
                map.insert(
                    name.clone(),
                    ExternalCtor {
                        source_module,
                        dict_params,
                        methods,
                        resolution: &compiled.resolution,
                        record_types: &compiled.front_resolution.record_types,
                        constructors: &compiled.front_resolution.constructors,
                    },
                );
            }
        }
    }
    map
}


/// Collect carryable plain functions ([`carryable_fun`]) from every compiled
/// module, borrowing each producer's resolution map. A bare name defined as a
/// carryable function more than once anywhere (a multi-clause function — separate
/// `FunBinding` decls — or two modules defining the same name) is **dropped**, so
/// the resulting bare-name keying is unambiguous. Used at consumer emit time.
pub fn external_funs_from_modules(
    modules: &HashMap<String, crate::codegen::CompiledModule>,
) -> ExternalFuns<'_> {
    let mut map = ExternalFuns::new();
    let mut dropped: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (source_module, compiled) in modules {
        for decl in &compiled.elaborated {
            let Some((name, params, body)) = carryable_fun(decl) else {
                continue;
            };
            if dropped.contains(name) {
                continue;
            }
            if map.contains_key(name) {
                // A second definition of this name — ambiguous; drop it entirely.
                map.remove(name);
                dropped.insert(name.to_string());
                continue;
            }
            map.insert(
                name.to_string(),
                ExternalFun {
                    source_module,
                    params,
                    body,
                    resolution: &compiled.resolution,
                    record_types: &compiled.front_resolution.record_types,
                    constructors: &compiled.front_resolution.constructors,
                },
            );
        }
    }
    map
}


/// If `decl` is a plain function eligible for "inline-to-cancel" carry, return its
/// `(name, params, body)`. Eligibility: a `FunBinding` with **no guard**, a body
/// that **dispatches on one of its own parameters** (`case Var(param) of …`, the
/// `apply_name_style`/`get_field` shape), **no self-reference** (so inlining can't
/// recurse — bounds depth without a stack guard), and a **bounded body size**.
/// Single-clause-ness is enforced by callers, which drop any name with more than
/// one carryable definition.
pub(crate) fn carryable_fun(decl: &Decl) -> Option<(&str, &[Pat], &Expr)> {
    let Decl::FunBinding {
        name,
        params,
        guard,
        body,
        ..
    } = decl
    else {
        return None;
    };
    if guard.is_some() {
        return None;
    }
    body_dispatch_param(params, body)?;
    if expr_node_count(body) > FUN_INLINE_SIZE_CAP {
        return None;
    }
    // Self-recursive bodies could inline without bound — exclude them.
    let bound: Vec<String> = Vec::new();
    let mut frees = std::collections::HashSet::new();
    collect_free_vars(body, &bound, &mut frees);
    if frees.contains(name) {
        return None;
    }
    Some((name, params, body))
}


/// The block tail (the value of a `Block` is its last `Stmt::Expr`) or `expr`
/// itself for a non-block — i.e. the expression in result position.
pub(crate) fn result_expr(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Block { stmts, .. } => match stmts.last().map(|s| &s.node) {
            Some(Stmt::Expr(e)) => e,
            _ => expr,
        },
        _ => expr,
    }
}


/// If `body`'s result expression is a `case` scrutinizing one of `params`
/// directly (`case Var(p) of …`), return that parameter's name.
pub(crate) fn body_dispatch_param<'a>(params: &'a [Pat], body: &Expr) -> Option<&'a str> {
    let ExprKind::Case { scrutinee, .. } = &result_expr(body).kind else {
        return None;
    };
    let ExprKind::Var { name } = &scrutinee.kind else {
        return None;
    };
    params.iter().find_map(|p| match p {
        Pat::Var { name: pn, .. } if pn == name => Some(pn.as_str()),
        _ => None,
    })
}


/// Number of expression nodes in `expr` (a cheap size bound for the carry filter).
pub(crate) fn expr_node_count(expr: &Expr) -> usize {
    let mut e = expr.clone();
    1 + child_exprs_mut(&mut e)
        .into_iter()
        .map(|c| expr_node_count(c))
        .sum::<usize>()
}

