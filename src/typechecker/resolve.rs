//! Name resolution pass: rewrites AST names to canonical (module-qualified) form.
//!
//! Runs after imports are processed (scope_map is complete), before the main
//! typechecking passes. Transforms:
//! - `QualifiedName { module: "List", name: "map" }` → `Var { name: "Std.List.map" }`
//! - `Constructor { name: "Just" }` → `Constructor { name: "Std.Maybe.Just" }` (if in scope_map)
//! - `Pat::Constructor { name: "Just" }` → `Pat::Constructor { name: "Std.Maybe.Just" }`

use crate::ast::*;

use super::ScopeMap;

/// Resolve names in a program using the scope_map built from imports.
/// Local definitions (type constructors, function names) shadow imports.
pub(crate) fn resolve_names(program: &mut [Decl], scope_map: &ScopeMap) {
    // Collect locally-defined constructor names so we don't resolve them to imports
    let mut local_ctors: std::collections::HashSet<String> = std::collections::HashSet::new();
    for decl in program.iter() {
        if let Decl::TypeDef { variants, .. } = decl {
            for variant in variants {
                local_ctors.insert(variant.node.name.clone());
            }
        }
    }

    let effective_scope = if local_ctors.is_empty() {
        scope_map.clone()
    } else {
        let mut scope = scope_map.clone();
        for name in &local_ctors {
            scope.constructors.remove(name);
            // Also remove from values since constructors appear there too
            scope.values.remove(name);
        }
        scope
    };

    for decl in program.iter_mut() {
        resolve_decl(decl, &effective_scope);
    }
}

fn resolve_decl(decl: &mut Decl, scope: &ScopeMap) {
    match decl {
        Decl::FunBinding {
            params, body, guard, ..
        } => {
            for p in params.iter_mut() {
                resolve_pat(p, scope);
            }
            resolve_expr(body, scope);
            if let Some(g) = guard {
                resolve_expr(g, scope);
            }
        }
        Decl::Val { value, .. } => {
            resolve_expr(value, scope);
        }
        Decl::ImplDef { methods, .. } => {
            for method in methods.iter_mut() {
                let m = &mut method.node;
                for p in m.params.iter_mut() {
                    resolve_pat(p, scope);
                }
                resolve_expr(&mut m.body, scope);
            }
        }
        Decl::HandlerDef {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms.iter_mut() {
                resolve_expr(&mut arm.node.body, scope);
            }
            if let Some(ret) = return_clause {
                resolve_expr(&mut ret.body, scope);
            }
        }
        _ => {}
    }
}

fn resolve_expr(expr: &mut Expr, scope: &ScopeMap) {
    match &mut expr.kind {
        // Resolve the canonical module path for qualified names.
        // `module` is preserved for codegen; `canonical_module` is used by the typechecker.
        ExprKind::QualifiedName { module, name, canonical_module } => {
            let key = format!("{}.{}", module, name);
            if let Some(canonical) = scope.resolve_value(&key)
                && let Some(dot_pos) = canonical.rfind('.')
            {
                *canonical_module = Some(canonical[..dot_pos].to_string());
            }
        }

        ExprKind::Constructor { name } => {
            if let Some(canonical) = scope.resolve_constructor(name) {
                *name = canonical.to_string();
            }
        }

        ExprKind::App { func, arg, .. } => {
            resolve_expr(func, scope);
            resolve_expr(arg, scope);
        }
        ExprKind::BinOp { left, right, .. } => {
            resolve_expr(left, scope);
            resolve_expr(right, scope);
        }
        ExprKind::UnaryMinus { expr, .. } => resolve_expr(expr, scope),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            resolve_expr(cond, scope);
            resolve_expr(then_branch, scope);
            resolve_expr(else_branch, scope);
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts.iter_mut() {
                resolve_stmt(&mut stmt.node, scope);
            }
        }
        ExprKind::Lambda { body, params, .. } => {
            for p in params.iter_mut() {
                resolve_pat(p, scope);
            }
            resolve_expr(body, scope);
        }
        ExprKind::Case { scrutinee, arms, .. } => {
            resolve_expr(scrutinee, scope);
            for arm in arms.iter_mut() {
                let arm = &mut arm.node;
                resolve_pat(&mut arm.pattern, scope);
                if let Some(g) = &mut arm.guard {
                    resolve_expr(g, scope);
                }
                resolve_expr(&mut arm.body, scope);
            }
        }
        ExprKind::Tuple { elements, .. } => {
            for e in elements.iter_mut() {
                resolve_expr(e, scope);
            }
        }
        ExprKind::RecordCreate { fields, .. } => {
            for f in fields.iter_mut() {
                resolve_expr(&mut f.2, scope);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            resolve_expr(record, scope);
            for f in fields.iter_mut() {
                resolve_expr(&mut f.2, scope);
            }
        }
        ExprKind::FieldAccess { expr, .. } => {
            resolve_expr(expr, scope);
        }
        ExprKind::With { expr, .. } => {
            resolve_expr(expr, scope);
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pat, val) in bindings.iter_mut() {
                resolve_pat(pat, scope);
                resolve_expr(val, scope);
            }
            resolve_expr(success, scope);
            for arm in else_arms.iter_mut() {
                let arm = &mut arm.node;
                resolve_pat(&mut arm.pattern, scope);
                if let Some(g) = &mut arm.guard {
                    resolve_expr(g, scope);
                }
                resolve_expr(&mut arm.body, scope);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms.iter_mut() {
                let arm = &mut arm.node;
                resolve_pat(&mut arm.pattern, scope);
                if let Some(g) = &mut arm.guard {
                    resolve_expr(g, scope);
                }
                resolve_expr(&mut arm.body, scope);
            }
            if let Some((timeout, body)) = after_clause {
                resolve_expr(timeout, scope);
                resolve_expr(body, scope);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for a in args.iter_mut() {
                resolve_expr(a, scope);
            }
        }
        ExprKind::Resume { value, .. } => {
            resolve_expr(value, scope);
        }
        _ => {}
    }
}

fn resolve_pat(pat: &mut Pat, scope: &ScopeMap) {
    match pat {
        Pat::Constructor { name, args, .. } => {
            if let Some(canonical) = scope.resolve_constructor(name) {
                *name = canonical.to_string();
            }
            for arg in args.iter_mut() {
                resolve_pat(arg, scope);
            }
        }
        Pat::Tuple { elements, .. } => {
            for p in elements.iter_mut() {
                resolve_pat(p, scope);
            }
        }
        _ => {}
    }
}

fn resolve_stmt(stmt: &mut Stmt, scope: &ScopeMap) {
    match stmt {
        Stmt::Expr(expr) => resolve_expr(expr, scope),
        Stmt::Let { value, pattern, .. } => {
            resolve_pat(pattern, scope);
            resolve_expr(value, scope);
        }
        Stmt::LetFun {
            params, body, guard, ..
        } => {
            for p in params.iter_mut() {
                resolve_pat(p, scope);
            }
            resolve_expr(body, scope);
            if let Some(g) = guard {
                resolve_expr(g, scope);
            }
        }
    }
}
