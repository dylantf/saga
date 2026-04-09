//! Name resolution pass: rewrites AST names to canonical (module-qualified) form.
//!
//! Runs after imports are processed (scope_map is complete), before the main
//! typechecking passes. Transforms:
//! - `Var { name: "map" }` -> `Var { name: "Std.List.map" }` (if not locally bound)
//! - `QualifiedName { module: "List", name: "map" }` -> fills `canonical_module`
//! - `Constructor { name: "Just" }` -> `Constructor { name: "Std.Maybe.Just" }` (if in scope_map)
//! - `Pat::Constructor { name: "Just" }` -> `Pat::Constructor { name: "Std.Maybe.Just" }`
//!
//! The pass is scope-aware: local bindings (function params, let bindings,
//! lambda params, case pattern bindings) shadow imported names.

use std::collections::HashSet;

use crate::ast::*;

use super::ScopeMap;

/// Rewrite a handler name to its canonical form if it's not locally shadowed.
fn canonicalize_handler_name(name: &mut String, scope: &ScopeMap, locals: &HashSet<String>) {
    if !locals.contains(name.as_str())
        && let Some(canonical) = scope.resolve_handler(name)
    {
        *name = canonical.to_string();
    }
}

/// Rewrite an effect qualifier to its canonical form.
fn canonicalize_effect_qualifier(qualifier: &mut Option<String>, scope: &ScopeMap) {
    if let Some(q) = qualifier
        && let Some(canonical) = scope.resolve_effect(q)
    {
        *q = canonical.to_string();
    }
}

/// Rewrite type names in a TypeExpr to canonical form.
fn resolve_type_expr(texpr: &mut TypeExpr, scope: &ScopeMap) {
    match texpr {
        TypeExpr::Named { name, .. } => {
            if let Some(canonical) = scope.resolve_type(name) {
                *name = canonical.to_string();
            } else {
                // Builtin type canonicalization (Int -> Std.Int.Int, etc.)
                let canonical = super::canonicalize_type_name(name);
                if canonical != name {
                    *name = canonical.to_string();
                }
            }
        }
        TypeExpr::App { func, arg, .. } => {
            resolve_type_expr(func, scope);
            resolve_type_expr(arg, scope);
        }
        TypeExpr::Arrow {
            from, to, effects, ..
        } => {
            resolve_type_expr(from, scope);
            resolve_type_expr(to, scope);
            for eff in effects {
                if let Some(canonical) = scope.resolve_effect(&eff.name) {
                    eff.name = canonical.to_string();
                }
                for arg in &mut eff.type_args {
                    resolve_type_expr(arg, scope);
                }
            }
        }
        TypeExpr::Record { fields, .. } => {
            for (_, field_ty) in fields {
                resolve_type_expr(field_ty, scope);
            }
        }
        TypeExpr::Labeled { inner, .. } => {
            resolve_type_expr(inner, scope);
        }
        TypeExpr::Var { .. } => {}
    }
}

/// Collect all variable names bound by a pattern.
fn collect_pat_bindings(pat: &Pat, out: &mut HashSet<String>) {
    match pat {
        Pat::Var { name, .. } => {
            out.insert(name.clone());
        }
        Pat::Constructor { args, .. } => {
            for arg in args {
                collect_pat_bindings(arg, out);
            }
        }
        Pat::Tuple { elements, .. } => {
            for p in elements {
                collect_pat_bindings(p, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_bindings(head, out);
            collect_pat_bindings(tail, out);
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            for (field_name, alias) in fields {
                match alias {
                    Some(p) => collect_pat_bindings(p, out),
                    None => {
                        out.insert(field_name.clone());
                    }
                }
            }
            if let Some(name) = as_name {
                out.insert(name.clone());
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (field_name, alias) in fields {
                match alias {
                    Some(p) => collect_pat_bindings(p, out),
                    None => {
                        out.insert(field_name.clone());
                    }
                }
            }
        }
        Pat::StringPrefix { rest, .. } => {
            collect_pat_bindings(rest, out);
        }
        _ => {}
    }
}

/// Resolve names in a program using the scope_map built from imports.
/// Local definitions (type constructors, function names) shadow imports.
pub(crate) fn resolve_names(program: &mut [Decl], scope_map: &ScopeMap) {
    // Collect locally-defined constructor names so we don't resolve them to imports
    let mut local_ctors: HashSet<String> = HashSet::new();
    let mut local_funs: HashSet<String> = HashSet::new();
    for decl in program.iter() {
        match decl {
            Decl::TypeDef { variants, .. } => {
                for variant in variants {
                    local_ctors.insert(variant.node.name.clone());
                }
            }
            Decl::FunBinding { name, .. } | Decl::FunSignature { name, .. } => {
                local_funs.insert(name.clone());
            }
            Decl::Val { name, .. } => {
                local_funs.insert(name.clone());
            }
            Decl::TraitDef { methods, .. } => {
                for method in methods {
                    local_funs.insert(method.node.name.clone());
                }
            }
            _ => {}
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
        resolve_decl(decl, &effective_scope, &local_funs);
    }
}

fn resolve_decl(decl: &mut Decl, scope: &ScopeMap, local_funs: &HashSet<String>) {
    match decl {
        Decl::FunSignature {
            params,
            return_type,
            effects,
            ..
        } => {
            for (_, texpr) in params.iter_mut() {
                resolve_type_expr(texpr, scope);
            }
            resolve_type_expr(return_type, scope);
            for eff in effects.iter_mut() {
                if let Some(canonical) = scope.resolve_effect(&eff.name) {
                    eff.name = canonical.to_string();
                }
                for arg in &mut eff.type_args {
                    resolve_type_expr(arg, scope);
                }
            }
        }
        Decl::FunBinding {
            params,
            body,
            guard,
            ..
        } => {
            let mut locals = local_funs.clone();
            for p in params.iter_mut() {
                resolve_pat(p, scope);
                collect_pat_bindings(p, &mut locals);
            }
            resolve_expr(body, scope, &locals);
            if let Some(g) = guard {
                resolve_expr(g, scope, &locals);
            }
        }
        Decl::Val { value, .. } => {
            resolve_expr(value, scope, local_funs);
        }
        Decl::TypeDef { variants, .. } => {
            for variant in variants.iter_mut() {
                for (_, texpr) in &mut variant.node.fields {
                    resolve_type_expr(texpr, scope);
                }
            }
        }
        Decl::RecordDef { fields, .. } => {
            for field in fields.iter_mut() {
                resolve_type_expr(&mut field.node.1, scope);
            }
        }
        Decl::ImplDef {
            target_type,
            methods,
            ..
        } => {
            // Resolve the target type name (e.g. "Ordering" -> "Std.Base.Ordering")
            if let Some(canonical) = scope.resolve_type(target_type) {
                *target_type = canonical.to_string();
            } else {
                let canonical = super::canonicalize_type_name(target_type);
                if canonical != target_type {
                    *target_type = canonical.to_string();
                }
            }
            for method in methods.iter_mut() {
                let m = &mut method.node;
                let mut locals = local_funs.clone();
                for p in m.params.iter_mut() {
                    resolve_pat(p, scope);
                    collect_pat_bindings(p, &mut locals);
                }
                resolve_expr(&mut m.body, scope, &locals);
            }
        }
        Decl::TraitDef { methods, .. } => {
            for method in methods.iter_mut() {
                let m = &mut method.node;
                for (_, texpr) in &mut m.params {
                    resolve_type_expr(texpr, scope);
                }
                resolve_type_expr(&mut m.return_type, scope);
            }
        }
        Decl::EffectDef { operations, .. } => {
            for op in operations.iter_mut() {
                for (_, texpr) in &mut op.node.params {
                    resolve_type_expr(texpr, scope);
                }
                resolve_type_expr(&mut op.node.return_type, scope);
            }
        }
        Decl::HandlerDef { body, .. } => {
            resolve_handler_body(body, scope, local_funs);
        }
        _ => {}
    }
}

fn collect_pat_vars(pat: &Pat, vars: &mut HashSet<String>) {
    match pat {
        Pat::Var { name, .. } => {
            vars.insert(name.clone());
        }
        Pat::Tuple { elements, .. } => {
            for e in elements {
                collect_pat_vars(e, vars);
            }
        }
        Pat::Constructor { args, .. } => {
            for a in args {
                collect_pat_vars(a, vars);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            for (name, alias) in fields {
                if let Some(p) = alias {
                    collect_pat_vars(p, vars);
                } else {
                    vars.insert(name.clone());
                }
            }
            if let Some(n) = as_name {
                vars.insert(n.clone());
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (name, alias) in fields {
                if let Some(p) = alias {
                    collect_pat_vars(p, vars);
                } else {
                    vars.insert(name.clone());
                }
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_vars(head, vars);
            collect_pat_vars(tail, vars);
        }
        Pat::StringPrefix { rest, .. } => {
            collect_pat_vars(rest, vars);
        }
        _ => {}
    }
}

fn resolve_handler_body(body: &mut HandlerBody, scope: &ScopeMap, local_funs: &HashSet<String>) {
    for arm in body.arms.iter_mut() {
        canonicalize_effect_qualifier(&mut arm.node.qualifier, scope);
        let mut locals = local_funs.clone();
        for pat in &arm.node.params {
            collect_pat_vars(pat, &mut locals);
        }
        resolve_expr(&mut arm.node.body, scope, &locals);
    }
    if let Some(ret) = &mut body.return_clause {
        let mut locals = local_funs.clone();
        for pat in &ret.params {
            collect_pat_vars(pat, &mut locals);
        }
        resolve_expr(&mut ret.body, scope, &locals);
    }
}

fn resolve_expr(expr: &mut Expr, scope: &ScopeMap, locals: &HashSet<String>) {
    match &mut expr.kind {
        // Resolve the canonical module path for qualified names.
        // `module` is preserved for codegen; `canonical_module` is used by the typechecker.
        ExprKind::QualifiedName {
            module,
            name,
            canonical_module,
        } => {
            let key = format!("{}.{}", module, name);
            if let Some(canonical) = scope.resolve_value(&key)
                && let Some(dot_pos) = canonical.rfind('.')
            {
                *canonical_module = Some(canonical[..dot_pos].to_string());
            }
        }

        ExprKind::Var { name, .. } => {
            if !locals.contains(name.as_str())
                && let Some(canonical) = scope.resolve_value(name)
            {
                *name = canonical.to_string();
            }
        }

        ExprKind::Constructor { name } => {
            if let Some(canonical) = scope.resolve_constructor(name) {
                *name = canonical.to_string();
            }
        }

        ExprKind::App { func, arg, .. } => {
            resolve_expr(func, scope, locals);
            resolve_expr(arg, scope, locals);
        }
        ExprKind::BinOp { left, right, .. } => {
            resolve_expr(left, scope, locals);
            resolve_expr(right, scope, locals);
        }
        ExprKind::UnaryMinus { expr, .. } => resolve_expr(expr, scope, locals),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            resolve_expr(cond, scope, locals);
            resolve_expr(then_branch, scope, locals);
            resolve_expr(else_branch, scope, locals);
        }
        ExprKind::Block { stmts, .. } => {
            // Block statements accumulate bindings: let x = ... makes x
            // visible in subsequent statements.
            let mut block_locals = locals.clone();
            for stmt in stmts.iter_mut() {
                resolve_stmt(&mut stmt.node, scope, &mut block_locals);
            }
        }
        ExprKind::Lambda { body, params, .. } => {
            let mut inner = locals.clone();
            for p in params.iter_mut() {
                resolve_pat(p, scope);
                collect_pat_bindings(p, &mut inner);
            }
            resolve_expr(body, scope, &inner);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            resolve_expr(scrutinee, scope, locals);
            for arm in arms.iter_mut() {
                let arm = &mut arm.node;
                resolve_pat(&mut arm.pattern, scope);
                let mut arm_locals = locals.clone();
                collect_pat_bindings(&arm.pattern, &mut arm_locals);
                if let Some(g) = &mut arm.guard {
                    resolve_expr(g, scope, &arm_locals);
                }
                resolve_expr(&mut arm.body, scope, &arm_locals);
            }
        }
        ExprKind::Tuple { elements, .. } => {
            for e in elements.iter_mut() {
                resolve_expr(e, scope, locals);
            }
        }
        ExprKind::RecordCreate { name, fields, .. } => {
            if let Some(canonical) = scope.resolve_type(name) {
                *name = canonical.to_string();
            } else {
                let canonical = super::canonicalize_type_name(name);
                if canonical != name {
                    *name = canonical.to_string();
                }
            }
            for f in fields.iter_mut() {
                resolve_expr(&mut f.2, scope, locals);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            resolve_expr(record, scope, locals);
            for f in fields.iter_mut() {
                resolve_expr(&mut f.2, scope, locals);
            }
        }
        ExprKind::FieldAccess { expr, .. } => {
            resolve_expr(expr, scope, locals);
        }
        ExprKind::With { expr, handler } => {
            resolve_expr(expr, scope, locals);
            match handler.as_mut() {
                Handler::Named(name, _) => {
                    canonicalize_handler_name(name, scope, locals);
                }
                Handler::Inline { items, .. } => {
                    for ann in items.iter_mut() {
                        match &mut ann.node {
                            HandlerItem::Named(named_ref) => {
                                canonicalize_handler_name(&mut named_ref.name, scope, locals);
                            }
                            HandlerItem::Arm(arm) => {
                                canonicalize_effect_qualifier(&mut arm.qualifier, scope);
                                let mut arm_locals = locals.clone();
                                for pat in &arm.params {
                                    collect_pat_vars(pat, &mut arm_locals);
                                }
                                resolve_expr(&mut arm.body, scope, &arm_locals);
                            }
                            HandlerItem::Return(ret) => {
                                let mut ret_locals = locals.clone();
                                for pat in &ret.params {
                                    collect_pat_vars(pat, &mut ret_locals);
                                }
                                resolve_expr(&mut ret.body, scope, &ret_locals);
                            }
                        }
                    }
                }
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let mut do_locals = locals.clone();
            for (pat, val) in bindings.iter_mut() {
                resolve_pat(pat, scope);
                resolve_expr(val, scope, &do_locals);
                collect_pat_bindings(pat, &mut do_locals);
            }
            resolve_expr(success, scope, &do_locals);
            for arm in else_arms.iter_mut() {
                let arm = &mut arm.node;
                resolve_pat(&mut arm.pattern, scope);
                let mut arm_locals = locals.clone();
                collect_pat_bindings(&arm.pattern, &mut arm_locals);
                if let Some(g) = &mut arm.guard {
                    resolve_expr(g, scope, &arm_locals);
                }
                resolve_expr(&mut arm.body, scope, &arm_locals);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms.iter_mut() {
                let arm = &mut arm.node;
                resolve_pat(&mut arm.pattern, scope);
                let mut arm_locals = locals.clone();
                collect_pat_bindings(&arm.pattern, &mut arm_locals);
                if let Some(g) = &mut arm.guard {
                    resolve_expr(g, scope, &arm_locals);
                }
                resolve_expr(&mut arm.body, scope, &arm_locals);
            }
            if let Some((timeout, body)) = after_clause {
                resolve_expr(timeout, scope, locals);
                resolve_expr(body, scope, locals);
            }
        }
        ExprKind::EffectCall {
            qualifier, args, ..
        } => {
            canonicalize_effect_qualifier(qualifier, scope);
            for a in args.iter_mut() {
                resolve_expr(a, scope, locals);
            }
        }
        ExprKind::Resume { value, .. } => {
            resolve_expr(value, scope, locals);
        }
        ExprKind::ListComprehension {
            body, qualifiers, ..
        } => {
            let mut comp_locals = locals.clone();
            for qual in qualifiers.iter_mut() {
                match qual {
                    ComprehensionQualifier::Generator(pat, iterable) => {
                        resolve_expr(iterable, scope, &comp_locals);
                        resolve_pat(pat, scope);
                        collect_pat_bindings(pat, &mut comp_locals);
                    }
                    ComprehensionQualifier::Guard(expr) => {
                        resolve_expr(expr, scope, &comp_locals);
                    }
                    ComprehensionQualifier::Let(pat, val) => {
                        resolve_expr(val, scope, &comp_locals);
                        resolve_pat(pat, scope);
                        collect_pat_bindings(pat, &mut comp_locals);
                    }
                }
            }
            resolve_expr(body, scope, &comp_locals);
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
        Pat::ConsPat { head, tail, .. } => {
            resolve_pat(head, scope);
            resolve_pat(tail, scope);
        }
        _ => {}
    }
}

fn resolve_stmt(stmt: &mut Stmt, scope: &ScopeMap, locals: &mut HashSet<String>) {
    match stmt {
        Stmt::Expr(expr) => resolve_expr(expr, scope, locals),
        Stmt::Let { value, pattern, .. } => {
            resolve_pat(pattern, scope);
            // Value is evaluated before the binding takes effect
            resolve_expr(value, scope, locals);
            collect_pat_bindings(pattern, locals);
        }
        Stmt::LetFun {
            name,
            params,
            body,
            guard,
            ..
        } => {
            // The function name itself is local
            locals.insert(name.clone());
            let mut inner = locals.clone();
            for p in params.iter_mut() {
                resolve_pat(p, scope);
                collect_pat_bindings(p, &mut inner);
            }
            resolve_expr(body, scope, &inner);
            if let Some(g) = guard {
                resolve_expr(g, scope, &inner);
            }
        }
    }
}
