use super::*;
use crate::ast::*;
use crate::typechecker::{Diagnostic, Severity};

/// Expand all `deriving` clauses in a program, appending synthetic `ImplDef`
/// nodes after each `TypeDef` that has them. Returns diagnostics for
/// unsupported derive requests.
///
/// `imported` carries trait/type summaries pulled from imported modules; it is
/// now used only to let `inherit_trait_defaults` clone default-method bodies
/// from imported traits. Callers without import context can pass
/// `&ImportedDecls::empty()`.
pub fn expand_derives(program: &mut Vec<Decl>, imported: &ImportedDecls) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    // Build a fresh program, splicing each decl's derived siblings (the
    // built-in `deriving (Show, Eq, …)` impls) in directly after the decl they
    // come from, so they stay adjacent to their type.
    let original = std::mem::take(program);

    let current_module = original.iter().find_map(|d| {
        if let Decl::ModuleDecl { path, .. } = d {
            Some(path.join("."))
        } else {
            None
        }
    });
    let mut scope = DeriveScope::new(imported, current_module.as_deref());
    let local_defining_values: std::collections::HashSet<String> = original
        .iter()
        .filter_map(|d| match d {
            Decl::FunSignature { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let local_defining_constructors: std::collections::HashSet<String> = original
        .iter()
        .flat_map(|d| match d {
            Decl::TypeDef { variants, .. } => {
                variants.iter().map(|v| v.node.name.clone()).collect()
            }
            _ => Vec::new(),
        })
        .collect();

    // Collect local trait definitions so `inherit_trait_defaults` can clone
    // default-method bodies into impls that omit them. (This is the only thing
    // the derive scope is used for now that routed/Generic derives are gone.)
    for d in &original {
        if let Decl::TraitDef {
            name,
            type_params,
            methods,
            ..
        } = d
        {
            scope.add_local_trait(
                name.clone(),
                RoutedTraitInfo {
                    type_params: type_params.clone(),
                    methods: methods.iter().map(|m| m.node.clone()).collect(),
                    defining_module: current_module.clone(),
                    defining_module_values: local_defining_values.clone(),
                    defining_module_constructors: local_defining_constructors.clone(),
                },
            );
        }
    }

    let mut rebuilt: Vec<Decl> = Vec::with_capacity(original.len());
    for decl in &original {
        let mut extra: Vec<Decl> = Vec::new();
        match decl {
            Decl::TypeDef {
                name,
                type_params,
                variants,
                deriving,
                span,
                ..
            } => {
                // Ord requires Eq (supertrait). Automatically derive Eq if Ord
                // is requested but Eq isn't explicitly listed.
                let needs_eq = deriving.iter().any(|d| d.is_plain_named("Ord"))
                    && !deriving.iter().any(|d| d.is_plain_named("Eq"));

                if needs_eq
                    && let Some(impl_def) =
                        generate_derive("Eq", name, type_params, variants, *span)
                {
                    extra.push(impl_def);
                }

                for spec in deriving {
                    let trait_name = &spec.trait_name;
                    if !spec.type_args.is_empty() {
                        errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot derive `{trait_name}` with type arguments"),
                            span: Some(spec.span),
                        });
                        continue;
                    }
                    match generate_derive(trait_name, name, type_params, variants, *span) {
                        Some(impl_def) => extra.push(impl_def),
                        None => errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot derive `{trait_name}` for type `{name}`"),
                            span: Some(*span),
                        }),
                    }
                }
            }
            Decl::RecordDef {
                public,
                name,
                type_params,
                fields,
                deriving,
                span,
                ..
            } => {
                for spec in deriving {
                    let trait_name = &spec.trait_name;
                    if !spec.type_args.is_empty() {
                        errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot derive `{trait_name}` with type arguments"),
                            span: Some(spec.span),
                        });
                        continue;
                    }
                    match generate_record_derive(
                        *public,
                        trait_name,
                        name,
                        type_params,
                        fields,
                        *span,
                    ) {
                        Ok(decls) => extra.extend(decls),
                        Err(Some(diag)) => errors.push(diag),
                        Err(None) => errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot derive `{trait_name}` for record `{name}`"),
                            span: Some(*span),
                        }),
                    }
                }
            }
            _ => {}
        }
        rebuilt.push(decl.clone());
        rebuilt.extend(extra);
    }
    *program = rebuilt;

    // Inheritance pass: walk every impl and inject default-body methods for
    // any trait method the impl omits. After this, downstream passes
    // (name resolution, typechecking, elaboration, codegen) see a complete
    // impl regardless of how many methods the user wrote out.
    //
    // Note: the local-trait scope above (and `imported`) cover both
    // user-written impls and the bridge/delegating impls just synthesized by
    // `derive_routed` — the latter intentionally skip defaulted methods so
    // this pass fills them in.
    inherit_trait_defaults(program, &scope);

    errors
}

/// Walk impl decls and clone any missing default bodies from the impl's trait
/// into the impl, with fresh NodeIds. The trait may be local or imported;
/// `scope` already merges both.
pub(crate) fn inherit_trait_defaults(program: &mut [Decl], scope: &DeriveScope<'_>) {
    let current_module = scope.current_module.map(|s| s.to_string());
    for decl in program.iter_mut() {
        let Decl::ImplDef {
            trait_name,
            trait_name_span,
            methods,
            ..
        } = decl
        else {
            continue;
        };
        let impl_site = *trait_name_span;
        let Ok(Some(entry)) = scope.trait_entry(trait_name) else {
            continue;
        };
        let provided: std::collections::HashSet<String> =
            methods.iter().map(|m| m.node.name.clone()).collect();
        // Trait methods shadow the qualification rewrite below: a free
        // reference to one of the trait's own methods inside a default body
        // must stay bare so trait dispatch can dispatch it through the impl.
        let trait_method_names: std::collections::HashSet<String> =
            entry.info.methods.iter().map(|m| m.name.clone()).collect();
        // Only qualify when the trait is defined in a different module than
        // the impl. Same-module impls already resolve module-local names.
        let qualify_module: Option<&str> = entry
            .info
            .defining_module
            .as_deref()
            .filter(|m| current_module.as_deref() != Some(*m));
        for tm in &entry.info.methods {
            if provided.contains(&tm.name) {
                continue;
            }
            let Some(default) = &tm.default_body else {
                continue;
            };
            let mut params = default.params.clone();
            let mut body = default.body.clone();
            for p in &mut params {
                crate::desugar::freshen_pat_ids(p);
                crate::desugar::retarget_pat_spans(p, impl_site);
            }
            crate::desugar::freshen_expr_ids(&mut body);
            crate::desugar::retarget_expr_spans(&mut body, impl_site);
            if let Some(module) = qualify_module {
                let mut bound: std::collections::HashSet<String> = std::collections::HashSet::new();
                for p in &params {
                    collect_pat_bindings(p, &mut bound);
                }
                qualify_free_vars(
                    &mut body,
                    module,
                    &entry.info.defining_module_values,
                    &trait_method_names,
                    &mut bound,
                );
                // Constructors live in their own namespace and are never
                // shadowed by the value bindings tracked above, so qualify
                // them in a separate, scope-insensitive walk.
                qualify_ctor_refs(&mut body, module, &entry.info.defining_module_constructors);
            }
            methods.push(Annotated::bare(ImplMethod {
                name: tm.name.clone(),
                name_span: impl_site,
                params,
                body,
            }));
        }
    }
}

/// Rewrite free `Var` references inside `expr` that name a top-level value
/// in the trait's defining module to `QualifiedName { module, name }`. Used
/// when a trait's default-method body is cloned into a downstream-module
/// impl: free identifiers need to keep resolving against the trait's
/// module, not the downstream module.
pub(crate) fn qualify_free_vars(
    expr: &mut Expr,
    module: &str,
    module_values: &std::collections::HashSet<String>,
    trait_methods: &std::collections::HashSet<String>,
    bound: &mut std::collections::HashSet<String>,
) {
    match &mut expr.kind {
        ExprKind::Var { name } => {
            if !bound.contains(name)
                && !trait_methods.contains(name)
                && module_values.contains(name)
            {
                expr.kind = ExprKind::QualifiedName {
                    module: module.to_string(),
                    name: name.clone(),
                    canonical_module: Some(module.to_string()),
                };
            }
        }
        ExprKind::Lit { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictMethodAccess { .. }
        | ExprKind::DictSuperAccess { .. }
        | ExprKind::DictRef { .. } => {}
        ExprKind::App { func, arg } => {
            qualify_free_vars(func, module, module_values, trait_methods, bound);
            qualify_free_vars(arg, module, module_values, trait_methods, bound);
        }
        ExprKind::BinOp { left, right, .. } => {
            qualify_free_vars(left, module, module_values, trait_methods, bound);
            qualify_free_vars(right, module, module_values, trait_methods, bound);
        }
        ExprKind::UnaryMinus { expr: inner } => {
            qualify_free_vars(inner, module, module_values, trait_methods, bound);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            qualify_free_vars(cond, module, module_values, trait_methods, bound);
            qualify_free_vars(then_branch, module, module_values, trait_methods, bound);
            qualify_free_vars(else_branch, module, module_values, trait_methods, bound);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            qualify_free_vars(scrutinee, module, module_values, trait_methods, bound);
            for ann_arm in arms {
                let mut arm_bound = bound.clone();
                collect_pat_bindings(&ann_arm.node.pattern, &mut arm_bound);
                if let Some(g) = &mut ann_arm.node.guard {
                    qualify_free_vars(g, module, module_values, trait_methods, &mut arm_bound);
                }
                qualify_free_vars(
                    &mut ann_arm.node.body,
                    module,
                    module_values,
                    trait_methods,
                    &mut arm_bound,
                );
            }
        }
        ExprKind::Block { stmts, .. } => {
            let saved = bound.clone();
            for ann_stmt in stmts {
                qualify_stmt_free_vars(
                    &mut ann_stmt.node,
                    module,
                    module_values,
                    trait_methods,
                    bound,
                );
            }
            *bound = saved;
        }
        ExprKind::Lambda { params, body } => {
            let saved = bound.clone();
            for p in params.iter() {
                collect_pat_bindings(p, bound);
            }
            qualify_free_vars(body, module, module_values, trait_methods, bound);
            *bound = saved;
        }
        ExprKind::FieldAccess { expr: inner, .. } => {
            qualify_free_vars(inner, module, module_values, trait_methods, bound);
        }
        ExprKind::RecordCreate { fields, .. }
        | ExprKind::AnonRecordCreate { fields, .. }
        | ExprKind::RecordBuild { fields, .. } => {
            for (_, _, val) in fields {
                qualify_free_vars(val, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            qualify_free_vars(record, module, module_values, trait_methods, bound);
            for (_, _, val) in fields {
                qualify_free_vars(val, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                qualify_free_vars(arg, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::With {
            expr: inner,
            handler: _,
        } => {
            qualify_free_vars(inner, module, module_values, trait_methods, bound);
        }
        ExprKind::Resume { value } => {
            qualify_free_vars(value, module, module_values, trait_methods, bound);
        }
        ExprKind::HandlerExpr { .. } => {}
        ExprKind::Tuple { elements } => {
            for e in elements {
                qualify_free_vars(e, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let saved = bound.clone();
            for (p, e) in bindings {
                qualify_free_vars(e, module, module_values, trait_methods, bound);
                collect_pat_bindings(p, bound);
            }
            qualify_free_vars(success, module, module_values, trait_methods, bound);
            for ann_arm in else_arms {
                let mut arm_bound = saved.clone();
                collect_pat_bindings(&ann_arm.node.pattern, &mut arm_bound);
                if let Some(g) = &mut ann_arm.node.guard {
                    qualify_free_vars(g, module, module_values, trait_methods, &mut arm_bound);
                }
                qualify_free_vars(
                    &mut ann_arm.node.body,
                    module,
                    module_values,
                    trait_methods,
                    &mut arm_bound,
                );
            }
            *bound = saved;
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann_arm in arms {
                let mut arm_bound = bound.clone();
                collect_pat_bindings(&ann_arm.node.pattern, &mut arm_bound);
                if let Some(g) = &mut ann_arm.node.guard {
                    qualify_free_vars(g, module, module_values, trait_methods, &mut arm_bound);
                }
                qualify_free_vars(
                    &mut ann_arm.node.body,
                    module,
                    module_values,
                    trait_methods,
                    &mut arm_bound,
                );
            }
            if let Some((timeout, body)) = after_clause {
                qualify_free_vars(timeout, module, module_values, trait_methods, bound);
                qualify_free_vars(body, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::Ascription { expr: inner, .. } => {
            qualify_free_vars(inner, module, module_values, trait_methods, bound);
        }
        ExprKind::BitString { segments } => {
            for seg in segments {
                qualify_free_vars(&mut seg.value, module, module_values, trait_methods, bound);
                if let Some(size) = &mut seg.size {
                    qualify_free_vars(size, module, module_values, trait_methods, bound);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                qualify_free_vars(&mut seg.node, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                qualify_free_vars(&mut seg.node, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::Cons { head, tail } => {
            qualify_free_vars(head, module, module_values, trait_methods, bound);
            qualify_free_vars(tail, module, module_values, trait_methods, bound);
        }
        ExprKind::ListLit { elements, .. } => {
            for e in elements {
                qualify_free_vars(&mut e.node, module, module_values, trait_methods, bound);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    qualify_free_vars(e, module, module_values, trait_methods, bound);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            let saved = bound.clone();
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(p, e) => {
                        qualify_free_vars(e, module, module_values, trait_methods, bound);
                        collect_pat_bindings(p, bound);
                    }
                    ComprehensionQualifier::Let(p, e) => {
                        qualify_free_vars(e, module, module_values, trait_methods, bound);
                        collect_pat_bindings(p, bound);
                    }
                    ComprehensionQualifier::Guard(e) => {
                        qualify_free_vars(e, module, module_values, trait_methods, bound);
                    }
                }
            }
            qualify_free_vars(body, module, module_values, trait_methods, bound);
            *bound = saved;
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                qualify_free_vars(arg, module, module_values, trait_methods, bound);
            }
        }
    }
}

pub(crate) fn qualify_stmt_free_vars(
    stmt: &mut Stmt,
    module: &str,
    module_values: &std::collections::HashSet<String>,
    trait_methods: &std::collections::HashSet<String>,
    bound: &mut std::collections::HashSet<String>,
) {
    match stmt {
        Stmt::Let { pattern, value, .. } => {
            qualify_free_vars(value, module, module_values, trait_methods, bound);
            collect_pat_bindings(pattern, bound);
        }
        Stmt::LetFun {
            name,
            params,
            guard,
            body,
            ..
        } => {
            bound.insert(name.clone());
            let saved = bound.clone();
            for p in params.iter() {
                collect_pat_bindings(p, bound);
            }
            if let Some(g) = guard {
                qualify_free_vars(g, module, module_values, trait_methods, bound);
            }
            qualify_free_vars(body, module, module_values, trait_methods, bound);
            *bound = saved;
        }
        Stmt::Expr(e) => qualify_free_vars(e, module, module_values, trait_methods, bound),
    }
}

/// Rewrite bare data-constructor references inside a cloned default-method
/// body to their module-qualified canonical name, so they resolve against the
/// trait's defining module rather than the downstream impl-site module.
/// Constructors occupy their own namespace and are never shadowed by local
/// value bindings, so this walk is scope-insensitive (no `bound` tracking).
pub(crate) fn qualify_ctor_refs(
    expr: &mut Expr,
    module: &str,
    module_constructors: &std::collections::HashSet<String>,
) {
    match &mut expr.kind {
        ExprKind::Constructor { name } => {
            if !name.contains('.') && module_constructors.contains(name) {
                *name = format!("{}.{}", module, name);
            }
        }
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictMethodAccess { .. }
        | ExprKind::DictSuperAccess { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::HandlerExpr { .. } => {}
        ExprKind::App { func, arg } => {
            qualify_ctor_refs(func, module, module_constructors);
            qualify_ctor_refs(arg, module, module_constructors);
        }
        ExprKind::BinOp { left, right, .. } => {
            qualify_ctor_refs(left, module, module_constructors);
            qualify_ctor_refs(right, module, module_constructors);
        }
        ExprKind::UnaryMinus { expr: inner } => {
            qualify_ctor_refs(inner, module, module_constructors);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            qualify_ctor_refs(cond, module, module_constructors);
            qualify_ctor_refs(then_branch, module, module_constructors);
            qualify_ctor_refs(else_branch, module, module_constructors);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            qualify_ctor_refs(scrutinee, module, module_constructors);
            for ann_arm in arms {
                qualify_ctor_pat(&mut ann_arm.node.pattern, module, module_constructors);
                if let Some(g) = &mut ann_arm.node.guard {
                    qualify_ctor_refs(g, module, module_constructors);
                }
                qualify_ctor_refs(&mut ann_arm.node.body, module, module_constructors);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for ann_stmt in stmts {
                match &mut ann_stmt.node {
                    Stmt::Let { pattern, value, .. } => {
                        qualify_ctor_pat(pattern, module, module_constructors);
                        qualify_ctor_refs(value, module, module_constructors);
                    }
                    Stmt::LetFun {
                        params,
                        guard,
                        body,
                        ..
                    } => {
                        for p in params.iter_mut() {
                            qualify_ctor_pat(p, module, module_constructors);
                        }
                        if let Some(g) = guard {
                            qualify_ctor_refs(g, module, module_constructors);
                        }
                        qualify_ctor_refs(body, module, module_constructors);
                    }
                    Stmt::Expr(e) => qualify_ctor_refs(e, module, module_constructors),
                }
            }
        }
        ExprKind::Lambda { params, body } => {
            for p in params.iter_mut() {
                qualify_ctor_pat(p, module, module_constructors);
            }
            qualify_ctor_refs(body, module, module_constructors);
        }
        ExprKind::FieldAccess { expr: inner, .. } => {
            qualify_ctor_refs(inner, module, module_constructors);
        }
        ExprKind::RecordCreate { fields, .. }
        | ExprKind::AnonRecordCreate { fields, .. }
        | ExprKind::RecordBuild { fields, .. } => {
            for (_, _, val) in fields {
                qualify_ctor_refs(val, module, module_constructors);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            qualify_ctor_refs(record, module, module_constructors);
            for (_, _, val) in fields {
                qualify_ctor_refs(val, module, module_constructors);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                qualify_ctor_refs(arg, module, module_constructors);
            }
        }
        ExprKind::With { expr: inner, .. } => {
            qualify_ctor_refs(inner, module, module_constructors);
        }
        ExprKind::Resume { value } => qualify_ctor_refs(value, module, module_constructors),
        ExprKind::Tuple { elements } => {
            for e in elements {
                qualify_ctor_refs(e, module, module_constructors);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (p, e) in bindings {
                qualify_ctor_pat(p, module, module_constructors);
                qualify_ctor_refs(e, module, module_constructors);
            }
            qualify_ctor_refs(success, module, module_constructors);
            for ann_arm in else_arms {
                qualify_ctor_pat(&mut ann_arm.node.pattern, module, module_constructors);
                if let Some(g) = &mut ann_arm.node.guard {
                    qualify_ctor_refs(g, module, module_constructors);
                }
                qualify_ctor_refs(&mut ann_arm.node.body, module, module_constructors);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann_arm in arms {
                qualify_ctor_pat(&mut ann_arm.node.pattern, module, module_constructors);
                if let Some(g) = &mut ann_arm.node.guard {
                    qualify_ctor_refs(g, module, module_constructors);
                }
                qualify_ctor_refs(&mut ann_arm.node.body, module, module_constructors);
            }
            if let Some((timeout, body)) = after_clause {
                qualify_ctor_refs(timeout, module, module_constructors);
                qualify_ctor_refs(body, module, module_constructors);
            }
        }
        ExprKind::Ascription { expr: inner, .. } => {
            qualify_ctor_refs(inner, module, module_constructors);
        }
        ExprKind::BitString { segments } => {
            for seg in segments {
                qualify_ctor_refs(&mut seg.value, module, module_constructors);
                if let Some(size) = &mut seg.size {
                    qualify_ctor_refs(size, module, module_constructors);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                qualify_ctor_refs(&mut seg.node, module, module_constructors);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                qualify_ctor_refs(&mut seg.node, module, module_constructors);
            }
        }
        ExprKind::Cons { head, tail } => {
            qualify_ctor_refs(head, module, module_constructors);
            qualify_ctor_refs(tail, module, module_constructors);
        }
        ExprKind::ListLit { elements, .. } => {
            for e in elements {
                qualify_ctor_refs(&mut e.node, module, module_constructors);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    qualify_ctor_refs(e, module, module_constructors);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(p, e) | ComprehensionQualifier::Let(p, e) => {
                        qualify_ctor_pat(p, module, module_constructors);
                        qualify_ctor_refs(e, module, module_constructors);
                    }
                    ComprehensionQualifier::Guard(e) => {
                        qualify_ctor_refs(e, module, module_constructors);
                    }
                }
            }
            qualify_ctor_refs(body, module, module_constructors);
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                qualify_ctor_refs(arg, module, module_constructors);
            }
        }
    }
}

/// Companion to `qualify_ctor_refs` for constructor references that appear in
/// patterns (e.g. a default body that destructures one of the trait module's
/// own types).
pub(crate) fn qualify_ctor_pat(
    pat: &mut Pat,
    module: &str,
    module_constructors: &std::collections::HashSet<String>,
) {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } | Pat::Var { .. } => {}
        Pat::Constructor { name, args, .. } => {
            if !name.contains('.') && module_constructors.contains(name) {
                *name = format!("{}.{}", module, name);
            }
            for a in args {
                qualify_ctor_pat(a, module, module_constructors);
            }
        }
        Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
            for (_, alias) in fields {
                if let Some(p) = alias {
                    qualify_ctor_pat(p, module, module_constructors);
                }
            }
        }
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            for e in elements {
                qualify_ctor_pat(e, module, module_constructors);
            }
        }
        Pat::StringPrefix { rest, .. } => qualify_ctor_pat(rest, module, module_constructors),
        Pat::BitStringPat { segments, .. } => {
            for seg in segments {
                qualify_ctor_pat(&mut seg.value, module, module_constructors);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            qualify_ctor_pat(head, module, module_constructors);
            qualify_ctor_pat(tail, module, module_constructors);
        }
        Pat::Or { patterns, .. } => {
            for p in patterns {
                qualify_ctor_pat(p, module, module_constructors);
            }
        }
    }
}

pub(crate) fn collect_pat_bindings(pat: &Pat, out: &mut std::collections::HashSet<String>) {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
        Pat::Var { name, .. } => {
            out.insert(name.clone());
        }
        Pat::Constructor { args, .. } => {
            for a in args {
                collect_pat_bindings(a, out);
            }
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
        Pat::Tuple { elements, .. } => {
            for e in elements {
                collect_pat_bindings(e, out);
            }
        }
        Pat::StringPrefix { rest, .. } => collect_pat_bindings(rest, out),
        Pat::BitStringPat { segments, .. } => {
            for seg in segments {
                collect_pat_bindings(&seg.value, out);
            }
        }
        Pat::ListPat { elements, .. } => {
            for e in elements {
                collect_pat_bindings(e, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_bindings(head, out);
            collect_pat_bindings(tail, out);
        }
        Pat::Or { patterns, .. } => {
            for p in patterns {
                collect_pat_bindings(p, out);
            }
        }
    }
}
