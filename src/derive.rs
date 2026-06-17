//! Deriving pass: expands `deriving (Show, ...)` clauses on type definitions
//! into synthetic `ImplDef` nodes. Runs before typechecking so the generated
//! impls are validated like any hand-written impl.

use crate::ast::*;
use crate::token::Span;
use crate::token::StringKind;
use crate::typechecker::{Diagnostic, Severity};
use std::collections::HashMap;
use std::path::Path;

/// Pre-derive summaries for names visible from imports. This is intentionally
/// structural, not semantic resolution: derive uses it to emit qualified syntax,
/// then the normal resolver records authoritative NodeId-keyed meaning later.
#[derive(Default, Clone)]
pub struct ImportedDecls {
    pub traits: HashMap<String, Vec<SummaryEntry<RoutedTraitInfo>>>,
    pub types: HashMap<String, Vec<SummaryEntry<WrapperTypeInfo>>>,
    pub records: HashMap<String, Vec<SummaryEntry<WrapperRecordInfo>>>,
}

#[derive(Clone)]
pub struct SummaryEntry<T> {
    pub canonical: String,
    pub info: T,
}

#[derive(Clone)]
pub struct WrapperTypeInfo {
    pub type_params: Vec<TypeParam>,
    pub variants: Vec<TypeConstructor>,
    pub derives_generic: bool,
}

#[derive(Clone)]
pub struct WrapperRecordInfo {
    pub type_params: Vec<TypeParam>,
    pub fields: Vec<(String, TypeExpr)>,
    pub derives_generic: bool,
}

impl ImportedDecls {
    pub fn empty() -> Self {
        Self::default()
    }
}

#[derive(Default, Clone)]
struct ModuleSummary {
    traits: HashMap<String, RoutedTraitInfo>,
    types: HashMap<String, WrapperTypeInfo>,
    records: HashMap<String, WrapperRecordInfo>,
}

/// Walk a program's imports and gather the structural summaries visible to
/// derive expansion. Stdlib modules are loaded from embedded sources; project
/// modules are looked up via `module_map`. Parse/missing-module errors are
/// skipped here because the typechecker import pass reports them authoritatively.
///
/// Prelude imports are included because the prelude is auto-loaded into every
/// module, making `Result`, `Maybe`, and `Std.Generic` available at derive sites.
pub fn collect_imported_decls(
    program: &[Decl],
    module_map: Option<&crate::typechecker::ModuleMap>,
) -> ImportedDecls {
    let mut out = ImportedDecls::default();

    // Pull in everything the prelude imports first. This makes `Result`,
    // `Maybe`, and the Generic building blocks visible to expand_derives
    // without each call site having to thread them explicitly.
    const PRELUDE_SRC: &str = include_str!("stdlib/prelude.saga");
    if let Ok(prelude_tokens) = crate::lexer::Lexer::new(PRELUDE_SRC).lex()
        && let Ok(prelude_program) = crate::parser::Parser::new(prelude_tokens).parse_program()
    {
        collect_summaries_from_imports(&prelude_program, module_map, &mut out);
    }

    collect_summaries_from_imports(program, module_map, &mut out);
    out
}

fn collect_summaries_from_imports(
    program: &[Decl],
    module_map: Option<&crate::typechecker::ModuleMap>,
    out: &mut ImportedDecls,
) {
    for decl in program {
        if let Decl::Import {
            module_path,
            alias,
            exposing,
            ..
        } = decl
        {
            let module_name = module_path.join(".");
            let source = if let Some(src) = crate::typechecker::builtin_module_source(module_path) {
                src.to_string()
            } else if let Some(map) = module_map {
                match map
                    .get(&module_name)
                    .and_then(|p| std::fs::read_to_string(p).ok())
                {
                    Some(s) => s,
                    None => continue,
                }
            } else {
                continue;
            };
            let Ok(tokens) = crate::lexer::Lexer::new(&source).lex() else {
                continue;
            };
            let Ok(prog) = crate::parser::Parser::new(tokens).parse_program() else {
                continue;
            };
            let summary = module_summary(&prog);
            merge_summary_import(
                out,
                &module_name,
                alias.as_deref().unwrap_or(&module_name),
                exposing.as_ref(),
                &summary,
            );
        }
    }
}

fn module_summary(program: &[Decl]) -> ModuleSummary {
    let mut summary = ModuleSummary::default();
    let module_name = program.iter().find_map(|d| {
        if let Decl::ModuleDecl { path, .. } = d {
            Some(path.join("."))
        } else {
            None
        }
    });
    for d in program {
        match d {
            Decl::TypeDef {
                name,
                type_params,
                variants,
                deriving,
                public: true,
                opaque: false,
                ..
            } => {
                summary.types.insert(
                    name.clone(),
                    WrapperTypeInfo {
                        type_params: type_params.clone(),
                        variants: variants.iter().map(|v| v.node.clone()).collect(),
                        derives_generic: deriving.iter().any(|d| d.is_plain_named("Generic")),
                    },
                );
            }
            Decl::RecordDef {
                name,
                type_params,
                fields,
                deriving,
                public: true,
                ..
            } => {
                summary.records.insert(
                    name.clone(),
                    WrapperRecordInfo {
                        type_params: type_params.clone(),
                        fields: fields
                            .iter()
                            .map(|f| (f.node.0.clone(), f.node.1.clone()))
                            .collect(),
                        derives_generic: deriving.iter().any(|d| d.is_plain_named("Generic")),
                    },
                );
            }
            _ => {}
        }
    }
    let local_type_names: std::collections::HashSet<String> = summary
        .types
        .keys()
        .chain(summary.records.keys())
        .cloned()
        .collect();
    let defining_module_values: std::collections::HashSet<String> = program
        .iter()
        .filter_map(|d| match d {
            Decl::FunSignature {
                name, public: true, ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect();
    for d in program {
        if let Decl::TraitDef {
            name,
            type_params,
            functional_dependency,
            methods,
            public: true,
            ..
        } = d
        {
            summary.traits.insert(
                name.clone(),
                RoutedTraitInfo {
                    type_params: type_params.clone(),
                    is_functional: functional_dependency.is_some(),
                    methods: methods
                        .iter()
                        .map(|m| {
                            let mut method = m.node.clone();
                            method.params = method
                                .params
                                .into_iter()
                                .map(|(label, ty)| {
                                    (
                                        label,
                                        qualify_summary_type_expr(
                                            ty,
                                            module_name.as_deref(),
                                            &local_type_names,
                                        ),
                                    )
                                })
                                .collect();
                            method.return_type = qualify_summary_type_expr(
                                method.return_type,
                                module_name.as_deref(),
                                &local_type_names,
                            );
                            method
                        })
                        .collect(),
                    defining_module: module_name.clone(),
                    defining_module_values: defining_module_values.clone(),
                },
            );
        }
    }
    summary
}

fn qualify_summary_type_expr(
    ty: TypeExpr,
    module_name: Option<&str>,
    local_type_names: &std::collections::HashSet<String>,
) -> TypeExpr {
    match ty {
        TypeExpr::Named { id, name, span } => {
            let name = if !name.contains('.') && local_type_names.contains(&name) {
                module_name.map(|m| format!("{m}.{name}")).unwrap_or(name)
            } else {
                name
            };
            TypeExpr::Named { id, name, span }
        }
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id,
            func: Box::new(qualify_summary_type_expr(
                *func,
                module_name,
                local_type_names,
            )),
            arg: Box::new(qualify_summary_type_expr(
                *arg,
                module_name,
                local_type_names,
            )),
            span,
        },
        TypeExpr::Arrow {
            id,
            from,
            to,
            effects,
            effect_row_var,
            span,
        } => TypeExpr::Arrow {
            id,
            from: Box::new(qualify_summary_type_expr(
                *from,
                module_name,
                local_type_names,
            )),
            to: Box::new(qualify_summary_type_expr(
                *to,
                module_name,
                local_type_names,
            )),
            effects,
            effect_row_var,
            span,
        },
        TypeExpr::Record {
            id,
            fields,
            multiline,
            span,
        } => TypeExpr::Record {
            id,
            fields: fields
                .into_iter()
                .map(|(label, ty)| {
                    (
                        label,
                        qualify_summary_type_expr(ty, module_name, local_type_names),
                    )
                })
                .collect(),
            multiline,
            span,
        },
        TypeExpr::Labeled {
            id,
            label,
            inner,
            span,
        } => TypeExpr::Labeled {
            id,
            label,
            inner: Box::new(qualify_summary_type_expr(
                *inner,
                module_name,
                local_type_names,
            )),
            span,
        },
        other => other,
    }
}

fn merge_summary_import(
    out: &mut ImportedDecls,
    module_name: &str,
    prefix: &str,
    exposing: Option<&crate::ast::Exposing>,
    summary: &ModuleSummary,
) {
    let exposed_surface = |name: &str| -> Option<String> {
        match exposing {
            None => Some(name.to_string()),
            Some(e) => e.surface_name_for_origin(name),
        }
    };
    for (name, info) in &summary.traits {
        register_summary_entry(
            &mut out.traits,
            &format!("{module_name}.{name}"),
            module_name,
            name,
            info,
        );
        if prefix != module_name {
            register_summary_entry(
                &mut out.traits,
                &format!("{prefix}.{name}"),
                module_name,
                name,
                info,
            );
        }
        if let Some(surface) = exposed_surface(name) {
            register_summary_entry(&mut out.traits, &surface, module_name, name, info);
        }
    }
    for (name, info) in &summary.types {
        register_summary_entry(
            &mut out.types,
            &format!("{module_name}.{name}"),
            module_name,
            name,
            info,
        );
        if prefix != module_name {
            register_summary_entry(
                &mut out.types,
                &format!("{prefix}.{name}"),
                module_name,
                name,
                info,
            );
        }
        if let Some(surface) = exposed_surface(name) {
            register_summary_entry(&mut out.types, &surface, module_name, name, info);
        }
    }
    for (name, info) in &summary.records {
        register_summary_entry(
            &mut out.records,
            &format!("{module_name}.{name}"),
            module_name,
            name,
            info,
        );
        if prefix != module_name {
            register_summary_entry(
                &mut out.records,
                &format!("{prefix}.{name}"),
                module_name,
                name,
                info,
            );
        }
        if let Some(surface) = exposed_surface(name) {
            register_summary_entry(&mut out.records, &surface, module_name, name, info);
        }
    }
}

fn register_summary_entry<T: Clone>(
    map: &mut HashMap<String, Vec<SummaryEntry<T>>>,
    visible: &str,
    module_name: &str,
    name: &str,
    info: &T,
) {
    let canonical = format!("{module_name}.{name}");
    let entries = map.entry(visible.to_string()).or_default();
    if entries.iter().any(|e| e.canonical == canonical) {
        return;
    }
    entries.push(SummaryEntry {
        canonical,
        info: info.clone(),
    });
}

/// Build an `ImportedDecls` by scanning a project root for `.saga` files.
/// Convenience wrapper used by integration tests that don't have a checker
/// handy. Real callers (cli, lsp) should use `collect_imported_decls` with
/// the checker's module map.
pub fn collect_from_project_root(program: &[Decl], root: &Path) -> ImportedDecls {
    let map = crate::typechecker::scan_source_dir(root).ok();
    collect_imported_decls(program, map.as_ref())
}

/// Expand all `deriving` clauses in a program, appending synthetic `ImplDef`
/// nodes after each `TypeDef` that has them. Returns diagnostics for
/// unsupported derive requests.
///
/// `imported` carries trait/type summaries pulled from imported modules so
/// routed derives (`deriving (Foo)` where `Foo` is imported) can resolve.
/// Callers without import context can pass `&ImportedDecls::empty()`.
pub fn expand_derives(program: &mut Vec<Decl>, imported: &ImportedDecls) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    // Build a fresh program, splicing each decl's derived siblings in directly
    // after it. Generic-derived `Rep__T` typedefs and their impls must be
    // visible before any later user impl whose where-app form mentions
    // `Generic T r`, otherwise the where-app's coherence lookup fires before
    // the impl is registered.
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
    for d in &original {
        match d {
            Decl::TraitDef {
                name,
                type_params,
                functional_dependency,
                methods,
                ..
            } => {
                scope.add_local_trait(
                    name.clone(),
                    RoutedTraitInfo {
                        type_params: type_params.clone(),
                        is_functional: functional_dependency.is_some(),
                        methods: methods.iter().map(|m| m.node.clone()).collect(),
                        defining_module: current_module.clone(),
                        defining_module_values: local_defining_values.clone(),
                    },
                );
            }
            Decl::TypeDef {
                name,
                type_params,
                variants,
                deriving,
                ..
            } => {
                scope.add_local_type(
                    name.clone(),
                    WrapperTypeInfo {
                        type_params: type_params.clone(),
                        variants: variants.iter().map(|v| v.node.clone()).collect(),
                        derives_generic: deriving.iter().any(|d| d.is_plain_named("Generic")),
                    },
                );
            }
            Decl::RecordDef {
                name,
                type_params,
                fields,
                deriving,
                ..
            } => {
                scope.add_local_record(
                    name.clone(),
                    WrapperRecordInfo {
                        type_params: type_params.clone(),
                        fields: fields
                            .iter()
                            .map(|f| (f.node.0.clone(), f.node.1.clone()))
                            .collect(),
                        derives_generic: deriving.iter().any(|d| d.is_plain_named("Generic")),
                    },
                );
            }
            _ => {}
        }
    }

    let mut rebuilt: Vec<Decl> = Vec::with_capacity(original.len());
    for decl in &original {
        let mut extra: Vec<Decl> = Vec::new();
        match decl {
            Decl::TypeDef {
                public,
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

                // Auto-include Generic: if any non-hardcoded derive is requested
                // and Generic isn't explicitly listed, synthesize it first.
                let has_routed = deriving
                    .iter()
                    .any(|d| !d.type_args.is_empty() || !is_hardcoded_derive(d.bare_name()));
                let has_generic = deriving.iter().any(|d| d.is_plain_named("Generic"));
                if has_routed && !has_generic {
                    match derive_adt_generic(*public, name, type_params, variants, *span) {
                        Ok(decls) => extra.extend(decls),
                        Err(Some(diag)) => errors.push(diag),
                        Err(None) => errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot auto-derive `Generic` for type `{name}`"),
                            span: Some(*span),
                        }),
                    }
                }

                for spec in deriving {
                    let trait_name = &spec.trait_name;
                    let bare = spec.bare_name();
                    if !spec.type_args.is_empty() {
                        if is_hardcoded_derive(bare) {
                            errors.push(Diagnostic {
                                severity: Severity::Error,
                                message: format!(
                                    "cannot derive `{trait_name}` with type arguments"
                                ),
                                span: Some(spec.span),
                            });
                        } else {
                            match derive_applied_selectable(spec, name, type_params, *span, &scope)
                            {
                                Ok(decls) => extra.extend(decls),
                                Err(diag) => errors.push(diag),
                            }
                        }
                        continue;
                    }
                    if bare == "Generic" {
                        match derive_adt_generic(*public, name, type_params, variants, *span) {
                            Ok(decls) => extra.extend(decls),
                            Err(Some(diag)) => errors.push(diag),
                            Err(None) => errors.push(Diagnostic {
                                severity: Severity::Error,
                                message: format!("cannot derive `{trait_name}` for type `{name}`"),
                                span: Some(*span),
                            }),
                        }
                        continue;
                    }
                    if !is_hardcoded_derive(bare) {
                        match derive_routed(trait_name, name, type_params, *span, &scope) {
                            Ok(decls) => extra.extend(decls),
                            Err(diag) => errors.push(diag),
                        }
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
                let has_routed = deriving
                    .iter()
                    .any(|d| !d.type_args.is_empty() || !is_hardcoded_derive(d.bare_name()));
                let has_generic = deriving.iter().any(|d| d.is_plain_named("Generic"));
                if has_routed && !has_generic {
                    match derive_record_generic(*public, name, type_params, fields, *span) {
                        Ok(decls) => extra.extend(decls),
                        Err(Some(diag)) => errors.push(diag),
                        Err(None) => errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot auto-derive `Generic` for record `{name}`"),
                            span: Some(*span),
                        }),
                    }
                }

                for spec in deriving {
                    let trait_name = &spec.trait_name;
                    let bare = spec.bare_name();
                    if !spec.type_args.is_empty() {
                        if is_hardcoded_derive(bare) {
                            errors.push(Diagnostic {
                                severity: Severity::Error,
                                message: format!(
                                    "cannot derive `{trait_name}` with type arguments"
                                ),
                                span: Some(spec.span),
                            });
                        } else {
                            match derive_applied_selectable(spec, name, type_params, *span, &scope)
                            {
                                Ok(decls) => extra.extend(decls),
                                Err(diag) => errors.push(diag),
                            }
                        }
                        continue;
                    }
                    if !is_hardcoded_derive(bare) && bare != "Generic" {
                        match derive_routed(trait_name, name, type_params, *span, &scope) {
                            Ok(decls) => extra.extend(decls),
                            Err(diag) => errors.push(diag),
                        }
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
fn inherit_trait_defaults(program: &mut [Decl], scope: &DeriveScope<'_>) {
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
fn qualify_free_vars(
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
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}
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
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
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
        ExprKind::ListLit { elements } => {
            for e in elements {
                qualify_free_vars(e, module, module_values, trait_methods, bound);
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

fn qualify_stmt_free_vars(
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

fn collect_pat_bindings(pat: &Pat, out: &mut std::collections::HashSet<String>) {
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

/// Minimal trait info captured at expand_derives time for routed-derive
/// method/signature discovery. We only need the method names and signature
/// shapes — direction detection and body generation work off these.
#[derive(Clone)]
pub struct RoutedTraitInfo {
    pub type_params: Vec<TypeParam>,
    pub is_functional: bool,
    pub methods: Vec<TraitMethod>,
    /// Module that defines this trait, e.g. "Lib" or "Std.Generic". Used to
    /// retarget free identifiers in cloned default-method bodies so they
    /// resolve against the trait's defining module rather than the
    /// downstream impl-site module.
    pub defining_module: Option<String>,
    /// Names of top-level `fun` bindings exported from
    /// `defining_module`. A free identifier inside a cloned default body
    /// that matches one of these names is rewritten to a `QualifiedName`
    /// referencing the trait's module, so cross-module impls don't see
    /// "undefined variable" errors for identifiers defined alongside the
    /// trait.
    pub defining_module_values: std::collections::HashSet<String>,
}

struct DeriveScope<'a> {
    imported: &'a ImportedDecls,
    current_module: Option<&'a str>,
    local_traits: HashMap<String, SummaryEntry<RoutedTraitInfo>>,
    local_types: HashMap<String, SummaryEntry<WrapperTypeInfo>>,
    local_records: HashMap<String, SummaryEntry<WrapperRecordInfo>>,
}

impl<'a> DeriveScope<'a> {
    fn new(imported: &'a ImportedDecls, current_module: Option<&'a str>) -> Self {
        Self {
            imported,
            current_module,
            local_traits: HashMap::new(),
            local_types: HashMap::new(),
            local_records: HashMap::new(),
        }
    }

    fn add_local_trait(&mut self, name: String, info: RoutedTraitInfo) {
        insert_local(&mut self.local_traits, self.current_module, name, info);
    }

    fn add_local_type(&mut self, name: String, info: WrapperTypeInfo) {
        insert_local(&mut self.local_types, self.current_module, name, info);
    }

    fn add_local_record(&mut self, name: String, info: WrapperRecordInfo) {
        insert_local(&mut self.local_records, self.current_module, name, info);
    }

    fn trait_entry(&self, name: &str) -> Result<Option<&SummaryEntry<RoutedTraitInfo>>, String> {
        lookup_summary(name, &self.local_traits, &self.imported.traits, "trait")
    }

    fn type_entry(&self, name: &str) -> Result<Option<&SummaryEntry<WrapperTypeInfo>>, String> {
        lookup_summary(
            name,
            &self.local_types,
            &self.imported.types,
            "wrapper type",
        )
    }

    fn record_entry(&self, name: &str) -> Result<Option<&SummaryEntry<WrapperRecordInfo>>, String> {
        lookup_summary(
            name,
            &self.local_records,
            &self.imported.records,
            "wrapper record",
        )
    }
}

fn insert_local<T: Clone>(
    map: &mut HashMap<String, SummaryEntry<T>>,
    current_module: Option<&str>,
    name: String,
    info: T,
) {
    let canonical = current_module
        .map(|m| format!("{m}.{name}"))
        .unwrap_or_else(|| name.clone());
    let entry = SummaryEntry { canonical, info };
    map.insert(name.clone(), entry.clone());
    if let Some(module) = current_module {
        map.insert(format!("{module}.{name}"), entry);
    }
}

fn lookup_summary<'a, T>(
    name: &str,
    local: &'a HashMap<String, SummaryEntry<T>>,
    imported: &'a HashMap<String, Vec<SummaryEntry<T>>>,
    label: &str,
) -> Result<Option<&'a SummaryEntry<T>>, String> {
    if let Some(entry) = local.get(name) {
        return Ok(Some(entry));
    }
    let Some(entries) = imported.get(name) else {
        return Ok(None);
    };
    match entries.as_slice() {
        [] => Ok(None),
        [entry] => Ok(Some(entry)),
        many => {
            let mut candidates: Vec<String> = many.iter().map(|e| e.canonical.clone()).collect();
            candidates.sort();
            Err(format!(
                "{label} `{name}` is ambiguous; candidates: {}",
                candidates.join(", ")
            ))
        }
    }
}

fn is_hardcoded_derive(bare: &str) -> bool {
    matches!(
        bare,
        "Show" | "Debug" | "Eq" | "Ord" | "Enum" | "Generic" | "Default"
    )
}

fn derive_applied_selectable(
    spec: &DeriveSpec,
    type_name: &str,
    type_params: &[TypeParam],
    span: Span,
    scope: &DeriveScope<'_>,
) -> Result<Vec<Decl>, Diagnostic> {
    let trait_entry = match scope.trait_entry(&spec.trait_name) {
        Ok(Some(entry)) => entry,
        Ok(None) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{}`: trait is not in scope", spec.trait_name),
                span: Some(spec.span),
            });
        }
        Err(reason) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{}`: {reason}", spec.trait_name),
                span: Some(spec.span),
            });
        }
    };
    let trait_info = &trait_entry.info;
    let trait_syntax = trait_entry.canonical.clone();
    let trait_display = spec
        .trait_name
        .rsplit('.')
        .next()
        .unwrap_or(&spec.trait_name);

    if spec.type_args.len() != 1 {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` with {} type arguments; applied derives support exactly one row type",
                spec.type_args.len()
            ),
            span: Some(spec.span),
        });
    }
    let row_type = &spec.type_args[0];
    if !is_supported_applied_row_type(row_type) {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: row argument must be a named type or named type application"
            ),
            span: Some(row_type.span()),
        });
    }
    let row_type = canonicalize_applied_row_type(row_type, scope);
    ensure_row_generic_available(trait_display, &row_type, spec.span, scope)?;
    if trait_info.type_params.len() != 2 || !trait_info.is_functional {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` with a row argument: trait must be a functional two-parameter trait"
            ),
            span: Some(spec.span),
        });
    }

    let self_var = &trait_info.type_params[0].name;
    let row_var = &trait_info.type_params[1].name;
    let mut methods = Vec::new();
    for method in &trait_info.methods {
        if method.default_body.is_some() {
            continue;
        }
        if !is_selectable_shaped_method(method, self_var, row_var) {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!(
                    "cannot derive `{trait_display}` for `{type_name}`: method `{}` must have shape `{self_var} -> {row_var}` with no effects",
                    method.name
                ),
                span: Some(method.span),
            });
        }
        methods.push(method.clone());
    }
    if methods.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for `{type_name}`: every method has a default body, so there is nothing to synthesize"
            ),
            span: Some(spec.span),
        });
    }

    let zero_span = Span { start: 0, end: 0 };
    let source_rep_name = format!("Rep__{type_name}");
    let row_rep_type = rep_type_for_named_type(&row_type).expect("validated row type");
    let row_rep_ctor = row_type
        .head_name()
        .map(rep_name_for_type_head)
        .expect("validated row type");

    let routed_info = RoutedDeriveInfo {
        trait_name: trait_display.to_string(),
        target_type: type_name.to_string(),
        deriving_span: spec.span,
    };

    let bridge_methods = methods
        .iter()
        .map(|method| {
            Annotated::bare(synth_selectable_bridge_method(
                method,
                &source_rep_name,
                &row_rep_ctor,
                span,
            ))
        })
        .collect();
    let bridge_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax.clone(),
        trait_name_span: zero_span,
        trait_type_args: vec![row_rep_type.clone()],
        target_type: source_rep_name,
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: type_params.to_vec(),
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: bridge_methods,
        routed_derive_info: Some(routed_info.clone()),
        span,
        dangling_trivia: vec![],
    };

    let source_rep_var = "__selection_rep".to_string();
    let row_rep_var = "__row_rep".to_string();
    let source_applied = apply_type_params(type_name, type_params);
    let where_apps = vec![
        TraitApp {
            id: NodeId::fresh(),
            trait_name: "Std.Generic.Generic".into(),
            type_args: vec![
                source_applied,
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: source_rep_var.clone(),
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
        TraitApp {
            id: NodeId::fresh(),
            trait_name: "Std.Generic.Generic".into(),
            type_args: vec![
                row_type.clone(),
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: row_rep_var.clone(),
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
        TraitApp {
            id: NodeId::fresh(),
            trait_name: trait_syntax.clone(),
            type_args: vec![
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: source_rep_var,
                    span: zero_span,
                },
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: row_rep_var,
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
    ];
    let delegating_methods = methods
        .iter()
        .map(|method| Annotated::bare(synth_selectable_delegating_method(method, span)))
        .collect();
    let delegating_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax,
        trait_name_span: zero_span,
        trait_type_args: vec![row_type.clone()],
        target_type: type_name.into(),
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: type_params.to_vec(),
        where_clause: vec![],
        where_apps,
        needs: vec![],
        methods: delegating_methods,
        routed_derive_info: Some(routed_info),
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![bridge_impl, delegating_impl])
}

fn ensure_row_generic_available(
    trait_display: &str,
    row_type: &TypeExpr,
    derive_span: Span,
    scope: &DeriveScope<'_>,
) -> Result<(), Diagnostic> {
    let Some(row_head) = row_type.head_name() else {
        return Ok(());
    };
    let rep_head = rep_name_for_type_head(row_head);
    let has_explicit_rep = matches!(scope.type_entry(&rep_head), Ok(Some(_)))
        || matches!(scope.record_entry(&rep_head), Ok(Some(_)));

    match scope.record_entry(row_head) {
        Ok(Some(entry)) if entry.info.derives_generic || has_explicit_rep => return Ok(()),
        Ok(Some(_)) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!(
                    "cannot derive `{trait_display}`: row type `{row_head}` must derive `Generic`"
                ),
                span: Some(derive_span),
            });
        }
        Err(reason) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{trait_display}`: {reason}"),
                span: Some(derive_span),
            });
        }
        Ok(None) => {}
    }

    match scope.type_entry(row_head) {
        Ok(Some(entry)) if entry.info.derives_generic || has_explicit_rep => Ok(()),
        Ok(Some(_)) => Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: row type `{row_head}` must derive `Generic`"
            ),
            span: Some(derive_span),
        }),
        Err(reason) => Err(Diagnostic {
            severity: Severity::Error,
            message: format!("cannot derive `{trait_display}`: {reason}"),
            span: Some(derive_span),
        }),
        Ok(None) => Ok(()),
    }
}

fn canonicalize_applied_row_type(ty: &TypeExpr, scope: &DeriveScope<'_>) -> TypeExpr {
    match ty {
        TypeExpr::Named { id, name, span } => {
            let canonical = scope
                .record_entry(name)
                .ok()
                .flatten()
                .map(|entry| entry.canonical.clone())
                .or_else(|| {
                    scope
                        .type_entry(name)
                        .ok()
                        .flatten()
                        .map(|entry| entry.canonical.clone())
                })
                .unwrap_or_else(|| name.clone());
            TypeExpr::Named {
                id: *id,
                name: canonical,
                span: *span,
            }
        }
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id: *id,
            func: Box::new(canonicalize_applied_row_type(func, scope)),
            arg: Box::new(canonicalize_applied_row_type(arg, scope)),
            span: *span,
        },
        other => other.clone(),
    }
}

fn is_selectable_shaped_method(method: &TraitMethod, self_var: &str, row_var: &str) -> bool {
    method.params.len() == 1
        && method.effects.is_empty()
        && method.effect_row_var.is_empty()
        && matches!(&method.params[0].1, TypeExpr::Var { name, .. } if name == self_var)
        && matches!(&method.return_type, TypeExpr::Var { name, .. } if name == row_var)
}

fn is_supported_applied_row_type(ty: &TypeExpr) -> bool {
    if ty.head_name().is_some_and(|head| head == "Tuple") {
        return false;
    }
    match ty {
        TypeExpr::Named { .. } => true,
        TypeExpr::App { func, arg, .. } => {
            is_supported_applied_row_type(func) && is_supported_applied_row_type(arg)
        }
        _ => false,
    }
}

fn rep_type_for_named_type(ty: &TypeExpr) -> Option<TypeExpr> {
    let zero_span = Span { start: 0, end: 0 };
    match ty {
        TypeExpr::Named { name, .. } => Some(TypeExpr::Named {
            id: NodeId::fresh(),
            name: rep_name_for_type_head(name),
            span: zero_span,
        }),
        TypeExpr::App { func, arg, .. } => Some(TypeExpr::App {
            id: NodeId::fresh(),
            func: Box::new(rep_type_for_named_type(func)?),
            arg: Box::new((**arg).clone()),
            span: zero_span,
        }),
        _ => None,
    }
}

fn rep_name_for_type_head(head: &str) -> String {
    if let Some((module, name)) = head.rsplit_once('.') {
        format!("{module}.Rep__{name}")
    } else {
        format!("Rep__{head}")
    }
}

fn synth_selectable_bridge_method(
    method: &TraitMethod,
    source_rep_name: &str,
    row_rep_ctor: &str,
    span: Span,
) -> ImplMethod {
    let inner = "__inner".to_string();
    let method_call = app_expr(var_expr(&method.name, span), var_expr(&inner, span), span);
    ImplMethod {
        name: method.name.clone(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Constructor {
            id: NodeId::fresh(),
            name: source_rep_name.to_string(),
            args: vec![Pat::Var {
                id: NodeId::fresh(),
                name: inner,
                span,
            }],
            span,
        }],
        body: apply_ctor(row_rep_ctor, method_call, span),
    }
}

fn synth_selectable_delegating_method(method: &TraitMethod, span: Span) -> ImplMethod {
    let value = "__val".to_string();
    let to_call = app_expr(var_expr("to", span), var_expr(&value, span), span);
    let method_call = app_expr(var_expr(&method.name, span), to_call, span);
    let from_call = app_expr(var_expr("from", span), method_call, span);
    ImplMethod {
        name: method.name.clone(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: value,
            span,
        }],
        body: from_call,
    }
}

fn var_expr(name: &str, span: Span) -> Expr {
    Expr::synth(span, ExprKind::Var { name: name.into() })
}

fn app_expr(func: Expr, arg: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(func),
            arg: Box::new(arg),
        },
    )
}

/// Synthesize the delegating impl for a user-defined derivable trait.
/// Shape (per Phase 2d+2e carry-forward, recommendation b):
///
/// ```text
/// impl <Trait> for <T> [where {a: <Trait>, ...}]
///   where {Generic <T-applied> r, <Trait> r}
/// {
///   <method_name> __val = case to __val { Rep__<T> __inner -> <method_name> __inner }
/// }
/// ```
///
/// The `where_apps` form makes the dependency on `Generic` and the routed
/// trait explicit (better diagnostics at registration). The per-tparam old-form
/// `where_clause` entries are required so the impl-body inference can satisfy
/// `<Trait> a` constraints that bubble up from the Rep__T building-block
/// instances at use time.
fn derive_routed(
    trait_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    span: Span,
    scope: &DeriveScope<'_>,
) -> Result<Vec<Decl>, Diagnostic> {
    let trait_entry = match scope.trait_entry(trait_name) {
        Ok(Some(entry)) => entry,
        Ok(None) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{trait_name}`: trait is not in scope"),
                span: Some(span),
            });
        }
        Err(reason) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{trait_name}`: {reason}"),
                span: Some(span),
            });
        }
    };
    let trait_info = &trait_entry.info;
    let trait_syntax = trait_entry.canonical.clone();
    let trait_display = trait_name.rsplit('.').next().unwrap_or(trait_name);

    if trait_info.methods.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for `{type_name}`: trait `{trait_display}` has no methods to route"
            ),
            span: Some(span),
        });
    }
    let self_var: String = trait_info
        .type_params
        .first()
        .map(|tp| tp.name.clone())
        .unwrap_or_default();

    // Classify each method's direction up-front so any bad method kills the
    // whole derive before we synthesize anything partial. Methods that carry
    // a default body in the trait declaration are skipped here — impl-checking
    // will splice in the cloned default, which lets library authors mark a
    // method as "convenience wrapper over the routed one" without forcing the
    // synthesizer to invent a body for it.
    let mut classified: Vec<(TraitMethod, MethodDirection)> =
        Vec::with_capacity(trait_info.methods.len());
    for method in &trait_info.methods {
        if method.default_body.is_some() {
            continue;
        }
        match classify_method_direction(method, &self_var, scope) {
            Ok(dir) => classified.push((method.clone(), dir)),
            Err(reason) => {
                return Err(Diagnostic {
                    severity: Severity::Error,
                    message: format!("cannot derive `{trait_display}` for `{type_name}`: {reason}"),
                    span: Some(span),
                });
            }
        }
    }
    if classified.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for `{type_name}`: every method in trait \
                 `{trait_display}` has a default body, so there is nothing to synthesize"
            ),
            span: Some(span),
        });
    }

    let rep_name = format!("Rep__{type_name}");
    let zero_span = Span { start: 0, end: 0 };

    // Per-tparam old-form bounds: `where {a: <Trait>, ...}`. Required so the
    // bridge impl's body and the delegating impl's body can satisfy the
    // `<Trait> a` constraints that bubble up from the Rep building-block
    // impls (e.g. `Leaf a where {a: <Trait>}`).
    let per_tparam_where: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_syntax.clone(),
                type_args: vec![],
                span: zero_span,
            }],
        })
        .collect();

    // Per-method bodies for the bridge impl (target = Rep__T). Each method is
    // synthesized independently; a single impl carries one ImplMethod entry
    // per trait method.
    let mut bridge_methods: Vec<Annotated<ImplMethod>> = Vec::with_capacity(classified.len());
    let mut delegating_methods: Vec<Annotated<ImplMethod>> = Vec::with_capacity(classified.len());
    for (method, dir) in &classified {
        let (bridge_m, deleg_m) = synth_method_pair(method, dir, &rep_name, span);
        bridge_methods.push(Annotated::bare(bridge_m));
        delegating_methods.push(Annotated::bare(deleg_m));
    }

    let routed_info = RoutedDeriveInfo {
        trait_name: trait_display.to_string(),
        target_type: type_name.to_string(),
        deriving_span: span,
    };
    let bridge_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax.clone(),
        trait_name_span: zero_span,
        trait_type_args: vec![],
        target_type: rep_name.clone(),
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: type_params.to_vec(),
        where_clause: per_tparam_where.clone(),
        where_apps: vec![],
        needs: vec![],
        methods: bridge_methods,
        routed_derive_info: Some(routed_info.clone()),
        span,
        dangling_trivia: vec![],
    };

    let fresh_r = "__r".to_string();
    let target_applied = apply_type_params(type_name, type_params);
    let where_apps = vec![
        TraitApp {
            id: NodeId::fresh(),
            trait_name: "Std.Generic.Generic".into(),
            type_args: vec![
                target_applied,
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: fresh_r.clone(),
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
        TraitApp {
            id: NodeId::fresh(),
            trait_name: trait_syntax.clone(),
            type_args: vec![TypeExpr::Var {
                id: NodeId::fresh(),
                name: fresh_r,
                span: zero_span,
            }],
            span: zero_span,
        },
    ];
    let delegating_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax,
        trait_name_span: zero_span,
        trait_type_args: vec![],
        target_type: type_name.into(),
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: type_params.to_vec(),
        where_clause: per_tparam_where,
        where_apps,
        needs: vec![],
        methods: delegating_methods,
        routed_derive_info: Some(routed_info),
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![bridge_impl, delegating_impl])
}

/// Direction of a single routed-derive method. `To` carries a per-parameter
/// flag vector identifying which params are `a`-typed (need `to`/Rep__T
/// wrapping) vs. passthrough. `From` carries a `FromShape` describing the
/// wrapper structurally.
#[derive(Clone)]
enum MethodDirection {
    To { a_params: Vec<Option<SplicePath>> },
    From(FromShape),
}

/// Validate a method's shape for routed deriving and decide which direction it
/// runs. Returns a human-readable reason on failure for use in the surrounding
/// diagnostic.
///
/// To-direction supports any number of parameters: each parameter must either
/// be exactly the trait's self variable (an `a`-param — wrapped via `to` /
/// destructured from `Rep__T`) or contain no occurrence of the self variable
/// at all (a passthrough param). Nested self (e.g. `List a`) is rejected.
fn classify_method_direction(
    method: &TraitMethod,
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<MethodDirection, String> {
    let return_has_self = type_expr_contains_var(&method.return_type, self_var);

    let mut a_params: Vec<Option<SplicePath>> = Vec::with_capacity(method.params.len());
    let mut any_param_has_self = false;
    for (_label, ty) in &method.params {
        let mut visiting = Vec::new();
        match classify_splice_path(ty, self_var, scope, &mut visiting) {
            Ok(path) => {
                if path.is_some() {
                    any_param_has_self = true;
                }
                a_params.push(path);
            }
            Err(reason) => {
                return Err(format!("method `{}` parameter: {}", method.name, reason));
            }
        }
    }

    match (any_param_has_self, return_has_self) {
        (true, false) => Ok(MethodDirection::To { a_params }),
        (false, true) => match classify_from_return(&method.return_type, self_var, scope) {
            Ok(shape) => Ok(MethodDirection::From(shape)),
            Err(reason) => Err(format!("method `{}`: {}", method.name, reason)),
        },
        (true, true) => Err(format!(
            "method `{}` has the self type on both sides; \
             routed deriving cannot infer a direction (consider splitting the trait)",
            method.name
        )),
        (false, false) => Err(format!(
            "method `{}` does not consume or produce a value of the self type",
            method.name
        )),
    }
}

/// Build the bridge-impl ImplMethod and delegating-impl ImplMethod for a
/// single trait method.
fn synth_method_pair(
    method: &TraitMethod,
    dir: &MethodDirection,
    rep_name: &str,
    span: Span,
) -> (ImplMethod, ImplMethod) {
    let zero_span = Span { start: 0, end: 0 };
    let method_name = method.name.clone();
    match dir {
        MethodDirection::To { a_params } => {
            // Bridge:    method (Rep__T i0) (Rep__T i1) p2 = method i0 i1 p2
            // Delegate:  method p0 p1 p2                   = method (to p0) (to p1) p2
            // For each param:
            //   - splice param (path is Some): the bridge destructures `Rep__T`
            //     at every a-leaf (via `build_splice_pattern`) and forwards the
            //     rebuilt product; the delegate binds the whole param and threads
            //     `to` into each a-leaf (via `apply_splice_path`). A bare-`a` param
            //     is the `Leaf` case of both — `(Rep__T __i)` / `to __p`.
            //   - passthrough (path is None): bridge & delegate both bind __p<k>
            //     and forward it unchanged.
            let n = a_params.len();
            let mut bridge_params: Vec<Pat> = Vec::with_capacity(n);
            let mut bridge_args: Vec<Expr> = Vec::with_capacity(n);
            let mut deleg_params: Vec<Pat> = Vec::with_capacity(n);
            let mut deleg_args: Vec<Expr> = Vec::with_capacity(n);
            let to_op = |e: Expr, s: Span| -> Expr {
                Expr::synth(
                    s,
                    ExprKind::App {
                        func: Box::new(Expr::synth(s, ExprKind::Var { name: "to".into() })),
                        arg: Box::new(e),
                    },
                )
            };
            let mut bridge_counter = 0usize;
            for (i, path) in a_params.iter().enumerate() {
                let param_var = format!("__p{i}");
                match path {
                    Some(p) => {
                        let (bpat, barg) =
                            build_splice_pattern(p, rep_name, &mut bridge_counter, span);
                        bridge_params.push(bpat);
                        bridge_args.push(barg);
                        deleg_params.push(Pat::Var {
                            id: NodeId::fresh(),
                            name: param_var.clone(),
                            span,
                        });
                        let arg = Expr::synth(span, ExprKind::Var { name: param_var });
                        deleg_args.push(apply_splice_path(p, arg, &to_op, span));
                    }
                    None => {
                        bridge_params.push(Pat::Var {
                            id: NodeId::fresh(),
                            name: param_var.clone(),
                            span,
                        });
                        bridge_args.push(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: param_var.clone(),
                            },
                        ));
                        deleg_params.push(Pat::Var {
                            id: NodeId::fresh(),
                            name: param_var.clone(),
                            span,
                        });
                        deleg_args.push(Expr::synth(span, ExprKind::Var { name: param_var }));
                    }
                }
            }
            let method_name_for_call = method_name.clone();
            let build_call = |args: Vec<Expr>| -> Expr {
                let mut acc = Expr::synth(
                    span,
                    ExprKind::Var {
                        name: method_name_for_call.clone(),
                    },
                );
                for arg in args {
                    acc = Expr::synth(
                        span,
                        ExprKind::App {
                            func: Box::new(acc),
                            arg: Box::new(arg),
                        },
                    );
                }
                acc
            };
            let bridge = ImplMethod {
                name: method_name.clone(),
                name_span: zero_span,
                params: bridge_params,
                body: build_call(bridge_args),
            };
            let deleg = ImplMethod {
                name: method_name,
                name_span: zero_span,
                params: deleg_params,
                body: build_call(deleg_args),
            };
            (bridge, deleg)
        }
        MethodDirection::From(shape) => {
            // All params are passthrough in from-direction (the a appears only
            // in the return). Bind each as `__p<i>` and forward all of them to
            // the recursive method call inside the case scrutinee.
            let input_vars: Vec<String> = (0..method.params.len())
                .map(|i| format!("__p{i}"))
                .collect();
            let build_params = || -> Vec<Pat> {
                input_vars
                    .iter()
                    .map(|n| Pat::Var {
                        id: NodeId::fresh(),
                        name: n.clone(),
                        span,
                    })
                    .collect()
            };

            let rep_name_owned = rep_name.to_string();
            let bridge_wrap = |inner: Expr, s: Span| apply_ctor(&rep_name_owned, inner, s);
            let bridge_body = build_from_body(&method_name, &input_vars, &bridge_wrap, shape, span);
            let bridge = ImplMethod {
                name: method_name.clone(),
                name_span: zero_span,
                params: build_params(),
                body: bridge_body,
            };

            let deleg_wrap = |inner: Expr, s: Span| {
                Expr::synth(
                    s,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            s,
                            ExprKind::Var {
                                name: "from".into(),
                            },
                        )),
                        arg: Box::new(inner),
                    },
                )
            };
            let deleg_body = build_from_body(&method_name, &input_vars, &deleg_wrap, shape, span);
            let deleg = ImplMethod {
                name: method_name,
                name_span: zero_span,
                params: build_params(),
                body: deleg_body,
            };
            (bridge, deleg)
        }
    }
}

/// Structural description of a from-direction method's return wrapper. The
/// general shape is: either bare `a`, or a sum/record wrapper where every
/// `a` position has been located by walking the wrapper's variants/fields
/// against the trait's self type variable. Per-variant a-position bits drive
/// codegen — `build_from_body` reads this and threads `wrap` through each
/// marked position while passing other positions through unchanged.
#[derive(Clone)]
enum FromShape {
    Bare,
    Sum {
        variants: Vec<VariantShape>,
    },
    Record {
        wrapper_name: String,
        fields: Vec<FieldShape>,
    },
}

#[derive(Clone)]
struct VariantShape {
    ctor_name: String,
    /// One entry per field; `None` = no `a` (passthrough), `Some(path)` =
    /// the field's type carries `a` at the leaves the path locates; apply
    /// `wrap` there (under wrapper-self-param substitution).
    field_a_positions: Vec<Option<SplicePath>>,
}

#[derive(Clone)]
struct FieldShape {
    label: String,
    /// `None` = passthrough, `Some(path)` = splice `a` at the path's leaves.
    path: Option<SplicePath>,
}

/// A lens locating every occurrence of the trait's self type `a` inside a
/// (possibly nested) product type, so codegen can splice the `Generic` iso
/// (`to`/`from`/`Rep__T`) at each `a`-leaf rather than around the whole value.
///
/// `Leaf` is the base case (the value *is* `a`); `Tuple`/`Record` recurse into
/// product positions. `a` nested under a sum or a parametric/recursive
/// container (`List a`, custom sums, self-referential records) is *not*
/// representable here — `classify_splice_path` rejects those with a diagnostic.
#[derive(Clone)]
enum SplicePath {
    /// The value at this position is exactly `a`.
    Leaf,
    /// `(T0, T1, ...)` — per-element path (`None` = element has no `a`).
    Tuple(Vec<Option<SplicePath>>),
    /// A named record `Name { f0: .., f1: .. }` — per-field path.
    Record {
        name: String,
        fields: Vec<(String, Option<SplicePath>)>,
    },
}

/// Classify a from-direction method's return type by structural inspection.
/// Walks the trait method's return TypeExpr to find the wrapper head and its
/// type args, looks the wrapper up in the merged local+imported decl tables,
/// then walks the wrapper's variants/fields to mark which positions carry the
/// trait's self type variable. Returns `Err(reason)` for the various cases
/// the synthesizer can't handle: opaque wrapper, no `a`-position anywhere,
/// or nested `a` (e.g. `Yep (List a)` — would require recursing through the
/// `List` Generic representation, deferred).
fn classify_from_return(
    te: &TypeExpr,
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<FromShape, String> {
    // Bare `a`: the trait's self type variable as the entire return.
    if let TypeExpr::Var { name, .. } = te
        && name == self_var
    {
        return Ok(FromShape::Bare);
    }

    // Otherwise expect a (possibly multi-arg) type application headed by a
    // Named wrapper. Extract head name and the left-to-right args.
    let (head, args) = extract_head_and_args(te).ok_or_else(|| {
        "return type must be either the trait's self variable or a named wrapper applied \
             to type arguments"
            .to_string()
    })?;

    // The wrapper's call-site args may now nest `a` inside a product (e.g.
    // `Result (a, Int) String`). The per-field substitution in
    // `classify_sum_wrapper`/`classify_record_wrapper` feeds each such arg
    // through `classify_splice_path`, which rejects non-product nesting
    // (`Result (List a) String`) with a diagnostic. So no up-front arg check
    // is needed here.

    // Look up the wrapper. Sum (TypeDef) first, then record (RecordDef).
    match scope.type_entry(&head) {
        Ok(Some(td)) => {
            return classify_sum_wrapper(&head, &td.info, &args, self_var, scope);
        }
        Ok(None) => {}
        Err(reason) => return Err(reason),
    }
    match scope.record_entry(&head) {
        Ok(Some(rd)) => {
            return classify_record_wrapper(&head, &rd.info, &args, self_var, scope);
        }
        Ok(None) => {}
        Err(reason) => return Err(reason),
    }
    Err(format!(
        "wrapper type `{}` is not defined in the current module or any imported module; \
         routed from-derives need the wrapper's TypeDef in scope so they can inspect its \
         variants",
        head
    ))
}

/// Extract the bare head name and left-to-right type arguments from a
/// possibly-applied TypeExpr. Returns None if the TypeExpr isn't a named
/// type or a chain of applications headed by one.
fn extract_head_and_args(te: &TypeExpr) -> Option<(String, Vec<TypeExpr>)> {
    match te {
        TypeExpr::Named { name, .. } => Some((name.clone(), vec![])),
        TypeExpr::App { func, arg, .. } => {
            let (head, mut args) = extract_head_and_args(func)?;
            args.push(arg.as_ref().clone());
            Some((head, args))
        }
        _ => None,
    }
}

fn is_self_var(te: &TypeExpr, self_var: &str) -> bool {
    matches!(te, TypeExpr::Var { name, .. } if name == self_var)
}

/// Walk a sum wrapper's declared variants and identify a-positions. The
/// wrapper's local type params that bind to the trait's self at the call
/// site form `wrapper_self_params`; any variant field whose TypeExpr is
/// exactly `Var(p)` for some `p` in that set is an a-position. A field that
/// CONTAINS such a `p` but isn't directly that `Var` (e.g. `List a`,
/// `Foo a Int`) is the nested-a case and we reject.
fn classify_sum_wrapper(
    name: &str,
    td: &WrapperTypeInfo,
    call_args: &[TypeExpr],
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<FromShape, String> {
    if call_args.len() != td.type_params.len() {
        return Err(format!(
            "wrapper `{}` declares {} type parameter(s) but is applied to {}",
            name,
            td.type_params.len(),
            call_args.len()
        ));
    }
    if !call_args
        .iter()
        .any(|a| type_expr_contains_var(a, self_var))
    {
        return Err(format!(
            "wrapper `{}` doesn't carry the trait's self type at any type-argument position",
            name
        ));
    }
    let subst = param_subst(&td.type_params, call_args);

    let mut variants = Vec::with_capacity(td.variants.len());
    let mut any_a_position = false;
    let ctor_prefix = name.rsplit_once('.').map(|(module, _)| module.to_string());
    for variant in &td.variants {
        let mut field_a_positions = Vec::with_capacity(variant.fields.len());
        for (_label, fty) in &variant.fields {
            let resolved = subst_type_params(fty, &subst);
            let mut visiting = Vec::new();
            let path = classify_splice_path(&resolved, self_var, scope, &mut visiting).map_err(
                |reason| format!("wrapper `{}` variant `{}`: {}", name, variant.name, reason),
            )?;
            if path.is_some() {
                any_a_position = true;
            }
            field_a_positions.push(path);
        }
        variants.push(VariantShape {
            ctor_name: ctor_prefix
                .as_ref()
                .map(|prefix| format!("{prefix}.{}", variant.name))
                .unwrap_or_else(|| variant.name.clone()),
            field_a_positions,
        });
    }
    if !any_a_position {
        return Err(format!(
            "wrapper `{}` has no variant field carrying the trait's self type — nothing for \
             `from` to thread through",
            name
        ));
    }
    Ok(FromShape::Sum { variants })
}

fn classify_record_wrapper(
    name: &str,
    rd: &WrapperRecordInfo,
    call_args: &[TypeExpr],
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<FromShape, String> {
    if call_args.len() != rd.type_params.len() {
        return Err(format!(
            "wrapper `{}` declares {} type parameter(s) but is applied to {}",
            name,
            rd.type_params.len(),
            call_args.len()
        ));
    }
    if !call_args
        .iter()
        .any(|a| type_expr_contains_var(a, self_var))
    {
        return Err(format!(
            "wrapper record `{}` doesn't carry the trait's self type at any type-argument \
             position",
            name
        ));
    }
    let subst = param_subst(&rd.type_params, call_args);
    let mut fields = Vec::with_capacity(rd.fields.len());
    let mut any_a_position = false;
    for (label, fty) in &rd.fields {
        let resolved = subst_type_params(fty, &subst);
        let mut visiting = Vec::new();
        let path = classify_splice_path(&resolved, self_var, scope, &mut visiting)
            .map_err(|reason| format!("wrapper record `{}` field `{}`: {}", name, label, reason))?;
        if path.is_some() {
            any_a_position = true;
        }
        fields.push(FieldShape {
            label: label.clone(),
            path,
        });
    }
    if !any_a_position {
        return Err(format!(
            "wrapper record `{}` has no field carrying the trait's self type — nothing for \
             `from` to thread through",
            name
        ));
    }
    Ok(FromShape::Record {
        wrapper_name: name.to_string(),
        fields,
    })
}

/// Build a `[(param_name, call_arg)]` substitution pairing a wrapper's declared
/// type parameters with the type arguments it's applied to at the call site.
fn param_subst(type_params: &[TypeParam], call_args: &[TypeExpr]) -> Vec<(String, TypeExpr)> {
    type_params
        .iter()
        .map(|p| p.name.clone())
        .zip(call_args.iter().cloned())
        .collect()
}

/// Substitute type-parameter variables in `te` according to `subst`. Used to
/// resolve a wrapper's declared field types against the call-site type
/// arguments before locating the trait's self type within them. The cloned
/// TypeExpr is only ever inspected (never spliced into the AST), so reusing the
/// original NodeIds is harmless.
fn subst_type_params(te: &TypeExpr, subst: &[(String, TypeExpr)]) -> TypeExpr {
    match te {
        TypeExpr::Var { name, .. } => subst
            .iter()
            .find(|(p, _)| p == name)
            .map(|(_, replacement)| replacement.clone())
            .unwrap_or_else(|| te.clone()),
        TypeExpr::Named { .. } | TypeExpr::Symbol { .. } => te.clone(),
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id: *id,
            func: Box::new(subst_type_params(func, subst)),
            arg: Box::new(subst_type_params(arg, subst)),
            span: *span,
        },
        TypeExpr::Arrow {
            id,
            from,
            to,
            effects,
            effect_row_var,
            span,
        } => TypeExpr::Arrow {
            id: *id,
            from: Box::new(subst_type_params(from, subst)),
            to: Box::new(subst_type_params(to, subst)),
            effects: effects.clone(),
            effect_row_var: effect_row_var.clone(),
            span: *span,
        },
        TypeExpr::Record {
            id,
            fields,
            multiline,
            span,
        } => TypeExpr::Record {
            id: *id,
            fields: fields
                .iter()
                .map(|(l, t)| (l.clone(), subst_type_params(t, subst)))
                .collect(),
            multiline: *multiline,
            span: *span,
        },
        TypeExpr::Labeled {
            id,
            label,
            inner,
            span,
        } => TypeExpr::Labeled {
            id: *id,
            label: label.clone(),
            inner: Box::new(subst_type_params(inner, subst)),
            span: *span,
        },
    }
}

/// Locate every occurrence of the trait's self type `a` inside `te` as a
/// `SplicePath`, or return:
/// - `Ok(None)` — `te` doesn't mention `a` (a passthrough position)
/// - `Ok(Some(path))` — `a` sits at the leaves the path locates (products only)
/// - `Err(reason)` — `a` is nested under a non-product (sum / `List a` / arrow /
///   anonymous record) or a recursive type
///
/// `visiting` carries the canonical names of named records currently being
/// expanded, so a self-referential record is rejected rather than looped.
fn classify_splice_path(
    te: &TypeExpr,
    self_var: &str,
    scope: &DeriveScope<'_>,
    visiting: &mut Vec<String>,
) -> Result<Option<SplicePath>, String> {
    // Bare `a`.
    if is_self_var(te, self_var) {
        return Ok(Some(SplicePath::Leaf));
    }
    // No occurrence anywhere — passthrough.
    if !type_expr_contains_var(te, self_var) {
        return Ok(None);
    }

    // `a` occurs nested. Only products (tuples / named records) are spliceable.
    let (head, args) = extract_head_and_args(te).ok_or_else(|| {
        "the trait's self type is nested in a non-leaf position that routed deriving cannot \
         splice through; only `a` inside tuples and records is supported"
            .to_string()
    })?;

    // Tuple `(T0, T1, ...)` — recurse per element.
    if head == "Tuple" {
        let mut elems = Vec::with_capacity(args.len());
        for arg in &args {
            elems.push(classify_splice_path(arg, self_var, scope, visiting)?);
        }
        return Ok(Some(SplicePath::Tuple(elems)));
    }

    // Named record — recurse into its fields, guarding against recursion.
    if let Some(rd) = scope.record_entry(&head)? {
        let canonical = rd.canonical.clone();
        if visiting.contains(&canonical) {
            return Err(format!(
                "the trait's self type is nested in a non-leaf position inside recursive record \
                 `{}`; routed deriving cannot splice through a recursive type",
                head
            ));
        }
        let info = &rd.info;
        if args.len() != info.type_params.len() {
            return Err(format!(
                "record `{}` declares {} type parameter(s) but is applied to {}",
                head,
                info.type_params.len(),
                args.len()
            ));
        }
        let subst = param_subst(&info.type_params, &args);
        visiting.push(canonical);
        let mut fields = Vec::with_capacity(info.fields.len());
        for (label, fty) in &info.fields {
            let resolved = subst_type_params(fty, &subst);
            let sub = classify_splice_path(&resolved, self_var, scope, visiting)?;
            fields.push((label.clone(), sub));
        }
        visiting.pop();
        return Ok(Some(SplicePath::Record {
            name: head.clone(),
            fields,
        }));
    }

    // Sum types, `List a`, arrows, anonymous records: not a product we can
    // structurally rebuild. The phrasing keeps "nested in a non-leaf" so callers
    // (and the existing diagnostics/tests) read consistently.
    Err(format!(
        "the trait's self type is nested in a non-leaf position under `{}`, which is not a \
         product type; routed deriving can only splice through tuples and records",
        head
    ))
}

/// Transform a value expression by applying `leaf_op` (the `Generic` iso —
/// `to`/`from`/`Rep__T`) at every `a`-leaf the path locates. Products are
/// destructured with a single-arm `case` and rebuilt, threading `leaf_op` into
/// marked positions and passing the rest through unchanged.
fn apply_splice_path(
    path: &SplicePath,
    value: Expr,
    leaf_op: &dyn Fn(Expr, Span) -> Expr,
    span: Span,
) -> Expr {
    match path {
        SplicePath::Leaf => leaf_op(value, span),
        SplicePath::Tuple(elems) => {
            let vars: Vec<String> = (0..elems.len()).map(|i| format!("__t{i}")).collect();
            let pat = Pat::Tuple {
                id: NodeId::fresh(),
                elements: vars
                    .iter()
                    .map(|n| Pat::Var {
                        id: NodeId::fresh(),
                        name: n.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let rebuilt: Vec<Expr> = elems
                .iter()
                .enumerate()
                .map(|(i, sub)| {
                    let v = Expr::synth(
                        span,
                        ExprKind::Var {
                            name: vars[i].clone(),
                        },
                    );
                    match sub {
                        Some(p) => apply_splice_path(p, v, leaf_op, span),
                        None => v,
                    }
                })
                .collect();
            let body = Expr::synth(span, ExprKind::Tuple { elements: rebuilt });
            single_arm_case(value, pat, body, span)
        }
        SplicePath::Record { name, fields } => {
            let zero_span = Span { start: 0, end: 0 };
            let pat = Pat::Record {
                id: NodeId::fresh(),
                name: name.clone(),
                fields: fields.iter().map(|(l, _)| (l.clone(), None)).collect(),
                rest: false,
                as_name: None,
                span,
            };
            let body_fields: Vec<(String, Span, Expr)> = fields
                .iter()
                .map(|(label, sub)| {
                    let v = Expr::synth(
                        span,
                        ExprKind::Var {
                            name: label.clone(),
                        },
                    );
                    let value = match sub {
                        Some(p) => apply_splice_path(p, v, leaf_op, span),
                        None => v,
                    };
                    (label.clone(), zero_span, value)
                })
                .collect();
            let body = Expr::synth(
                span,
                ExprKind::RecordCreate {
                    name: name.clone(),
                    fields: body_fields,
                },
            );
            single_arm_case(value, pat, body, span)
        }
    }
}

fn single_arm_case(scrutinee: Expr, pattern: Pat, body: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            arms: vec![Annotated::bare(CaseArm {
                pattern,
                guard: None,
                body,
                span,
            })],
            dangling_trivia: vec![],
        },
    )
}

/// Build a destructuring pattern + matching rebuild expression for the
/// To-direction *bridge*, which unwraps `Rep__T` at each `a`-leaf in the
/// pattern (rather than via an expression). The bridge binds inner structural
/// values at the leaves and passthrough vars elsewhere, then reassembles the
/// product to forward to the recursive method call. `counter` makes every bound
/// variable unique across the whole parameter list.
fn build_splice_pattern(
    path: &SplicePath,
    rep_name: &str,
    counter: &mut usize,
    span: Span,
) -> (Pat, Expr) {
    match path {
        SplicePath::Leaf => {
            let inner = format!("__i{}", *counter);
            *counter += 1;
            let pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: rep_name.to_string(),
                args: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: inner.clone(),
                    span,
                }],
                span,
            };
            (pat, Expr::synth(span, ExprKind::Var { name: inner }))
        }
        SplicePath::Tuple(elems) => {
            let mut pats = Vec::with_capacity(elems.len());
            let mut exprs = Vec::with_capacity(elems.len());
            for sub in elems {
                let (p, e) = build_splice_pattern_field(sub, rep_name, counter, span);
                pats.push(p);
                exprs.push(e);
            }
            (
                Pat::Tuple {
                    id: NodeId::fresh(),
                    elements: pats,
                    span,
                },
                Expr::synth(span, ExprKind::Tuple { elements: exprs }),
            )
        }
        SplicePath::Record { name, fields } => {
            let zero_span = Span { start: 0, end: 0 };
            let mut pat_fields = Vec::with_capacity(fields.len());
            let mut expr_fields = Vec::with_capacity(fields.len());
            for (label, sub) in fields {
                match sub {
                    Some(p) => {
                        let (pp, ee) = build_splice_pattern(p, rep_name, counter, span);
                        pat_fields.push((label.clone(), Some(pp)));
                        expr_fields.push((label.clone(), zero_span, ee));
                    }
                    None => {
                        pat_fields.push((label.clone(), None));
                        expr_fields.push((
                            label.clone(),
                            zero_span,
                            Expr::synth(
                                span,
                                ExprKind::Var {
                                    name: label.clone(),
                                },
                            ),
                        ));
                    }
                }
            }
            (
                Pat::Record {
                    id: NodeId::fresh(),
                    name: name.clone(),
                    fields: pat_fields,
                    rest: false,
                    as_name: None,
                    span,
                },
                Expr::synth(
                    span,
                    ExprKind::RecordCreate {
                        name: name.clone(),
                        fields: expr_fields,
                    },
                ),
            )
        }
    }
}

/// A single product element/field for the To-bridge: either recurse (it carries
/// `a`) or bind a fresh passthrough var.
fn build_splice_pattern_field(
    sub: &Option<SplicePath>,
    rep_name: &str,
    counter: &mut usize,
    span: Span,
) -> (Pat, Expr) {
    match sub {
        Some(p) => build_splice_pattern(p, rep_name, counter, span),
        None => {
            let v = format!("__p{}", *counter);
            *counter += 1;
            (
                Pat::Var {
                    id: NodeId::fresh(),
                    name: v.clone(),
                    span,
                },
                Expr::synth(span, ExprKind::Var { name: v }),
            )
        }
    }
}

/// Build the body of a from-direction method. The body has the shape
/// `case method input { <reconstruction arms> }` where each arm matches one
/// wrapper variant (or destructures the single record), rebinds its fields,
/// and reconstructs the wrapper applying `wrap` at each a-position.
fn build_from_body(
    method_name: &str,
    input_vars: &[String],
    wrap: &dyn Fn(Expr, Span) -> Expr,
    shape: &FromShape,
    span: Span,
) -> Expr {
    // `method __p0 __p1 ...` — recursive call forwards every input through
    // the dictionary to the next instance in the chain.
    let mut inner_call = Expr::synth(
        span,
        ExprKind::Var {
            name: method_name.into(),
        },
    );
    for iv in input_vars {
        inner_call = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(inner_call),
                arg: Box::new(Expr::synth(span, ExprKind::Var { name: iv.clone() })),
            },
        );
    }
    match shape {
        FromShape::Bare => wrap(inner_call, span),
        FromShape::Sum { variants, .. } => {
            let arms: Vec<Annotated<CaseArm>> = variants
                .iter()
                .map(|v| Annotated::bare(build_variant_arm(v, wrap, span)))
                .collect();
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(inner_call),
                    arms,
                    dangling_trivia: vec![],
                },
            )
        }
        FromShape::Record {
            wrapper_name,
            fields,
        } => {
            let arm = build_record_arm(wrapper_name, fields, wrap, span);
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(inner_call),
                    arms: vec![Annotated::bare(arm)],
                    dangling_trivia: vec![],
                },
            )
        }
    }
}

/// One case arm reconstructing a single variant. Zero-field variants
/// destructure-and-reconstruct trivially; multi-field variants bind each
/// field to `__f<i>` and rebuild via positional constructor application,
/// applying `wrap` at marked a-positions.
fn build_variant_arm(v: &VariantShape, wrap: &dyn Fn(Expr, Span) -> Expr, span: Span) -> CaseArm {
    let field_vars: Vec<String> = (0..v.field_a_positions.len())
        .map(|i| format!("__f{i}"))
        .collect();
    let pat = Pat::Constructor {
        id: NodeId::fresh(),
        name: v.ctor_name.clone(),
        args: field_vars
            .iter()
            .map(|n| Pat::Var {
                id: NodeId::fresh(),
                name: n.clone(),
                span,
            })
            .collect(),
        span,
    };
    let mut body = Expr::synth(
        span,
        ExprKind::Constructor {
            name: v.ctor_name.clone(),
        },
    );
    for (i, path) in v.field_a_positions.iter().enumerate() {
        let arg = Expr::synth(
            span,
            ExprKind::Var {
                name: field_vars[i].clone(),
            },
        );
        let arg = match path {
            Some(p) => apply_splice_path(p, arg, wrap, span),
            None => arg,
        };
        body = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(body),
                arg: Box::new(arg),
            },
        );
    }
    CaseArm {
        pattern: pat,
        guard: None,
        body,
        span,
    }
}

/// One case arm destructuring a record wrapper. Pattern is
/// `Wrap { f1, f2, ... }`, body reconstructs via `Wrap { f1: wrap?(f1), ... }`.
fn build_record_arm(
    wrapper_name: &str,
    fields: &[FieldShape],
    wrap: &dyn Fn(Expr, Span) -> Expr,
    span: Span,
) -> CaseArm {
    let zero_span = Span { start: 0, end: 0 };
    let pat = Pat::Record {
        id: NodeId::fresh(),
        name: wrapper_name.to_string(),
        fields: fields.iter().map(|f| (f.label.clone(), None)).collect(),
        rest: false,
        as_name: None,
        span,
    };
    let body_fields: Vec<(String, Span, Expr)> = fields
        .iter()
        .map(|f| {
            let var_expr = Expr::synth(
                span,
                ExprKind::Var {
                    name: f.label.clone(),
                },
            );
            let value = match &f.path {
                Some(p) => apply_splice_path(p, var_expr, wrap, span),
                None => var_expr,
            };
            (f.label.clone(), zero_span, value)
        })
        .collect();
    let body = Expr::synth(
        span,
        ExprKind::RecordCreate {
            name: wrapper_name.to_string(),
            fields: body_fields,
        },
    );
    CaseArm {
        pattern: pat,
        guard: None,
        body,
        span,
    }
}

fn type_expr_contains_var(te: &TypeExpr, name: &str) -> bool {
    match te {
        TypeExpr::Var { name: n, .. } => n == name,
        TypeExpr::Named { .. } | TypeExpr::Symbol { .. } => false,
        TypeExpr::App { func, arg, .. } => {
            type_expr_contains_var(func, name) || type_expr_contains_var(arg, name)
        }
        TypeExpr::Arrow { from, to, .. } => {
            type_expr_contains_var(from, name) || type_expr_contains_var(to, name)
        }
        TypeExpr::Record { fields, .. } => {
            fields.iter().any(|(_, t)| type_expr_contains_var(t, name))
        }
        TypeExpr::Labeled { inner, .. } => type_expr_contains_var(inner, name),
    }
}

/// Returns the decls to splice into the program, or:
///   - `Err(None)` for "unsupported trait, use the default cannot-derive error"
///   - `Err(Some(diag))` for a specific diagnostic
fn generate_record_derive(
    public: bool,
    trait_name: &str,
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
    match bare {
        "Show" | "Debug" => Ok(vec![derive_record_stringify(
            bare,
            if bare == "Show" { "show" } else { "debug" },
            record_name,
            type_params,
            fields,
            span,
        )]),
        "Eq" => Ok(vec![derive_marker_trait(
            "Eq",
            record_name,
            type_params,
            span,
        )]),
        "Default" => Ok(vec![derive_record_default(
            record_name,
            type_params,
            fields,
            span,
        )]),
        "Generic" => derive_record_generic(public, record_name, type_params, fields, span),
        _ => Err(None),
    }
}

/// Build `type Rep__R = Rep__R <inner-rep>` + `impl Generic R (Rep__R) { to, from }`.
/// Handles parameterized and recursive records: the Rep type carries the same
/// type parameters as the user record, and field types referencing the user
/// type round-trip naturally through the runtime dictionary (no special
/// recursion handling in the Rep shape).
fn derive_record_generic(
    public: bool,
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    // Naming: use a leading uppercase letter so the lexer classifies the
    // name as an UpperIdent (type/constructor). The planning doc proposed
    // `__Rep_<R>` but a leading `_` lexes as lowercase, which would break
    // user-written ascriptions like `(to p : __Rep_Person)`.
    let rep_name = format!("Rep__{record_name}");
    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();

    // 1. Synthetic TypeDef: `type Rep__R <params> = Rep__R (Record <inner>)`.
    // The Record wrapper carries the runtime type name and gives library
    // codecs a hook for outer record framing (e.g. JSON `{}`).
    let inner_type = type_app(type_named("Record"), build_rep_type_inner(&plain_fields));
    let ctor_field_type = inner_type.clone();
    let rep_typedef = Decl::TypeDef {
        id: NodeId::fresh(),
        doc: vec![],
        public,
        opaque: false,
        name: rep_name.clone(),
        name_span: Span { start: 0, end: 0 },
        type_params: type_params.to_vec(),
        variants: vec![Annotated::bare(TypeConstructor {
            id: NodeId::fresh(),
            name: rep_name.clone(),
            fields: vec![(None, ctor_field_type)],
            span,
        })],
        deriving: vec![],
        multiline: false,
        span,
    };

    // 2. `to p = __Rep_R (And (Labeled "name" (Leaf p.name)) ...)`
    let param_name = "__val".to_string();
    let param_var = Expr::synth(
        span,
        ExprKind::Var {
            name: param_name.clone(),
        },
    );
    let inner_expr = build_rep_to_expr(&plain_fields, &param_var, span);
    let record_wrapped = apply2(
        &generic_name("Record"),
        string_lit(record_name, span),
        inner_expr,
        span,
    );
    let to_body = apply_ctor(&rep_name, record_wrapped, span);
    let to_method = Annotated::bare(ImplMethod {
        name: "to".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: param_name,
            span,
        }],
        body: to_body,
    });

    // 3. `from (__Rep_R (And (Labeled _ (Leaf n)) ...)) = R { name: n, ... }`
    let field_var_names: Vec<String> = (0..plain_fields.len()).map(|i| format!("__f{i}")).collect();
    let inner_pat = build_rep_from_pattern(&field_var_names, span);
    let record_pat = Pat::Constructor {
        id: NodeId::fresh(),
        name: generic_name("Record"),
        args: vec![
            Pat::Wildcard {
                id: NodeId::fresh(),
                span,
            },
            inner_pat,
        ],
        span,
    };
    let from_param = Pat::Constructor {
        id: NodeId::fresh(),
        name: rep_name.clone(),
        args: vec![record_pat],
        span,
    };
    let record_fields: Vec<(String, Span, Expr)> = plain_fields
        .iter()
        .zip(field_var_names.iter())
        .map(|((fname, _), vname)| {
            (
                fname.clone(),
                Span { start: 0, end: 0 },
                Expr::synth(
                    span,
                    ExprKind::Var {
                        name: vname.clone(),
                    },
                ),
            )
        })
        .collect();
    let from_body = if plain_fields.is_empty() {
        // Zero-field record: just construct the record with no fields.
        Expr::synth(
            span,
            ExprKind::RecordCreate {
                name: record_name.into(),
                fields: vec![],
            },
        )
    } else {
        Expr::synth(
            span,
            ExprKind::RecordCreate {
                name: record_name.into(),
                fields: record_fields,
            },
        )
    };
    let from_method = Annotated::bare(ImplMethod {
        name: "from".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![from_param],
        body: from_body,
    });

    let rep_with_params = apply_type_params(&rep_name, type_params);
    let impl_def = Decl::ImplDef {
        trait_name_span: Span { start: 0, end: 0 },
        target_type_span: Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Generic".into(),
        trait_type_args: vec![rep_with_params],
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![to_method, from_method],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![rep_typedef, impl_def])
}

/// Build a TypeExpr that applies `name` to each of `type_params` as a Var.
/// e.g. (`Rep__Box`, `["a"]`) -> `App(Named(Rep__Box), Var(a))`.
fn apply_type_params(name: &str, type_params: &[TypeParam]) -> TypeExpr {
    let mut acc = TypeExpr::Named {
        id: NodeId::fresh(),
        name: name.into(),
        span: Span { start: 0, end: 0 },
    };
    for tp in type_params {
        acc = TypeExpr::App {
            id: NodeId::fresh(),
            func: Box::new(acc),
            arg: Box::new(TypeExpr::Var {
                id: NodeId::fresh(),
                name: tp.name.clone(),
                span: Span { start: 0, end: 0 },
            }),
            span: Span { start: 0, end: 0 },
        };
    }
    acc
}

/// Build `type Rep__T = Rep__T <inner>` + `impl Generic Rep__T for T { to, from }`
/// for an ADT (`Decl::TypeDef`). Mirrors `derive_record_generic`'s shape but
/// the inner Rep is a right-leaning Or chain over `Labeled "Variant" <shape>`.
///
/// Direct self-reference detection only — indirect recursion via other types
/// is rare and deferred to Phase 2d alongside true recursive support.
fn derive_adt_generic(
    public: bool,
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    if variants.is_empty() {
        return Err(Some(Diagnostic {
            severity: Severity::Error,
            message: format!("cannot derive (Generic) for `{type_name}`: no variants"),
            span: Some(span),
        }));
    }

    let rep_name = format!("Rep__{type_name}");

    // 1. Inner Rep type = `Adt <Or-tree>` where the Or-tree is a right-leaning
    // chain of `Variant <variant_shape_type>`. `Adt` carries the runtime type
    // name; `Variant` replaces `Labeled` for constructor-name layers so library
    // codecs can distinguish constructor names from record-field names.
    let inner_type = type_app(type_named("Adt"), build_adt_rep_inner_type(variants));
    let rep_typedef = Decl::TypeDef {
        id: NodeId::fresh(),
        doc: vec![],
        public,
        opaque: false,
        name: rep_name.clone(),
        name_span: Span { start: 0, end: 0 },
        type_params: type_params.to_vec(),
        variants: vec![Annotated::bare(TypeConstructor {
            id: NodeId::fresh(),
            name: rep_name.clone(),
            fields: vec![(None, inner_type)],
            span,
        })],
        deriving: vec![],
        multiline: false,
        span,
    };

    // 2. `to __val = case __val { V0 a b -> Rep__T (Or_Left (Labeled "V0" ...)); ... }`
    let param_name = "__val".to_string();
    let n = variants.len();
    let to_arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .enumerate()
        .map(|(i, ann_v)| {
            let v = &ann_v.node;
            let field_vars: Vec<String> = (0..v.fields.len()).map(|j| format!("__x{j}")).collect();
            let pattern = Pat::Constructor {
                id: NodeId::fresh(),
                name: v.name.clone(),
                args: field_vars
                    .iter()
                    .map(|name| Pat::Var {
                        id: NodeId::fresh(),
                        name: name.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let shape_expr = build_variant_shape_expr(&v.fields, &field_vars, span);
            // Variant <shape> — constructor name lives in the type.
            let variant = apply_ctor(&generic_name("Variant"), shape_expr, span);
            let or_wrapped = or_wrap_expr(variant, i, n, span);
            let adt_wrapped = apply2(
                &generic_name("Adt"),
                string_lit(type_name, span),
                or_wrapped,
                span,
            );
            let body = apply_ctor(&rep_name, adt_wrapped, span);
            Annotated::bare(CaseArm {
                pattern,
                guard: None,
                body,
                span,
            })
        })
        .collect();
    let to_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: param_name.clone(),
                },
            )),
            arms: to_arms,
            dangling_trivia: vec![],
        },
    );
    let to_method = Annotated::bare(ImplMethod {
        name: "to".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: param_name.clone(),
            span,
        }],
        body: to_body,
    });

    // 3. `from __val = case __val { Rep__T (or-pat (Labeled _ shape-pat)) -> Ctor args; ... }`
    let from_param = "__rep".to_string();
    let from_arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .enumerate()
        .map(|(i, ann_v)| {
            let v = &ann_v.node;
            let field_vars: Vec<String> = (0..v.fields.len()).map(|j| format!("__y{j}")).collect();
            let shape_pat = build_variant_shape_pat(&v.fields, &field_vars, span);
            let variant_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Variant"),
                args: vec![shape_pat],
                span,
            };
            let or_wrapped_pat = or_wrap_pat(variant_pat, i, n, span);
            let adt_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Adt"),
                args: vec![
                    Pat::Wildcard {
                        id: NodeId::fresh(),
                        span,
                    },
                    or_wrapped_pat,
                ],
                span,
            };
            let outer_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: rep_name.clone(),
                args: vec![adt_pat],
                span,
            };
            let body = build_ctor_application(&v.name, &field_vars, span);
            Annotated::bare(CaseArm {
                pattern: outer_pat,
                guard: None,
                body,
                span,
            })
        })
        .collect();
    let from_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: from_param.clone(),
                },
            )),
            arms: from_arms,
            dangling_trivia: vec![],
        },
    );
    let from_method = Annotated::bare(ImplMethod {
        name: "from".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: from_param,
            span,
        }],
        body: from_body,
    });

    let rep_with_params = apply_type_params(&rep_name, type_params);
    let impl_def = Decl::ImplDef {
        trait_name_span: Span { start: 0, end: 0 },
        target_type_span: Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Generic".into(),
        trait_type_args: vec![rep_with_params],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![to_method, from_method],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![rep_typedef, impl_def])
}

/// Build the inner Rep type for an ADT: right-leaning `Or` chain wrapping
/// `Labeled <variant_shape>` for each variant.
fn build_adt_rep_inner_type(variants: &[Annotated<TypeConstructor>]) -> TypeExpr {
    let variant_shapes: Vec<TypeExpr> = variants
        .iter()
        .map(|v| {
            // Variant 'CtorName <shape> — constructor name lives in the type.
            type_app(
                type_app(type_named("Variant"), type_symbol(&v.node.name)),
                build_variant_shape_type(&v.node.fields),
            )
        })
        .collect();
    let mut iter = variant_shapes.into_iter().rev();
    let mut acc = iter.next().unwrap();
    for prev in iter {
        acc = type_app(type_app(type_named("Or"), prev), acc);
    }
    acc
}

/// Variant shape type: U1 for 0 fields, single field rep for 1, right-leaning
/// And chain for >=2.
fn build_variant_shape_type(fields: &[(Option<String>, TypeExpr)]) -> TypeExpr {
    if fields.is_empty() {
        return type_named("U1");
    }
    let n = fields.len();
    let mut acc = field_rep_type_adt(&fields[n - 1].0, &fields[n - 1].1);
    for i in (0..n - 1).rev() {
        acc = type_app(
            type_app(
                type_named("And"),
                field_rep_type_adt(&fields[i].0, &fields[i].1),
            ),
            acc,
        );
    }
    acc
}

/// For a single ADT constructor field: `Labeled 'lbl (Leaf T)` if labeled,
/// else `Leaf T`.
fn field_rep_type_adt(label: &Option<String>, ty: &TypeExpr) -> TypeExpr {
    let leaf = type_app(type_named("Leaf"), ty.clone());
    match label {
        Some(lbl) => type_app(type_app(type_named("Labeled"), type_symbol(lbl)), leaf),
        None => leaf,
    }
}

/// Expression form of `build_variant_shape_type`: builds the And/Labeled/Leaf
/// expression tree from already-bound field variables.
fn build_variant_shape_expr(
    fields: &[(Option<String>, TypeExpr)],
    field_vars: &[String],
    span: Span,
) -> Expr {
    if fields.is_empty() {
        return Expr::synth(
            span,
            ExprKind::Constructor {
                name: generic_name("U1"),
            },
        );
    }
    let leaf_for = |label: &Option<String>, var: &str| -> Expr {
        let leaf = apply_ctor(
            &generic_name("Leaf"),
            Expr::synth(span, ExprKind::Var { name: var.into() }),
            span,
        );
        match label {
            // Labeled (Leaf var) — name lives in the type now.
            Some(_) => apply_ctor(&generic_name("Labeled"), leaf, span),
            None => leaf,
        }
    };
    let n = fields.len();
    let mut acc = leaf_for(&fields[n - 1].0, &field_vars[n - 1]);
    for i in (0..n - 1).rev() {
        let cur = leaf_for(&fields[i].0, &field_vars[i]);
        acc = apply2(&generic_name("And"), cur, acc, span);
    }
    acc
}

/// Pattern form of the variant shape, binding each field to the matching name
/// in `field_vars`.
fn build_variant_shape_pat(
    fields: &[(Option<String>, TypeExpr)],
    field_vars: &[String],
    span: Span,
) -> Pat {
    if fields.is_empty() {
        return Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("U1"),
            args: vec![],
            span,
        };
    }
    let leaf_pat_for = |label: &Option<String>, var: &str| -> Pat {
        let leaf = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Leaf"),
            args: vec![Pat::Var {
                id: NodeId::fresh(),
                name: var.into(),
                span,
            }],
            span,
        };
        match label {
            // Labeled (Leaf var) — name lives in the type now.
            Some(_) => Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Labeled"),
                args: vec![leaf],
                span,
            },
            None => leaf,
        }
    };
    let n = fields.len();
    let mut acc = leaf_pat_for(&fields[n - 1].0, &field_vars[n - 1]);
    for i in (0..n - 1).rev() {
        let cur = leaf_pat_for(&fields[i].0, &field_vars[i]);
        acc = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("And"),
            args: vec![cur, acc],
            span,
        };
    }
    acc
}

/// `Or_Right^i (Or_Left inner)` for i < total-1; `Or_Right^(total-1) inner`
/// for the last variant; bare `inner` if there's only one variant.
fn or_wrap_expr(inner: Expr, index: usize, total: usize, span: Span) -> Expr {
    if total == 1 {
        return inner;
    }
    let mut e = if index == total - 1 {
        inner
    } else {
        apply_ctor(&generic_name("Or_Left"), inner, span)
    };
    for _ in 0..index {
        e = apply_ctor(&generic_name("Or_Right"), e, span);
    }
    e
}

/// Pattern counterpart to `or_wrap_expr`.
fn or_wrap_pat(inner: Pat, index: usize, total: usize, span: Span) -> Pat {
    if total == 1 {
        return inner;
    }
    let mut p = if index == total - 1 {
        inner
    } else {
        Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Or_Left"),
            args: vec![inner],
            span,
        }
    };
    for _ in 0..index {
        p = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Or_Right"),
            args: vec![p],
            span,
        };
    }
    p
}

/// Build a curried application of `ctor` to each `field_var`. For nullary
/// constructors, returns just `Ctor`.
fn build_ctor_application(ctor: &str, field_vars: &[String], span: Span) -> Expr {
    let mut e = Expr::synth(span, ExprKind::Constructor { name: ctor.into() });
    for v in field_vars {
        e = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(e),
                arg: Box::new(Expr::synth(span, ExprKind::Var { name: v.clone() })),
            },
        );
    }
    e
}

fn type_named(name: &str) -> TypeExpr {
    TypeExpr::Named {
        id: NodeId::fresh(),
        name: generic_name(name),
        span: Span { start: 0, end: 0 },
    }
}

fn generic_name(name: &str) -> String {
    format!("Std.Generic.{name}")
}

fn type_app(func: TypeExpr, arg: TypeExpr) -> TypeExpr {
    TypeExpr::App {
        id: NodeId::fresh(),
        func: Box::new(func),
        arg: Box::new(arg),
        span: Span { start: 0, end: 0 },
    }
}

/// Build a type-level symbol literal `TypeExpr::Symbol`. Used by the Generic
/// synthesizer to put constructor/field names at the type level rather than
/// carrying them as value-level strings.
fn type_symbol(name: &str) -> TypeExpr {
    TypeExpr::Symbol {
        id: NodeId::fresh(),
        name: name.to_string(),
        span: Span { start: 0, end: 0 },
    }
}

/// Build the inner Rep type (without the outer newtype wrapping). Right-leaning
/// And chain for >=2 fields; `Labeled 'name (Leaf T)` for 1 field; U1 for 0.
fn build_rep_type_inner(fields: &[(String, TypeExpr)]) -> TypeExpr {
    if fields.is_empty() {
        return type_named("U1");
    }
    let mut iter = fields.iter().rev();
    let (last_name, last_ty) = iter.next().unwrap();
    let mut acc = field_rep_type(last_name, last_ty);
    for (fname, ty) in iter {
        acc = type_app(type_app(type_named("And"), field_rep_type(fname, ty)), acc);
    }
    acc
}

/// Record field rep type: `Labeled 'fieldname (Leaf T)`. The field name is
/// carried as a type-level symbol; library codecs recover the string via
/// `KnownSymbol`.
fn field_rep_type(name: &str, ty: &TypeExpr) -> TypeExpr {
    type_app(
        type_app(type_named("Labeled"), type_symbol(name)),
        type_app(type_named("Leaf"), ty.clone()),
    )
}

fn apply_ctor(name: &str, arg: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(Expr::synth(
                span,
                ExprKind::Constructor { name: name.into() },
            )),
            arg: Box::new(arg),
        },
    )
}

fn apply2(func: &str, a: Expr, b: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(Expr::synth(
                span,
                ExprKind::App {
                    func: Box::new(Expr::synth(
                        span,
                        ExprKind::Constructor { name: func.into() },
                    )),
                    arg: Box::new(a),
                },
            )),
            arg: Box::new(b),
        },
    )
}

fn string_lit(s: &str, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::Lit {
            value: Lit::String(s.into(), StringKind::Normal),
        },
    )
}

/// Build the `to` body's inner expression (everything inside the __Rep_R newtype wrap).
fn build_rep_to_expr(fields: &[(String, TypeExpr)], record_var: &Expr, span: Span) -> Expr {
    if fields.is_empty() {
        return Expr::synth(
            span,
            ExprKind::Constructor {
                name: generic_name("U1"),
            },
        );
    }
    let labeled_for = |fname: &str| -> Expr {
        // Labeled (Leaf record_var.fname) — name lives in the type now.
        let field_access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(record_var.clone()),
                field: fname.into(),
                record_name: None,
            },
        );
        let leaf = apply_ctor(&generic_name("Leaf"), field_access, span);
        apply_ctor(&generic_name("Labeled"), leaf, span)
    };

    let mut iter = fields.iter().rev();
    let (last_name, _) = iter.next().unwrap();
    let mut acc = labeled_for(last_name);
    for (fname, _) in iter {
        acc = apply2(&generic_name("And"), labeled_for(fname), acc, span);
    }
    acc
}

/// Build the inner pattern matched by `from`: matches the And/Labeled/Leaf tree
/// and binds each field's value to the corresponding variable in `field_vars`.
fn build_rep_from_pattern(field_vars: &[String], span: Span) -> Pat {
    if field_vars.is_empty() {
        return Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("U1"),
            args: vec![],
            span,
        };
    }
    let labeled_pat = |var: &str| -> Pat {
        // Labeled (Leaf var) — name is at the type level, no wildcard needed.
        Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Labeled"),
            args: vec![Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Leaf"),
                args: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: var.into(),
                    span,
                }],
                span,
            }],
            span,
        }
    };

    let mut iter = field_vars.iter().rev();
    let last = iter.next().unwrap();
    let mut acc = labeled_pat(last);
    for v in iter {
        acc = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("And"),
            args: vec![labeled_pat(v), acc],
            span,
        };
    }
    acc
}

/// Generate `impl Show/Debug for R { show/debug r = "R { field: " <> show/debug r.field <> ... <> "}" }`
fn derive_record_stringify(
    trait_name: &str,
    method_name: &str,
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Decl {
    let param_name = "__val".to_string();
    let param_var = Expr::synth(
        span,
        ExprKind::Var {
            name: param_name.clone(),
        },
    );

    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();
    let body = build_record_debug_expr(method_name, record_name, &plain_fields, &param_var, span);

    // Each type param needs the same trait (same as ADT derive)
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_name.into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        trait_type_args: vec![],
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: method_name.into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: param_name,
                span,
            }],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Default for R { default = R { field: default, ... } }`.
fn derive_record_default(
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Decl {
    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();
    let body_fields: Vec<(String, Span, Expr)> = plain_fields
        .iter()
        .map(|(field_name, _)| {
            (
                field_name.clone(),
                Span { start: 0, end: 0 },
                Expr::synth(
                    span,
                    ExprKind::Var {
                        name: "default".into(),
                    },
                ),
            )
        })
        .collect();
    let body = Expr::synth(
        span,
        ExprKind::RecordCreate {
            name: record_name.into(),
            fields: body_fields,
        },
    );

    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .filter(|tp| {
            plain_fields
                .iter()
                .any(|(_, ty)| type_expr_contains_var(ty, &tp.name))
        })
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: "Default".into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Default".into(),
        trait_type_args: vec![],
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: "default".into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Build the debug string expression for a record. For fields with anonymous
/// record types, generates inline formatting instead of calling `debug`.
fn build_record_debug_expr(
    method_name: &str,
    label: &str,
    fields: &[(String, TypeExpr)],
    base_expr: &Expr,
    span: Span,
) -> Expr {
    let mut parts: Vec<Expr> = Vec::new();
    let mut prefix = if label.is_empty() {
        "{ ".to_string()
    } else {
        format!("{label} {{ ")
    };

    for (i, (field_name, ty)) in fields.iter().enumerate() {
        if i > 0 {
            prefix.push_str(", ");
        }
        prefix.push_str(field_name);
        prefix.push_str(": ");
        parts.push(Expr::synth(
            span,
            ExprKind::Lit {
                value: Lit::String(prefix.clone(), StringKind::Normal),
            },
        ));
        prefix.clear();

        let field_access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(base_expr.clone()),
                field: field_name.clone(),
                record_name: None,
            },
        );

        match ty {
            TypeExpr::Record {
                fields: inner_fields,
                ..
            } => {
                // Inline the anonymous record's debug output
                parts.push(build_record_debug_expr(
                    method_name,
                    "",
                    inner_fields,
                    &field_access,
                    span,
                ));
            }
            _ => {
                // Call debug/show on the field value
                parts.push(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: method_name.into(),
                            },
                        )),
                        arg: Box::new(field_access),
                    },
                ));
            }
        }
    }

    parts.push(Expr::synth(
        span,
        ExprKind::Lit {
            value: Lit::String(" }".into(), StringKind::Normal),
        },
    ));

    parts
        .into_iter()
        .reduce(|acc, part| {
            Expr::synth(
                span,
                ExprKind::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(acc),
                    right: Box::new(part),
                },
            )
        })
        .unwrap()
}

fn generate_derive(
    trait_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Option<Decl> {
    // Use bare trait name — deriving works with well-known traits only.
    // The parser may produce qualified names (e.g. "Std.Base.Show") if written that way.
    let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
    match bare {
        "Show" => Some(derive_stringify(
            "Show",
            "show",
            type_name,
            type_params,
            variants,
            span,
        )),
        "Debug" => Some(derive_stringify(
            "Debug",
            "debug",
            type_name,
            type_params,
            variants,
            span,
        )),
        "Eq" => Some(derive_marker_trait("Eq", type_name, type_params, span)),
        "Ord" => Some(derive_ord(type_name, type_params, variants, span)),
        "Enum" => Some(derive_enum(type_name, variants, span)),
        // "Generic" is handled by `expand_derives` via `derive_adt_generic`
        // because it emits multiple decls (TypeDef + ImplDef).
        _ => None,
    }
}

/// Generate `impl Show/Debug for T { show/debug x = case x { ... } }`
fn derive_stringify(
    trait_name: &str,
    method_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Decl {
    let arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .map(|ann_variant| {
            let variant = &ann_variant.node;
            let ctor_name = &variant.name;

            if variant.fields.is_empty() {
                // `Ctor -> "Ctor"`
                Annotated::bare(CaseArm {
                    pattern: Pat::Constructor {
                        id: NodeId::fresh(),
                        name: ctor_name.clone(),
                        args: vec![],
                        span,
                    },
                    guard: None,
                    body: Expr::synth(
                        span,
                        ExprKind::Lit {
                            value: Lit::String(ctor_name.clone(), StringKind::Normal),
                        },
                    ),
                    span,
                })
            } else {
                // Generate field variable names
                let field_vars: Vec<String> = (0..variant.fields.len())
                    .map(|i| format!("__x{}", i))
                    .collect();

                let pattern = Pat::Constructor {
                    id: NodeId::fresh(),
                    name: ctor_name.clone(),
                    args: field_vars
                        .iter()
                        .map(|v| Pat::Var {
                            id: NodeId::fresh(),
                            name: v.clone(),
                            span,
                        })
                        .collect(),
                    span,
                };

                // Build: "Ctor(" <> show/debug __x0 <> ", " <> show/debug __x1 <> ")"
                // With labels: "Ctor(label: " <> show/debug __x0 <> ... <> ")"
                let mut parts: Vec<Expr> = Vec::new();
                let mut prefix = format!("{ctor_name}(");

                for (i, (label, _ty)) in variant.fields.iter().enumerate() {
                    if i > 0 {
                        prefix.push_str(", ");
                    }
                    if let Some(lbl) = label {
                        prefix.push_str(lbl);
                        prefix.push_str(": ");
                    }
                    parts.push(Expr::synth(
                        span,
                        ExprKind::Lit {
                            value: Lit::String(prefix.clone(), StringKind::Normal),
                        },
                    ));
                    prefix.clear();

                    // `show/debug __xi`
                    parts.push(Expr::synth(
                        span,
                        ExprKind::App {
                            func: Box::new(Expr::synth(
                                span,
                                ExprKind::Var {
                                    name: method_name.into(),
                                },
                            )),
                            arg: Box::new(Expr::synth(
                                span,
                                ExprKind::Var {
                                    name: field_vars[i].clone(),
                                },
                            )),
                        },
                    ));
                }

                parts.push(Expr::synth(
                    span,
                    ExprKind::Lit {
                        value: Lit::String(")".into(), StringKind::Normal),
                    },
                ));

                let body = parts
                    .into_iter()
                    .reduce(|acc, part| {
                        Expr::synth(
                            span,
                            ExprKind::BinOp {
                                op: BinOp::Concat,
                                left: Box::new(acc),
                                right: Box::new(part),
                            },
                        )
                    })
                    .unwrap();

                Annotated::bare(CaseArm {
                    pattern,
                    guard: None,
                    body,
                    span,
                })
            }
        })
        .collect();

    let scrutinee_name = "__val".to_string();
    let body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: scrutinee_name.clone(),
                },
            )),
            arms,
            dangling_trivia: vec![],
        },
    );

    // Each type param needs the same trait
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_name.into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: method_name.into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: scrutinee_name,
                span,
            }],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Ord for T { compare x y = ... }` using declaration-order
/// constructor indexing and left-to-right field comparison.
fn derive_ord(
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Decl {
    let x = "__x".to_string();
    let y = "__y".to_string();

    // Build same-constructor arms: (A(a0,a1), A(b0,b1)) -> field-by-field compare
    let mut arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .map(|ann_variant| {
            let variant = &ann_variant.node;
            let ctor = &variant.name;
            let arity = variant.fields.len();

            let a_vars: Vec<String> = (0..arity).map(|i| format!("__a{i}")).collect();
            let b_vars: Vec<String> = (0..arity).map(|i| format!("__b{i}")).collect();

            let pat_a = Pat::Constructor {
                id: NodeId::fresh(),
                name: ctor.clone(),
                args: a_vars
                    .iter()
                    .map(|v| Pat::Var {
                        id: NodeId::fresh(),
                        name: v.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let pat_b = Pat::Constructor {
                id: NodeId::fresh(),
                name: ctor.clone(),
                args: b_vars
                    .iter()
                    .map(|v| Pat::Var {
                        id: NodeId::fresh(),
                        name: v.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let pattern = Pat::Tuple {
                id: NodeId::fresh(),
                elements: vec![pat_a, pat_b],
                span,
            };

            let body = if arity == 0 {
                // Same nullary constructor: always Eq
                Expr::synth(span, ExprKind::Constructor { name: "Eq".into() })
            } else {
                // Compare fields left-to-right, short-circuit on non-Eq
                build_field_compare(&a_vars, &b_vars, span)
            };

            Annotated::bare(CaseArm {
                pattern,
                guard: None,
                body,
                span,
            })
        })
        .collect();

    // Wildcard arm for different constructors: compare by index.
    if variants.len() > 1 {
        let index_case = |var: &str| -> Expr {
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(Expr::synth(span, ExprKind::Var { name: var.into() })),
                    arms: variants
                        .iter()
                        .enumerate()
                        .map(|(i, ann_v)| {
                            let v = &ann_v.node;
                            let wildcards: Vec<Pat> = (0..v.fields.len())
                                .map(|_| Pat::Wildcard {
                                    id: NodeId::fresh(),
                                    span,
                                })
                                .collect();
                            Annotated::bare(CaseArm {
                                pattern: Pat::Constructor {
                                    id: NodeId::fresh(),
                                    name: v.name.clone(),
                                    args: wildcards,
                                    span,
                                },
                                guard: None,
                                body: Expr::synth(
                                    span,
                                    ExprKind::Lit {
                                        value: Lit::Int((i as i64).to_string(), i as i64),
                                    },
                                ),
                                span,
                            })
                        })
                        .collect(),
                    dangling_trivia: vec![],
                },
            )
        };

        // compare (case __x { ... -> 0, ... -> 1 }) (case __y { ... })
        let compare_indices = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: "compare".into(),
                            },
                        )),
                        arg: Box::new(index_case(&x)),
                    },
                )),
                arg: Box::new(index_case(&y)),
            },
        );

        arms.push(Annotated::bare(CaseArm {
            pattern: Pat::Wildcard {
                id: NodeId::fresh(),
                span,
            },
            guard: None,
            body: compare_indices,
            span,
        }));
    }

    let body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Tuple {
                    elements: vec![
                        Expr::synth(span, ExprKind::Var { name: x.clone() }),
                        Expr::synth(span, ExprKind::Var { name: y.clone() }),
                    ],
                },
            )),
            arms,
            dangling_trivia: vec![],
        },
    );

    // Ord requires Eq, but Eq is BIF-dispatched (no dict), so only Ord
    // needs to be in the where clause for dictionary passing purposes.
    // The Eq supertrait constraint is still checked by the typechecker.
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: "Ord".into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Ord".into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: "compare".into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![
                Pat::Var {
                    id: NodeId::fresh(),
                    name: x,
                    span,
                },
                Pat::Var {
                    id: NodeId::fresh(),
                    name: y,
                    span,
                },
            ],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Build a left-to-right field comparison chain:
/// `case compare a0 b0 { Eq -> case compare a1 b1 { Eq -> ... Eq; o -> o }; o -> o }`
fn build_field_compare(a_vars: &[String], b_vars: &[String], span: Span) -> Expr {
    assert!(!a_vars.is_empty());

    // Start from the last field and build inward
    let mut result = Expr::synth(span, ExprKind::Constructor { name: "Eq".into() });

    for i in (0..a_vars.len()).rev() {
        let cmp_call = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: "compare".into(),
                            },
                        )),
                        arg: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: a_vars[i].clone(),
                            },
                        )),
                    },
                )),
                arg: Box::new(Expr::synth(
                    span,
                    ExprKind::Var {
                        name: b_vars[i].clone(),
                    },
                )),
            },
        );

        if i == a_vars.len() - 1 && a_vars.len() == 1 {
            // Single field: just return the compare result directly
            result = cmp_call;
        } else {
            // Wrap in: case compare ai bi { Eq -> <inner>; __other -> __other }
            let other_var = format!("__ord{i}");
            result = Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(cmp_call),
                    arms: vec![
                        Annotated::bare(CaseArm {
                            pattern: Pat::Constructor {
                                id: NodeId::fresh(),
                                name: "Eq".into(),
                                args: vec![],
                                span,
                            },
                            guard: None,
                            body: result,
                            span,
                        }),
                        Annotated::bare(CaseArm {
                            pattern: Pat::Var {
                                id: NodeId::fresh(),
                                name: other_var.clone(),
                                span,
                            },
                            guard: None,
                            body: Expr::synth(span, ExprKind::Var { name: other_var }),
                            span,
                        }),
                    ],
                    dangling_trivia: vec![],
                },
            );
        }
    }

    result
}

/// Generate a method-less impl for an operator trait (e.g. Eq).
/// The trait is dispatched via BEAM BIFs, so no methods are needed --
/// we just register the impl so the typechecker accepts the constraint.
fn derive_marker_trait(
    trait_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    span: Span,
) -> Decl {
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_name.into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Enum for T { to_enum x = case x { ... }; from_enum n = case n { ... } }`
/// Only valid for types with all nullary constructors.
fn derive_enum(type_name: &str, variants: &[Annotated<TypeConstructor>], span: Span) -> Decl {
    for ann_v in variants {
        let v = &ann_v.node;
        if !v.fields.is_empty() {
            panic!(
                "cannot derive Enum for `{}`: constructor `{}` has fields (Enum requires all nullary constructors)",
                type_name, v.name
            );
        }
    }

    // to_enum x = case x { Red -> 0 | Green -> 1 | Blue -> 2 }
    let to_enum_param = "__val".to_string();
    let to_enum_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: to_enum_param.clone(),
                },
            )),
            arms: variants
                .iter()
                .enumerate()
                .map(|(i, ann_v)| {
                    Annotated::bare(CaseArm {
                        pattern: Pat::Constructor {
                            id: NodeId::fresh(),
                            name: ann_v.node.name.clone(),
                            args: vec![],
                            span,
                        },
                        guard: None,
                        body: Expr::synth(
                            span,
                            ExprKind::Lit {
                                value: Lit::Int((i as i64).to_string(), i as i64),
                            },
                        ),
                        span,
                    })
                })
                .collect(),
            dangling_trivia: vec![],
        },
    );

    // from_enum n = case n { 0 -> Red | 1 -> Green | 2 -> Blue | _ -> panic "invalid enum index" }
    let from_enum_param = "__n".to_string();
    let mut from_enum_arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .enumerate()
        .map(|(i, ann_v)| {
            Annotated::bare(CaseArm {
                pattern: Pat::Lit {
                    id: NodeId::fresh(),
                    value: Lit::Int((i as i64).to_string(), i as i64),
                    span,
                },
                guard: None,
                body: Expr::synth(
                    span,
                    ExprKind::Constructor {
                        name: ann_v.node.name.clone(),
                    },
                ),
                span,
            })
        })
        .collect();
    // Wildcard arm: panic on invalid index
    from_enum_arms.push(Annotated::bare(CaseArm {
        pattern: Pat::Wildcard {
            id: NodeId::fresh(),
            span,
        },
        guard: None,
        body: Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::Var {
                        name: "panic".into(),
                    },
                )),
                arg: Box::new(Expr::synth(
                    span,
                    ExprKind::Lit {
                        value: Lit::String(
                            format!("invalid enum index for {}", type_name),
                            StringKind::Normal,
                        ),
                    },
                )),
            },
        ),
        span,
    }));
    let from_enum_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: from_enum_param.clone(),
                },
            )),
            arms: from_enum_arms,
            dangling_trivia: vec![],
        },
    );

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Enum".into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: vec![],
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![
            Annotated::bare(ImplMethod {
                name: "to_enum".into(),
                name_span: Span { start: 0, end: 0 },
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: to_enum_param,
                    span,
                }],
                body: to_enum_body,
            }),
            Annotated::bare(ImplMethod {
                name: "from_enum".into(),
                name_span: Span { start: 0, end: 0 },
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: from_enum_param,
                    span,
                }],
                body: from_enum_body,
            }),
        ],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}
