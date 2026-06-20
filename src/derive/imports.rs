use super::*;
use crate::ast::*;
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
    /// Impls visible from imports. Impls are coherence-global, so they are kept
    /// as a flat list (not keyed by surface name) and brought in whenever their
    /// module is imported. Used by routed-derive scope specialization.
    pub(crate) impls: Vec<DeriveImplInfo>,
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
    pub opaque: bool,
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
pub(crate) struct ModuleSummary {
    traits: HashMap<String, RoutedTraitInfo>,
    types: HashMap<String, WrapperTypeInfo>,
    records: HashMap<String, WrapperRecordInfo>,
    impls: Vec<DeriveImplInfo>,
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
    const PRELUDE_SRC: &str = include_str!("../stdlib/prelude.saga");
    if let Ok(prelude_tokens) = crate::lexer::Lexer::new(PRELUDE_SRC).lex()
        && let Ok(prelude_program) = crate::parser::Parser::new(prelude_tokens).parse_program()
    {
        collect_summaries_from_imports(&prelude_program, module_map, &mut out);
    }

    collect_summaries_from_imports(program, module_map, &mut out);
    out
}


pub(crate) fn collect_summaries_from_imports(
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
            // Unqualified `import A.B.C` brings names into scope under the last
            // path segment (`C.name`), so the derive scope must register that
            // prefix too — otherwise a `deriving (C.SomeTrait ...)` can't find
            // the imported trait's synthesis metadata and silently falls back to
            // the non-synthesizing path (the synthesized `Rep__*` then never
            // exists). An explicit `as` alias overrides the segment.
            let last_segment = module_name.rsplit('.').next().unwrap_or(&module_name);
            merge_summary_import(
                out,
                &module_name,
                alias.as_deref().unwrap_or(last_segment),
                exposing.as_ref(),
                &summary,
            );
        }
    }
}


pub(crate) fn module_summary(program: &[Decl]) -> ModuleSummary {
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
                opaque,
                ..
            } => {
                summary.types.insert(
                    name.clone(),
                    WrapperTypeInfo {
                        type_params: type_params.clone(),
                        variants: if *opaque {
                            vec![]
                        } else {
                            variants.iter().map(|v| v.node.clone()).collect()
                        },
                        derives_generic: deriving.iter().any(|d| d.is_plain_named("Generic")),
                        opaque: *opaque,
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
    // Collect every data constructor declared in this module, public or not:
    // a default body may construct a value of a type that the module keeps
    // private (the downstream impl never names the type, it just gets the
    // value back), so privacy doesn't gate which constructors a default body
    // can reference.
    let defining_module_constructors: std::collections::HashSet<String> = program
        .iter()
        .flat_map(|d| match d {
            Decl::TypeDef { variants, .. } => {
                variants.iter().map(|v| v.node.name.clone()).collect()
            }
            _ => Vec::new(),
        })
        .collect();
    for d in program {
        if let Decl::ImplDef {
            trait_name,
            trait_type_args,
            target_type_expr: Some(target),
            ..
        } = d
            && trait_type_args.len() == 1
        {
            // Qualify the impl's type names with their defining module so the
            // bindings read off during scope specialization resolve correctly
            // when emitted into the importing module.
            summary.impls.push(DeriveImplInfo {
                trait_bare: trait_name.rsplit('.').next().unwrap_or(trait_name).to_string(),
                target: qualify_summary_type_expr(
                    target.clone(),
                    module_name.as_deref(),
                    &local_type_names,
                ),
                row: qualify_summary_type_expr(
                    trait_type_args[0].clone(),
                    module_name.as_deref(),
                    &local_type_names,
                ),
            });
        }
        if let Decl::TraitDef {
            name,
            type_params,
            functional_dependency,
            synthesis,
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
                    fundep: functional_dependency.clone(),
                    synthesis: synthesis
                        .as_ref()
                        .map(|s| qualify_synthesis_spec(s, module_name.as_deref())),
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
                    defining_module_constructors: defining_module_constructors.clone(),
                },
            );
        }
    }
    summary
}


pub(crate) fn qualify_summary_type_expr(
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


pub(crate) fn merge_summary_import(
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
    // Impls are coherence-global: importing a module brings all its impls into
    // scope regardless of the `exposing` list. Dedup by structural identity so
    // repeated imports (e.g. via the prelude) don't accumulate duplicates.
    for imp in &summary.impls {
        if !out.impls.iter().any(|existing| {
            existing.trait_bare == imp.trait_bare
                && te_structural_eq(&existing.target, &imp.target)
                && te_structural_eq(&existing.row, &imp.row)
        }) {
            out.impls.push(imp.clone());
        }
    }
}


pub(crate) fn register_summary_entry<T: Clone>(
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

