use std::collections::{HashMap, HashSet};

use super::import_scope::synthesize_all_exposed;
use crate::typechecker::{
    Checker, EffectDefInfo, HandlerInfo, ImplInfo, RecordInfo, Scheme, TraitInfo, TypeAliasInfo,
    arity_keyed_target_name,
};

/// All public items exported by a typechecked module, cached as a single unit.
#[derive(Debug, Clone, Default)]
pub struct ModuleExports {
    /// Public type bindings: name -> scheme.
    pub bindings: Vec<(String, Scheme)>,
    /// Public binding surface name -> canonical origin name.
    /// Local exports map to `ThisModule.name`; re-exports retain their
    /// defining module, e.g. `plus -> Math.add`.
    pub binding_origins: HashMap<String, String>,
    /// Type name -> constructor names (empty vec for opaque types).
    pub type_constructors: HashMap<String, Vec<String>>,
    /// Public type surface name -> canonical origin type name.
    pub type_origins: HashMap<String, String>,
    /// Record name -> record info (type params + field types).
    pub record_defs: HashMap<String, RecordInfo>,
    /// Trait name -> trait info.
    pub traits: HashMap<String, TraitInfo>,
    /// Public trait surface name -> canonical origin trait name.
    pub trait_origins: HashMap<String, String>,
    /// (trait_name, trait_type_args, target_type) -> impl info.
    pub trait_impls: HashMap<(String, Vec<String>, String), ImplInfo>,
    /// Effect name -> effect def info.
    pub effects: HashMap<String, EffectDefInfo>,
    /// Public effect surface name -> canonical origin effect name.
    pub effect_origins: HashMap<String, String>,
    /// Handler name -> handler info.
    pub handlers: HashMap<String, HandlerInfo>,
    /// Public handler surface name -> canonical origin handler name.
    pub handler_origins: HashMap<String, String>,
    /// Type name -> declared parameter count (for arity checking across modules).
    pub type_arity: HashMap<String, usize>,
    /// Type name -> declared kinds of each type parameter (for kind checking
    /// across modules, e.g. symbol-kinded params on stdlib `Proxy`).
    pub type_param_kinds: HashMap<String, Vec<crate::ast::Kind>>,
    /// Public type aliases — exported by bare name. Bodies use the alias's
    /// own positional var IDs as placeholders; the importer re-keys them
    /// against fresh IDs at registration time.
    pub type_aliases: HashMap<String, TypeAliasInfo>,
    /// Names of effectful functions (for cross-module is_known_local checks).
    pub effectful_funs: HashSet<String>,
    /// Definition-site NodeIds for exported bindings (for cross-module find-references).
    pub def_ids: HashMap<String, crate::ast::NodeId>,
    /// Doc comments for exported declarations: name -> doc lines.
    pub doc_comments: HashMap<String, Vec<String>>,
}

impl ModuleExports {
    /// Collect all public exports from a typechecked module.
    pub fn collect(program: &[crate::ast::Decl], checker: &Checker) -> Self {
        use crate::ast::Decl;

        let pub_names = public_names_for_tc(program);

        // Bindings: from env and constructors
        let mut bindings: Vec<(String, Scheme)> = Vec::new();
        let mut binding_origins: HashMap<String, String> = HashMap::new();
        let mut def_ids: HashMap<String, crate::ast::NodeId> = HashMap::new();
        let module_prefix = checker.current_module.as_deref().unwrap_or("");
        for name in &pub_names {
            if let Some(scheme) = checker.env.get(name) {
                bindings.push((name.to_string(), scheme.clone()));
                binding_origins
                    .insert(name.to_string(), canonical_export_name(module_prefix, name));
                if let Some(did) = checker.env.def_id(name) {
                    def_ids.insert(name.to_string(), did);
                }
            } else if let Some(scheme) = checker.constructors.get(name) {
                bindings.push((name.to_string(), scheme.clone()));
                binding_origins
                    .insert(name.to_string(), canonical_export_name(module_prefix, name));
                if let Some(&did) = checker.lsp.constructor_def_ids.get(name) {
                    def_ids.insert(name.to_string(), did);
                }
            }
        }

        // Type constructors
        let mut type_constructors: HashMap<String, Vec<String>> = HashMap::new();
        let mut type_origins: HashMap<String, String> = HashMap::new();
        for decl in program {
            match decl {
                Decl::TypeDef {
                    public: true,
                    opaque,
                    name,
                    variants,
                    ..
                } => {
                    type_origins.insert(name.clone(), canonical_export_name(module_prefix, name));
                    if *opaque {
                        type_constructors.insert(name.clone(), vec![]);
                    } else {
                        let ctors: Vec<String> =
                            variants.iter().map(|v| v.node.name.clone()).collect();
                        type_constructors.insert(name.clone(), ctors);
                    }
                }
                Decl::RecordDef {
                    public: true, name, ..
                } => {
                    type_origins.insert(name.clone(), canonical_export_name(module_prefix, name));
                    type_constructors.insert(name.clone(), vec![name.clone()]);
                }
                _ => {}
            }
        }

        // Records, traits, trait impls, effects, handlers: all from AST + checker state
        let mut record_defs: HashMap<String, RecordInfo> = HashMap::new();
        let mut traits: HashMap<String, TraitInfo> = HashMap::new();
        let mut trait_origins: HashMap<String, String> = HashMap::new();
        let mut trait_impls: HashMap<(String, Vec<String>, String), ImplInfo> = HashMap::new();
        let mut effects: HashMap<String, EffectDefInfo> = HashMap::new();
        let mut effect_origins: HashMap<String, String> = HashMap::new();
        let mut handlers: HashMap<String, HandlerInfo> = HashMap::new();
        let mut handler_origins: HashMap<String, String> = HashMap::new();

        for decl in program {
            match decl {
                Decl::RecordDef {
                    public: true, name, ..
                } => {
                    // records map uses canonical keys
                    let canonical = checker
                        .current_module
                        .as_ref()
                        .map(|m| format!("{}.{}", m, name))
                        .unwrap_or_else(|| name.clone());
                    if let Some(fields) = checker.records.get(&canonical) {
                        record_defs.insert(name.clone(), fields.clone());
                    }
                }
                Decl::TraitDef {
                    public: true, name, ..
                } => {
                    // Traits are stored under canonical key (Module.Trait)
                    let canonical = checker
                        .current_module
                        .as_ref()
                        .map(|m| format!("{}.{}", m, name))
                        .unwrap_or_else(|| name.clone());
                    if let Some(info) = checker.trait_state.traits.get(&canonical) {
                        traits.insert(name.clone(), info.clone());
                        trait_origins.insert(name.clone(), canonical);
                    }
                }
                Decl::ImplDef {
                    id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    type_params,
                    ..
                } => {
                    let resolved_trait = checker.resolved_impl_trait_name(*id, trait_name);
                    let resolved_target = checker.resolved_impl_target_type_name(*id, target_type);
                    let resolved_target =
                        arity_keyed_target_name(&resolved_target, type_params.len());
                    let resolved_trait_type_args: Vec<String> = trait_type_args
                        .iter()
                        .map(|te| checker.resolved_type_name(te.id(), te.simple_name()))
                        .collect();
                    let key = (resolved_trait, resolved_trait_type_args, resolved_target);
                    if let Some(info) = checker.trait_state.impls.get(&key) {
                        trait_impls.insert(key, info.clone());
                    }
                }
                Decl::EffectDef {
                    public: true, name, ..
                } => {
                    // Effects are stored under canonical key (Module.Effect)
                    let canonical = checker
                        .current_module
                        .as_ref()
                        .map(|m| format!("{}.{}", m, name))
                        .unwrap_or_else(|| name.clone());
                    if let Some(info) = checker.effects.get(&canonical) {
                        effects.insert(name.clone(), info.clone());
                        effect_origins.insert(name.clone(), canonical);
                    }
                }
                Decl::HandlerDef {
                    public: true, name, ..
                } => {
                    let canonical = checker
                        .current_module
                        .as_ref()
                        .map(|m| format!("{}.{}", m, name))
                        .unwrap_or_else(|| name.clone());
                    if let Some(info) = checker.handlers.get(&canonical) {
                        handlers.insert(name.clone(), info.clone());
                        handler_origins.insert(name.clone(), canonical);
                    }
                }
                _ => {}
            }
        }

        // Collect type arities for all exported types.
        // The checker stores type_arity under canonical names, but exports use bare names.
        let mut type_arity: HashMap<String, usize> = HashMap::new();
        for name in type_constructors.keys() {
            let canonical = if module_prefix.is_empty() {
                name.clone()
            } else {
                format!("{}.{}", module_prefix, name)
            };
            if let Some(&arity) = checker.type_arity.get(&canonical) {
                type_arity.insert(name.clone(), arity);
            }
        }
        for name in record_defs.keys() {
            let canonical = if module_prefix.is_empty() {
                name.clone()
            } else {
                format!("{}.{}", module_prefix, name)
            };
            if let Some(&arity) = checker.type_arity.get(&canonical) {
                type_arity.insert(name.clone(), arity);
            }
        }

        // Collect type aliases declared `pub`. The body is keyed under the
        // alias's bare name (importer canonicalizes during merge).
        let mut type_aliases_out: HashMap<String, TypeAliasInfo> = HashMap::new();
        for decl in program {
            if let crate::ast::Decl::TypeAlias {
                public: true, name, ..
            } = decl
            {
                let canonical = if module_prefix.is_empty() {
                    name.clone()
                } else {
                    format!("{}.{}", module_prefix, name)
                };
                if let Some(info) = checker.type_aliases.get(&canonical) {
                    type_origins.insert(name.clone(), canonical.clone());
                    type_aliases_out.insert(name.clone(), info.clone());
                    // Also pick up arity/kinds so importer arity/kind-checks
                    // work. The kinds map is filled below from
                    // `type_constructors.keys()` only, which doesn't include
                    // aliases — surface them here too.
                    if let Some(&arity) = checker.type_arity.get(&canonical) {
                        type_arity.insert(name.clone(), arity);
                    }
                }
            }
        }

        // Collect declared param kinds (e.g. `Proxy (n : Symbol)`) so the
        // importer can enforce kind-correct uses at type-application sites.
        let mut type_param_kinds: HashMap<String, Vec<crate::ast::Kind>> = HashMap::new();
        for name in type_constructors.keys().chain(type_aliases_out.keys()) {
            let canonical = if module_prefix.is_empty() {
                name.clone()
            } else {
                format!("{}.{}", module_prefix, name)
            };
            if let Some(kinds) = checker.type_param_kinds.get(&canonical) {
                type_param_kinds.insert(name.clone(), kinds.clone());
            }
        }

        // Collect effectful function names — only functions with declared effects,
        // not all known_funs (which includes pure functions too).
        let effectful_funs: HashSet<String> = {
            let mut set = HashSet::new();
            for decl in program {
                if let Decl::FunSignature {
                    public: true,
                    name,
                    effects,
                    ..
                } = decl
                    && !effects.is_empty()
                {
                    set.insert(name.clone());
                }
            }
            set
        };

        // Collect doc comments from all public declarations
        let mut doc_comments: HashMap<String, Vec<String>> = HashMap::new();
        for decl in program {
            let (name, doc) = match decl {
                Decl::FunSignature {
                    public: true,
                    name,
                    doc,
                    ..
                } => (name, doc),
                Decl::TypeDef {
                    public: true,
                    name,
                    doc,
                    ..
                } => (name, doc),
                Decl::RecordDef {
                    public: true,
                    name,
                    doc,
                    ..
                } => (name, doc),
                Decl::EffectDef {
                    public: true,
                    name,
                    doc,
                    ..
                } => (name, doc),
                Decl::HandlerDef {
                    public: true,
                    name,
                    doc,
                    ..
                } => (name, doc),
                Decl::TraitDef {
                    public: true,
                    name,
                    doc,
                    ..
                } => (name, doc),
                _ => continue,
            };
            if !doc.is_empty() {
                doc_comments.insert(name.clone(), doc.clone());
            }
        }

        collect_value_reexports(
            program,
            checker,
            &mut bindings,
            &mut binding_origins,
            &mut def_ids,
            &mut doc_comments,
        );
        collect_type_and_trait_reexports(
            program,
            checker,
            &mut bindings,
            &mut binding_origins,
            &mut def_ids,
            &mut type_constructors,
            &mut type_origins,
            &mut record_defs,
            &mut traits,
            &mut trait_origins,
            &mut trait_impls,
            &mut type_arity,
            &mut type_param_kinds,
            &mut type_aliases_out,
            &mut doc_comments,
        );
        collect_effect_and_handler_reexports(
            program,
            checker,
            &mut effects,
            &mut effect_origins,
            &mut handlers,
            &mut handler_origins,
            &mut doc_comments,
        );

        let effectful_funs = collect_effectful_reexports(program, checker, effectful_funs);

        ModuleExports {
            bindings,
            binding_origins,
            type_constructors,
            type_origins,
            record_defs,
            traits,
            trait_origins,
            trait_impls,
            effects,
            effect_origins,
            handlers,
            handler_origins,
            type_arity,
            type_param_kinds,
            type_aliases: type_aliases_out,
            effectful_funs,
            def_ids,
            doc_comments,
        }
    }
}

fn canonical_export_name(module_prefix: &str, name: &str) -> String {
    if module_prefix.is_empty() {
        name.to_string()
    } else {
        format!("{}.{}", module_prefix, name)
    }
}

fn collect_effectful_reexports(
    program: &[crate::ast::Decl],
    checker: &Checker,
    mut effectful_funs: HashSet<String>,
) -> HashSet<String> {
    for (module_name, item) in public_import_items(program, checker) {
        let Some(exports) = checker.modules.exports.get(&module_name) else {
            continue;
        };
        if exports.effectful_funs.contains(&item.name) {
            effectful_funs.insert(item.surface_name().to_string());
        }
    }
    effectful_funs
}

fn collect_value_reexports(
    program: &[crate::ast::Decl],
    checker: &Checker,
    bindings: &mut Vec<(String, Scheme)>,
    binding_origins: &mut HashMap<String, String>,
    def_ids: &mut HashMap<String, crate::ast::NodeId>,
    doc_comments: &mut HashMap<String, Vec<String>>,
) {
    for (module_name, item) in public_import_items(program, checker) {
        let Some(exports) = checker.modules.exports.get(&module_name) else {
            continue;
        };
        let origin_name = item.name.as_str();
        let surface = item.surface_name();
        let Some((_, scheme)) = exports
            .bindings
            .iter()
            .find(|(name, _)| name == origin_name)
        else {
            continue;
        };
        if bindings.iter().any(|(name, _)| name == surface) {
            continue;
        }
        bindings.push((surface.to_string(), scheme.clone()));
        let origin = exports
            .binding_origins
            .get(origin_name)
            .cloned()
            .unwrap_or_else(|| format!("{}.{}", module_name, origin_name));
        binding_origins.insert(surface.to_string(), origin);
        if let Some(&did) = exports.def_ids.get(origin_name) {
            def_ids.insert(surface.to_string(), did);
        }
        if let Some(doc) = exports.doc_comments.get(origin_name) {
            doc_comments
                .entry(surface.to_string())
                .or_insert_with(|| doc.clone());
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_type_and_trait_reexports(
    program: &[crate::ast::Decl],
    checker: &Checker,
    bindings: &mut Vec<(String, Scheme)>,
    binding_origins: &mut HashMap<String, String>,
    def_ids: &mut HashMap<String, crate::ast::NodeId>,
    type_constructors: &mut HashMap<String, Vec<String>>,
    type_origins: &mut HashMap<String, String>,
    record_defs: &mut HashMap<String, RecordInfo>,
    traits: &mut HashMap<String, TraitInfo>,
    trait_origins: &mut HashMap<String, String>,
    trait_impls: &mut HashMap<(String, Vec<String>, String), ImplInfo>,
    type_arity: &mut HashMap<String, usize>,
    type_param_kinds: &mut HashMap<String, Vec<crate::ast::Kind>>,
    type_aliases: &mut HashMap<String, TypeAliasInfo>,
    doc_comments: &mut HashMap<String, Vec<String>>,
) {
    for (module_name, item) in public_import_items(program, checker) {
        let Some(exports) = checker.modules.exports.get(&module_name) else {
            continue;
        };
        let origin_name = item.name.as_str();
        let surface = item.surface_name();

        if let Some(&arity) = exports.type_arity.get(origin_name)
            && !type_arity.contains_key(surface)
        {
            type_arity.insert(surface.to_string(), arity);
            let origin = exports
                .type_origins
                .get(origin_name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, origin_name));
            type_origins.insert(surface.to_string(), origin);
            if let Some(kinds) = exports.type_param_kinds.get(origin_name) {
                type_param_kinds.insert(surface.to_string(), kinds.clone());
            }
            if let Some(info) = exports.type_aliases.get(origin_name) {
                type_aliases.insert(surface.to_string(), info.clone());
            }
            if let Some(info) = exports.record_defs.get(origin_name) {
                record_defs.insert(surface.to_string(), info.clone());
            }
            if let Some(ctors) = exports.type_constructors.get(origin_name) {
                let surfaced_ctors: Vec<String> = ctors
                    .iter()
                    .map(|ctor| {
                        if ctor == origin_name {
                            surface.to_string()
                        } else {
                            ctor.clone()
                        }
                    })
                    .collect();
                type_constructors.insert(surface.to_string(), surfaced_ctors);
                for ctor in ctors {
                    let ctor_surface = if ctor == origin_name { surface } else { ctor };
                    if bindings.iter().any(|(name, _)| name == ctor_surface) {
                        continue;
                    }
                    if let Some((_, scheme)) =
                        exports.bindings.iter().find(|(name, _)| name == ctor)
                    {
                        bindings.push((ctor_surface.to_string(), scheme.clone()));
                        let origin = exports
                            .binding_origins
                            .get(ctor)
                            .cloned()
                            .unwrap_or_else(|| format!("{}.{}", module_name, ctor));
                        binding_origins.insert(ctor_surface.to_string(), origin);
                        if let Some(&did) = exports.def_ids.get(ctor) {
                            def_ids.insert(ctor_surface.to_string(), did);
                        }
                    }
                }
            }
            if let Some(doc) = exports.doc_comments.get(origin_name) {
                doc_comments
                    .entry(surface.to_string())
                    .or_insert_with(|| doc.clone());
            }
        }

        if let Some(info) = exports.traits.get(origin_name)
            && !traits.contains_key(surface)
        {
            traits.insert(surface.to_string(), info.clone());
            let origin = exports
                .trait_origins
                .get(origin_name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, origin_name));
            trait_origins.insert(surface.to_string(), origin.clone());
            for (key, impl_info) in &exports.trait_impls {
                if key.0 == origin {
                    trait_impls
                        .entry(key.clone())
                        .or_insert_with(|| impl_info.clone());
                }
            }
            if let Some(doc) = exports.doc_comments.get(origin_name) {
                doc_comments
                    .entry(surface.to_string())
                    .or_insert_with(|| doc.clone());
            }
        }
    }
}

fn collect_effect_and_handler_reexports(
    program: &[crate::ast::Decl],
    checker: &Checker,
    effects: &mut HashMap<String, EffectDefInfo>,
    effect_origins: &mut HashMap<String, String>,
    handlers: &mut HashMap<String, HandlerInfo>,
    handler_origins: &mut HashMap<String, String>,
    doc_comments: &mut HashMap<String, Vec<String>>,
) {
    for (module_name, item) in public_import_items(program, checker) {
        let Some(exports) = checker.modules.exports.get(&module_name) else {
            continue;
        };
        let origin_name = item.name.as_str();
        let surface = item.surface_name();

        if let Some(info) = exports.effects.get(origin_name)
            && !effects.contains_key(surface)
        {
            effects.insert(surface.to_string(), info.clone());
            let origin = exports
                .effect_origins
                .get(origin_name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, origin_name));
            effect_origins.insert(surface.to_string(), origin);
            if let Some(doc) = exports.doc_comments.get(origin_name) {
                doc_comments
                    .entry(surface.to_string())
                    .or_insert_with(|| doc.clone());
            }
        }

        if let Some(info) = exports.handlers.get(origin_name)
            && !handlers.contains_key(surface)
        {
            handlers.insert(surface.to_string(), info.clone());
            let origin = exports
                .handler_origins
                .get(origin_name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, origin_name));
            handler_origins.insert(surface.to_string(), origin);
            if let Some(doc) = exports.doc_comments.get(origin_name) {
                doc_comments
                    .entry(surface.to_string())
                    .or_insert_with(|| doc.clone());
            }
        }
    }
}

fn public_import_items<'a>(
    program: &'a [crate::ast::Decl],
    checker: &'a Checker,
) -> Vec<(String, crate::ast::ExposedItem)> {
    let mut out = Vec::new();
    for decl in program {
        let crate::ast::Decl::Import {
            module_path,
            exposing,
            ..
        } = decl
        else {
            continue;
        };
        let module_name = module_path.join(".");
        match exposing {
            Some(crate::ast::Exposing::Items(items)) => {
                out.extend(
                    items
                        .iter()
                        .filter(|item| item.public)
                        .cloned()
                        .map(|item| (module_name.clone(), item)),
                );
            }
            Some(crate::ast::Exposing::All { public: true, .. }) => {
                if let Some(exports) = checker.modules.exports.get(&module_name) {
                    out.extend(
                        synthesize_all_exposed(exports, true)
                            .into_iter()
                            .map(|item| (module_name.clone(), item)),
                    );
                }
            }
            _ => {}
        }
    }
    out
}

/// Names exported by a module for typechecking purposes.
pub(super) fn public_names_for_tc(
    program: &[crate::ast::Decl],
) -> std::collections::HashSet<String> {
    use crate::ast::Decl;
    let mut names = std::collections::HashSet::new();
    for decl in program {
        match decl {
            Decl::FunSignature {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            Decl::TypeDef {
                public: true,
                opaque,
                name,
                variants,
                ..
            } => {
                names.insert(name.clone());
                if !opaque {
                    for v in variants {
                        names.insert(v.node.name.clone());
                    }
                }
            }
            Decl::TypeAlias {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            Decl::RecordDef {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            Decl::HandlerDef {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            // Trait methods are owned by their `TraitInfo` (and exported via
            // `ModuleExports.traits`), not by the flat public-value namespace.
            // Intentionally not enumerated here.
            _ => {}
        }
    }
    names
}
