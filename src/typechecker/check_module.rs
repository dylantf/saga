use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use super::{
    Checker, Diagnostic, EffectDefInfo, HandlerInfo, ImplInfo, RecordInfo, Scheme, TraitInfo, Type,
    TypeAliasInfo,
};
use crate::token::Span;

// --- Module export types ---

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
                        super::arity_keyed_target_name(&resolved_target, type_params.len());
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

/// An effect operation definition for codegen: operation name and parameter count.
#[derive(Debug, Clone)]
pub struct EffectOpDef {
    pub name: String,
    /// Source-level parameter count before erasing `Unit` placeholders.
    pub source_param_count: usize,
    /// Runtime handler arity after erasing `Unit` placeholder parameters.
    pub runtime_param_count: usize,
    /// Indices of source params that survive runtime erasure.
    pub runtime_param_positions: Vec<usize>,
    /// For callback parameters, the effects absorbed by that parameter.
    pub param_absorbed_effects: HashMap<usize, Vec<String>>,
}

/// An effect definition for codegen: effect name, its operations, and type parameter count.
#[derive(Debug, Clone)]
pub struct EffectDef {
    pub name: String,
    pub ops: Vec<EffectOpDef>,
    pub type_param_count: usize,
}

/// A trait impl dict exported by a module.
#[derive(Debug, Clone)]
pub struct TraitImplDict {
    pub trait_name: String,
    /// Extra type arguments applied to the trait (e.g. ["NOK"] in `impl ConvertTo NOK for USD`).
    pub trait_type_args: Vec<String>,
    pub target_type: String,
    /// Module-qualified dict name (e.g. `__dict_Show_animals_Animal`).
    pub dict_name: String,
    /// Number of dict parameters (from where clause).
    pub arity: usize,
    /// Where-clause constraints as (constraint_trait, param_index) pairs.
    /// Used by the elaborator to pass correct sub-dicts for parameterized impls.
    pub param_constraints: Vec<(String, usize)>,
    /// Sorted, canonical effect names declared in the impl's `needs` clause.
    /// Applies uniformly to every method dispatched through this dict — codegen
    /// uses it to thread evidence at trait method call sites that elaborated
    /// to `DictMethodAccess`. Empty when the impl has no `needs` clause.
    pub impl_effects: Vec<String>,
}

/// Information about a module's exports needed by the lowerer/codegen.
/// Populated during typechecking alongside `tc_modules`.
#[derive(Debug, Clone, Default)]
pub struct ModuleCodegenInfo {
    /// Public type bindings: name -> scheme.
    pub exports: Vec<(String, Scheme)>,
    /// Public binding surface name -> canonical origin name.
    pub export_origins: Vec<(String, String)>,
    /// Public effect surface name -> canonical origin effect name.
    pub effect_origins: Vec<(String, String)>,
    /// Public effect definitions.
    pub effect_defs: Vec<EffectDef>,
    /// Public record definitions: record name -> ordered field names.
    pub record_fields: Vec<(String, Vec<String>)>,
    /// Public handler names.
    pub handler_defs: Vec<String>,
    /// Public handler surface name -> canonical origin handler name.
    pub handler_origins: Vec<(String, String)>,
    /// Public function effect annotations: name -> sorted effect names.
    pub fun_effects: Vec<(String, Vec<String>)>,
    /// Public type constructors: type name -> [constructor names].
    pub type_constructors: Vec<(String, Vec<String>)>,
    /// Trait impl dicts exported by this module.
    pub trait_impl_dicts: Vec<TraitImplDict>,
    /// External function mappings: (saga_name, erlang_module, erlang_func, arity).
    /// Includes both public and private externals (private ones are needed for handler inlining).
    pub external_funs: Vec<(String, String, String, usize)>,
    /// Compiler intrinsic exports: source name -> intrinsic id.
    pub intrinsic_exports: Vec<(String, crate::intrinsics::IntrinsicId)>,
}

fn collect_effects_from_fun_type(ty: &Type) -> Vec<String> {
    let mut effects = std::collections::BTreeSet::new();
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        for entry in &row.effects {
            effects.insert(entry.name.clone());
        }
        current = ret;
    }
    effects.into_iter().collect()
}

fn effect_param_absorbed_effects(op: &super::EffectOpSig) -> HashMap<usize, Vec<String>> {
    op.params
        .iter()
        .enumerate()
        .filter_map(|(idx, (_, ty))| {
            let effs = collect_effects_from_fun_type(ty);
            (!effs.is_empty()).then_some((idx, effs))
        })
        .collect()
}

/// Count the arity of a constructor from its type (number of Fun levels).
fn ctor_arity(ty: &Type) -> usize {
    match ty {
        Type::Fun(_, ret, _) => 1 + ctor_arity(ret),
        _ => 0,
    }
}

/// Map from module name (e.g. "Foo.Bar.Baz") to the file path that declares it.
pub type ModuleMap = HashMap<String, PathBuf>;

/// Visibility metadata for a module: which package it originates from and whether
/// it is exposed across the package boundary (listed in `[library] expose`).
#[derive(Debug, Clone)]
pub struct ModuleVisibility {
    pub package: String,
    pub exposed: bool,
}

/// Map from module name to its visibility metadata. Modules without an entry
/// are treated as local (no package, accessible only to other local modules).
pub type ModuleVisibilityMap = HashMap<String, ModuleVisibility>;

/// Scan all .saga files under `root`, extract their `module` declarations,
/// and build a map from declared module name to file path.
pub fn scan_project_modules(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    for entry_point in ["src", "lib"] {
        let dir = root.join(entry_point);
        if dir.is_dir() {
            scan_dir(&dir, root, &mut map, &[], false)?;
        }
    }
    Ok(map)
}

/// Scan a source directory for modules without skipping `tests/` subdirectories.
/// Allows the reserved `Std` namespace, since this is used to render the stdlib's
/// own docs and similar tooling outside the project-validation path.
pub fn scan_source_dir(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    scan_dir(root, root, &mut map, &["_build", "deps"], true)?;
    Ok(map)
}

fn scan_dir(
    dir: &Path,
    root: &Path,
    map: &mut ModuleMap,
    skip_dirs: &[&str],
    allow_std: bool,
) -> Result<(), String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {}", dir.display(), e))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("read_dir error: {}", e))?;
        let path = entry.path();
        if path.is_dir() {
            if path
                .file_name()
                .is_some_and(|n| skip_dirs.iter().any(|s| n == *s))
            {
                continue;
            }
            scan_dir(&path, root, map, skip_dirs, allow_std)?;
        } else if path.extension().is_some_and(|ext| ext == "saga") {
            match extract_module_name(&path) {
                Ok(Some(module_name)) => {
                    if !allow_std && (module_name.starts_with("Std.") || module_name == "Std") {
                        let rel = path.strip_prefix(root).unwrap_or(&path);
                        return Err(format!(
                            "module '{}' in {} uses the reserved `Std` namespace",
                            module_name,
                            rel.display()
                        ));
                    }
                    if let Some(existing) = map.get(&module_name) {
                        return Err(format!(
                            "module '{}' declared in both {} and {}",
                            module_name,
                            existing.display(),
                            path.display()
                        ));
                    }
                    map.insert(module_name, path);
                }
                Ok(None) => {
                    let rel = path.strip_prefix(root).unwrap_or(&path);
                    eprintln!(
                        "warning: {} has no module declaration, skipping",
                        rel.display()
                    );
                }
                Err(e) => {
                    let rel = path.strip_prefix(root).unwrap_or(&path);
                    eprintln!("warning: could not scan {}: {}", rel.display(), e);
                }
            }
        }
    }
    Ok(())
}

/// Extract the module name from a .saga file by lexing and scanning for the
/// first `module` declaration. Returns None if no module declaration is found.
fn extract_module_name(path: &Path) -> Result<Option<String>, String> {
    let source = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
    let tokens = crate::lexer::Lexer::new(&source)
        .lex()
        .map_err(|e| format!("lex error: {}", e.message))?;

    // Scan tokens for: Module UpperIdent (.UpperIdent)*
    use crate::token::Token;
    let mut i = 0;
    while i < tokens.len() {
        if matches!(tokens[i].token, Token::Module) {
            i += 1;
            // Collect the dotted module path
            let mut parts: Vec<String> = Vec::new();
            if i < tokens.len()
                && let Token::UpperIdent(name) = &tokens[i].token
            {
                parts.push(name.clone());
                i += 1;
                while i + 1 < tokens.len() {
                    if matches!(tokens[i].token, Token::Dot) {
                        if let Token::UpperIdent(name) = &tokens[i + 1].token {
                            parts.push(name.clone());
                            i += 2;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
            }
            if !parts.is_empty() {
                return Ok(Some(parts.join(".")));
            }
        }
        i += 1;
    }
    Ok(None)
}

/// Returns the embedded source for a builtin stdlib module, if it exists.
/// All builtin stdlib modules: (module name, source).
pub const BUILTIN_MODULES: &[(&str, &str)] = &[
    ("Std.Base", include_str!("../stdlib/Base.saga")),
    ("Std.Maybe", include_str!("../stdlib/Maybe.saga")),
    ("Std.Result", include_str!("../stdlib/Result.saga")),
    ("Std.List", include_str!("../stdlib/List.saga")),
    ("Std.Bool", include_str!("../stdlib/Bool.saga")),
    ("Std.Dict", include_str!("../stdlib/Dict.saga")),
    ("Std.Int", include_str!("../stdlib/Int.saga")),
    ("Std.Float", include_str!("../stdlib/Float.saga")),
    ("Std.String", include_str!("../stdlib/String.saga")),
    ("Std.Regex", include_str!("../stdlib/Regex.saga")),
    ("Std.Tuple", include_str!("../stdlib/Tuple.saga")),
    ("Std.Actor", include_str!("../stdlib/Actor.saga")),
    ("Std.Fail", include_str!("../stdlib/Fail.saga")),
    ("Std.Control", include_str!("../stdlib/Control.saga")),
    ("Std.Supervisor", include_str!("../stdlib/Supervisor.saga")),
    ("Std.Async", include_str!("../stdlib/Async.saga")),
    ("Std.IO.Unsafe", include_str!("../stdlib/IO.Unsafe.saga")),
    ("Std.IO", include_str!("../stdlib/IO.saga")),
    ("Std.Math", include_str!("../stdlib/Math.saga")),
    ("Std.Test", include_str!("../stdlib/Test.saga")),
    ("Std.Process", include_str!("../stdlib/Process.saga")),
    ("Std.File", include_str!("../stdlib/File.saga")),
    ("Std.Set", include_str!("../stdlib/Set.saga")),
    ("Std.Time", include_str!("../stdlib/Time.saga")),
    ("Std.DateTime", include_str!("../stdlib/DateTime.saga")),
    ("Std.BitString", include_str!("../stdlib/BitString.saga")),
    ("Std.Dynamic", include_str!("../stdlib/Dynamic.saga")),
    ("Std.Ref", include_str!("../stdlib/Ref.saga")),
    ("Std.AtomicRef", include_str!("../stdlib/AtomicRef.saga")),
    ("Std.Vec", include_str!("../stdlib/Vec.saga")),
    ("Std.Stream", include_str!("../stdlib/Stream.saga")),
    ("Std.Array", include_str!("../stdlib/Array.saga")),
    ("Std.Env", include_str!("../stdlib/Env.saga")),
    ("Std.Generic", include_str!("../stdlib/Generic.saga")),
];

pub fn builtin_module_source(module_path: &[String]) -> Option<&'static str> {
    let name = module_path.join(".");
    BUILTIN_MODULES
        .iter()
        .find(|(mod_name, _)| *mod_name == name)
        .map(|(_, src)| *src)
}

impl Checker {
    // --- Module import typechecking ---

    pub(crate) fn typecheck_import(
        &mut self,
        module_path: &[String],
        alias: Option<&str>,
        exposing: Option<&crate::ast::Exposing>,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let module_name = module_path.join(".");
        let prefix = alias
            .map(|a| a.to_string())
            .unwrap_or_else(|| module_path.last().unwrap().to_string());
        let exports = self.load_module(module_path, span)?;
        // Expand `(..)` to an explicit list of every public export so the rest
        // of the import pipeline can treat all-exposing imports as if they had
        // listed every name. This makes `(..)` equivalent by construction.
        let expanded: Option<Vec<crate::ast::ExposedItem>> = match exposing {
            Some(crate::ast::Exposing::All { public, .. }) => {
                Some(synthesize_all_exposed(&exports, *public))
            }
            _ => None,
        };
        let exposing_items: Option<&[crate::ast::ExposedItem]> = match (exposing, &expanded) {
            (None, _) => None,
            (Some(crate::ast::Exposing::Items(items)), _) => Some(items.as_slice()),
            (Some(crate::ast::Exposing::All { .. }), Some(items)) => Some(items.as_slice()),
            (Some(crate::ast::Exposing::All { .. }), None) => unreachable!(),
        };
        self.inject_exports(&exports, &module_name, &prefix, exposing_items, span)
    }

    /// Parse, typecheck, and cache a module without injecting it into the
    /// current checker's scope. Returns the module's exports.
    ///
    /// Used by `typecheck_import` (which then calls `inject_exports`) and by
    /// the auto-load step for canonical-name references (which calls only
    /// `register_module_canonical_exports`).
    pub(crate) fn load_module(
        &mut self,
        module_path: &[String],
        span: Span,
    ) -> Result<ModuleExports, Diagnostic> {
        let module_name = module_path.join(".");

        let is_builtin = builtin_module_source(module_path).is_some();

        let project_root = match &self.modules.project_root.clone() {
            None if !is_builtin => {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "cannot import '{}': user module imports require a project (create a project.toml)",
                        module_name
                    ),
                ));
            }
            Some(root) => Some(root.clone()),
            None => None,
        };

        if self.modules.loading.contains(&module_name) {
            return Err(Diagnostic::error_at(
                span,
                format!("circular import: {}", module_name),
            ));
        }

        // Resolve the module to a file path (or detect that it's a builtin)
        // BEFORE consulting the exports cache. Private modules are only
        // reachable to importers from the same package; doing this check up
        // front prevents the cache from short-circuiting an import that
        // shouldn't be allowed across the package boundary.
        let is_builtin_resolved = builtin_module_source(module_path).is_some();
        let resolved_path: Option<PathBuf> = if is_builtin_resolved {
            None
        } else {
            let importer_pkg = self
                .current_module
                .as_ref()
                .and_then(|m| self.modules.visibility.as_ref()?.get(m))
                .map(|v| v.package.clone());
            let global = self
                .modules
                .map
                .as_ref()
                .and_then(|m| m.get(&module_name))
                .cloned();
            // If the global hit is an exposed module from a different package
            // than the importer, that's fine. If it's a private/internal name
            // (no global hit), fall back to the importer's package private map.
            let path = global.or_else(|| {
                let pkg = importer_pkg.as_ref()?;
                self.modules
                    .private_modules
                    .as_ref()?
                    .get(pkg)?
                    .get(&module_name)
                    .cloned()
            });
            if path.is_none() {
                // Distinguish "doesn't exist" from "exists but private to
                // another package" for a better error message.
                let in_other_package = self.modules.private_modules.as_ref().is_some_and(|pm| {
                    pm.iter().any(|(pkg, m)| {
                        Some(pkg) != importer_pkg.as_ref() && m.contains_key(&module_name)
                    })
                });
                if in_other_package {
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "module '{}' is private to its package and not listed in `expose`",
                            module_name
                        ),
                    ));
                }
                return Err(Diagnostic::error_at(
                    span,
                    format!("unknown module '{}'", module_name),
                ));
            }
            path
        };

        // Cache hit: return cached exports (reachability already verified)
        if let Some(exports) = self.modules.exports.get(&module_name).cloned() {
            return Ok(exports);
        }

        // Resolve source: builtin modules are embedded, others read from the
        // file path resolved above.
        let source = if let Some(src) = builtin_module_source(module_path) {
            src.to_string()
        } else {
            let file_path = resolved_path.expect("non-builtin path resolved above");
            std::fs::read_to_string(&file_path).map_err(|e| {
                Diagnostic::error_at(span, format!("cannot read module '{}': {}", module_name, e))
            })?
        };

        let tokens = crate::lexer::Lexer::new(&source).lex().map_err(|e| {
            Diagnostic::error_at(
                span,
                format!("lex error in module '{}': {}", module_name, e.message),
            )
        })?;
        let mut program = crate::parser::Parser::new(tokens)
            .parse_program()
            .map_err(|e| {
                Diagnostic::error_at(
                    span,
                    format!("parse error in module '{}': {}", module_name, e.message),
                )
            })?;
        let imported = crate::derive::collect_imported_decls(&program, self.modules.map.as_ref());
        crate::derive::expand_derives(&mut program, &imported);
        crate::desugar::desugar_program(&mut program);

        // Cache the parsed program so the build step can skip re-parsing
        self.modules
            .programs
            .insert(module_name.clone(), program.clone());

        self.modules.loading.insert(module_name.clone());

        // Create a module checker. For non-builtin modules, clone the prelude
        // snapshot so we don't re-parse/re-check the prelude for every import.
        // For builtin Std modules, start from a fresh checker with the parent's
        // traits copied in (they can't load the prelude due to circular imports).
        let mut mod_checker = if !is_builtin {
            // Build or reuse the prelude snapshot
            if self.modules.prelude_snapshot.is_none() {
                let mut snapshot = match &project_root {
                    Some(root) => super::Checker::with_project_root(root.clone()),
                    None => super::Checker::new(),
                };
                snapshot.modules.map = self.modules.map.clone();
                snapshot.modules.visibility = self.modules.visibility.clone();
                snapshot.modules.private_modules = self.modules.private_modules.clone();
                // Load prelude (which imports Std first, then stdlib modules)
                let prelude_src = include_str!("../stdlib/prelude.saga");
                let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
                    .lex()
                    .expect("prelude lex error");
                let mut prelude_program = crate::parser::Parser::new(prelude_tokens)
                    .parse_program()
                    .expect("prelude parse error");
                crate::derive::expand_derives(
                    &mut prelude_program,
                    &crate::derive::ImportedDecls::empty(),
                );
                crate::desugar::desugar_program(&mut prelude_program);
                snapshot
                    .check_program_inner(&mut prelude_program)
                    .expect("prelude type errors");
                self.modules.prelude_snapshot = Some(Box::new(snapshot));
            }
            let mut mc = *self.modules.prelude_snapshot.as_ref().unwrap().clone();
            mc.next_var = self.next_var;
            mc
        } else {
            let mut mc = match project_root {
                Some(root) => super::Checker::with_project_root(root),
                None => super::Checker::new(),
            };
            mc.next_var = self.next_var;
            mc.allow_bodyless_annotations = true;
            self.seed_builtin_checker(&mut mc);
            mc
        };
        // Share the module cache so transitive imports benefit from caching
        mod_checker.modules.exports = self.modules.exports.clone();
        mod_checker.modules.codegen_info = self.modules.codegen_info.clone();
        mod_checker.modules.programs = self.modules.programs.clone();
        mod_checker.modules.map = self.modules.map.clone();
        mod_checker.modules.visibility = self.modules.visibility.clone();
        mod_checker.modules.private_modules = self.modules.private_modules.clone();
        // Share the loading set so circular imports are detected across
        // nested typecheck_import calls (child checkers need to see which
        // modules are mid-load in their ancestors).
        mod_checker.modules.loading = self.modules.loading.clone();
        mod_checker.current_module = Some(module_name.clone());
        mod_checker
            .check_program_inner(&mut program)
            .map_err(|errs| {
                Diagnostic::error_at(
                    span,
                    format!("type error in module '{}': {}", module_name, errs[0]),
                )
            })?;

        // Update the stored program with the resolved AST (resolve_names ran during check)
        self.modules
            .programs
            .insert(module_name.clone(), program.clone());

        // Collect all public exports into a single struct
        let exports = ModuleExports::collect(&program, &mod_checker);

        // Cache the CheckResult for elaboration (avoids re-typechecking in compile_std_modules)
        let mod_result = mod_checker.to_result();
        self.modules
            .check_results
            .insert(module_name.clone(), mod_result);

        // Advance the parent's var counter past the module's to keep IDs disjoint.
        if mod_checker.next_var > self.next_var {
            self.next_var = mod_checker.next_var;
        }

        // Inherit kind annotations for type-variable IDs introduced by the
        // module (e.g. symbol-kinded `n` from `type Proxy (n : Symbol) = ...`),
        // so subsequent instantiations of imported schemes preserve kinds.
        for (id, kind) in &mod_checker.var_kinds {
            self.var_kinds.entry(*id).or_insert(*kind);
        }

        // Merge back any caches populated by transitive imports
        for (k, v) in mod_checker.modules.programs {
            self.modules.programs.entry(k).or_insert(v);
        }
        for (k, v) in mod_checker.modules.exports {
            self.modules.exports.entry(k).or_insert(v);
        }
        for (k, v) in mod_checker.modules.codegen_info {
            self.modules.codegen_info.entry(k).or_insert(v);
        }
        for (k, v) in mod_checker.modules.check_results {
            self.modules.check_results.entry(k).or_insert(v);
        }

        self.modules.loading.remove(&module_name);

        // Build codegen info from the module's public declarations.
        // Pass the effects map so fun_effects can use canonical effect names.
        let codegen_info = collect_codegen_info(
            &module_name,
            &program,
            &exports,
            &mod_checker.effects,
            &mod_checker.scope_map,
            &mod_checker.trait_state.traits,
        );
        self.modules
            .codegen_info
            .insert(module_name.clone(), codegen_info);

        // Cache the exports
        self.modules
            .exports
            .insert(module_name.clone(), exports.clone());

        // After loading any Std module, merge its exported impls into the base
        // snapshot so later builtin module checkers inherit impls from all
        // previously loaded Std modules (e.g. Show for String from Std.String).
        // We merge only the module's own exports rather than cloning all of
        // self.trait_state.impls, to avoid leaking user-defined impls into the snapshot.
        if module_name.starts_with("Std.") {
            for (key, info) in &exports.trait_impls {
                self.modules
                    .base_trait_impls
                    .entry(key.clone())
                    .or_insert_with(|| info.clone());
            }
        }

        Ok(exports)
    }

    /// Seed a builtin (Std.*) module checker with the parent's trait definitions,
    /// ADT constructors, and trait impls so it can reference prelude-defined types.
    fn seed_builtin_checker(&self, mc: &mut Checker) {
        for (name, info) in &self.trait_state.traits {
            if !mc.trait_state.traits.contains_key(name) {
                mc.trait_state.traits.insert(name.clone(), info.clone());
                for method in &info.methods {
                    // Copy canonical-keyed entries so use-site lookups
                    // through ResolutionResult find the scheme. Schemes are
                    // sourced from `TraitMethodInfo.scheme` (the authority);
                    // env is the cached canonical-keyed view.
                    for (user, canonical) in &self.scope_map.values {
                        if user == &method.name
                            && canonical != &method.name
                            && mc.env.get(canonical).is_none()
                        {
                            mc.env.insert(canonical.clone(), method.scheme.clone());
                        }
                    }
                }
            }
        }
        for (name, scheme) in &self.constructors {
            if !mc.constructors.contains_key(name) {
                mc.constructors.insert(name.clone(), scheme.clone());
            }
        }
        for (name, variants) in &self.adt_variants {
            mc.adt_variants
                .entry(name.clone())
                .or_insert_with(|| variants.clone());
        }
        // Share trait impls from all previously loaded Std modules so stdlib modules
        // can use traits on standard types (e.g. Show for String, Ord for Int).
        for (key, info) in &self.modules.base_trait_impls {
            mc.trait_state
                .impls
                .entry(key.clone())
                .or_insert_with(|| info.clone());
        }
        // Share scope_map so builtin modules can resolve bare names to canonical forms
        mc.scope_map.merge(&self.scope_map);
    }

    /// Create a module checker seeded with this checker's caches.
    /// Import resolution will be O(1) cache hits. The caller still needs to
    /// call `check_program` to produce per-module `env` and `evidence` for elaboration.
    pub fn seeded_module_checker(
        &self,
        project_root: Option<std::path::PathBuf>,
        is_builtin: bool,
    ) -> Checker {
        let mut mc = if !is_builtin {
            if let Some(ref snapshot) = self.modules.prelude_snapshot {
                let mut mc = *snapshot.clone();
                if let Some(root) = project_root {
                    mc.modules.project_root = Some(root);
                }
                mc
            } else {
                match project_root {
                    Some(root) => super::Checker::with_project_root(root),
                    None => super::Checker::new(),
                }
            }
        } else {
            let mut mc = match project_root {
                Some(root) => super::Checker::with_project_root(root),
                None => super::Checker::new(),
            };
            self.seed_builtin_checker(&mut mc);
            mc
        };
        mc.allow_bodyless_annotations = is_builtin;
        mc.next_var = self.next_var;
        mc.modules.exports = self.modules.exports.clone();
        mc.modules.codegen_info = self.modules.codegen_info.clone();
        mc.modules.programs = self.modules.programs.clone();
        mc.modules.map = self.modules.map.clone();
        mc.modules.visibility = self.modules.visibility.clone();
        mc.modules.private_modules = self.modules.private_modules.clone();
        mc.modules.base_trait_impls = self.modules.base_trait_impls.clone();
        mc
    }

    /// Inject all exports from a module into this checker.
    /// Destructures ModuleExports so adding a new field is a compile error until handled here.
    fn inject_exports(
        &mut self,
        exports: &ModuleExports,
        module_name: &str,
        prefix: &str,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), Diagnostic> {
        self.register_module_canonical_exports(exports, module_name, Some(prefix), exposing);
        self.merge_import_scope(exports, module_name, prefix, exposing, span)
    }

    /// Merge an import's scope_map entries (and exposing-list LSP/records side
    /// effects) into this checker. This is the *scope injection* half of an
    /// import — what makes bare/aliased forms resolvable.
    ///
    /// Auto-loaded modules (referenced only via canonical names) deliberately
    /// skip this step so their bare/alias forms remain unresolvable without an
    /// explicit `import` decl.
    fn merge_import_scope(
        &mut self,
        exports: &ModuleExports,
        module_name: &str,
        prefix: &str,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let import_scope = resolve_import(exports, module_name, prefix, exposing)
            .map_err(|msg| Diagnostic::error_at(span, msg))?;
        self.scope_map.merge(&import_scope);

        // Exposing-list side effects on records/adt_variants/LSP docs.
        // (Validation and scope_map entries are handled by resolve_import above.)
        if let Some(exposed) = exposing {
            let binding_map: std::collections::HashMap<&str, &Scheme> = exports
                .bindings
                .iter()
                .map(|(n, s)| (n.as_str(), s))
                .collect();
            let binding_origin = |name: &str| -> String {
                exports
                    .binding_origins
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| super::canonical_join(module_name, name))
            };
            let type_origin = |name: &str| -> String {
                exports
                    .type_origins
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| super::canonical_join(module_name, name))
            };
            let mut ctor_to_type: std::collections::HashMap<&str, &str> =
                std::collections::HashMap::new();
            for (type_name, ctors) in &exports.type_constructors {
                for ctor in ctors {
                    ctor_to_type.insert(ctor.as_str(), type_name.as_str());
                }
            }

            for item in exposed {
                let name = item.name.as_str();
                let surface = item.surface_name();
                let is_type = name.starts_with(|c: char| c.is_uppercase());
                if is_type {
                    if let Some(fields) = exports.record_defs.get(name) {
                        let record_canonical = type_origin(name);
                        self.records.insert(record_canonical, fields.clone());
                    }
                    if let Some(ctors) = exports.type_constructors.get(name) {
                        let mut variants = Vec::new();
                        for ctor in ctors {
                            if let Some(&scheme) = binding_map.get(ctor.as_str()) {
                                let canonical_ctor = binding_origin(ctor);
                                if let Some(&did) = exports.def_ids.get(ctor.as_str()) {
                                    self.lsp
                                        .constructor_def_ids
                                        .entry(canonical_ctor.clone())
                                        .or_insert(did);
                                }
                                variants.push((canonical_ctor, ctor_arity(&scheme.ty)));
                            }
                        }
                        if !variants.is_empty() {
                            self.adt_variants
                                .entry(surface.to_string())
                                .or_insert(variants);
                        }
                    }
                    if ctor_to_type.contains_key(name)
                        && let Some(&did) = exports.def_ids.get(name)
                    {
                        self.lsp
                            .constructor_def_ids
                            .entry(surface.to_string())
                            .or_insert(did);
                    }
                }
                if let Some(doc) = exports.doc_comments.get(name) {
                    self.lsp
                        .imported_docs
                        .entry(surface.to_string())
                        .or_insert_with(|| doc.clone());
                }
            }
        }

        let _ = span;
        Ok(())
    }

    /// Register a module's exports under canonical keys (env, traits,
    /// trait_impls, effects, handlers, type_arity, constructors, records, etc.).
    ///
    /// This is the *loading* half of an import — what makes canonical names
    /// (`Module.Name`) resolvable. Both explicit imports and the auto-load
    /// step call this; only explicit imports follow up with `merge_import_scope`.
    ///
    /// `prefix` is used purely for aliased-form LSP doc-comment registration
    /// (a no-op for auto-load, where we pass `None`).
    pub(crate) fn register_module_canonical_exports(
        &mut self,
        exports: &ModuleExports,
        module_name: &str,
        prefix: Option<&str>,
        exposing: Option<&[crate::ast::ExposedItem]>,
    ) {
        if !self
            .modules
            .registered_canonical
            .insert(module_name.to_string())
        {
            return;
        }
        let ModuleExports {
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
            type_aliases,
            effectful_funs,
            def_ids,
            doc_comments,
        } = exports;

        // Traits and their methods. The full `Scheme` is owned by
        // `TraitMethodInfo` on the imported module's `TraitInfo` — read it
        // from there directly. `bindings` no longer carries trait methods.
        let binding_map: std::collections::HashMap<&str, &Scheme> =
            bindings.iter().map(|(n, s)| (n.as_str(), s)).collect();
        for (name, info) in traits {
            let trait_canonical = trait_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| super::canonical_join(module_name, name));
            self.trait_state
                .traits
                .entry(trait_canonical.clone())
                .or_insert_with(|| info.clone());
            // Register doc comments for the trait itself
            if let Some(doc) = doc_comments.get(name) {
                self.lsp
                    .imported_docs
                    .entry(name.clone())
                    .or_insert_with(|| doc.clone());
            }
            for method in &info.methods {
                // Canonical name (Module.Trait.method). Use sites resolve
                // through ResolutionResult, which records the canonical
                // form, so `self.env.get(canonical)` is the lookup contract.
                // No bare-name insertion: bare visibility is gated by
                // scope_map.trait_methods and produced by the resolver.
                let canonical = super::canonical_join(&trait_canonical, &method.name);
                if self.env.get(&canonical).is_none() {
                    if let Some(&did) = def_ids.get(method.name.as_str()) {
                        self.env
                            .insert_with_def(canonical, method.scheme.clone(), did);
                    } else {
                        self.env.insert(canonical, method.scheme.clone());
                    }
                }
            }
        }

        // Trait impls
        for (key, info) in trait_impls {
            self.trait_state
                .impls
                .entry(key.clone())
                .or_insert_with(|| info.clone());
        }

        // Effects: always register under both bare and qualified forms in
        // self.effects (the bare form is needed for internal type checking —
        // the type system stores bare effect names in EffectRows). The
        // scope_map controls which names users can write in `needs` clauses.
        let exposed_surface = |item: &str| -> Option<&str> {
            exposing.and_then(|list| {
                list.iter()
                    .find(|e| e.name == item)
                    .map(|e| e.surface_name())
            })
        };
        for (name, info) in effects {
            // One canonical entry: Module.Effect (e.g. Std.Fail.Fail)
            let canonical = effect_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            self.effects
                .entry(canonical)
                .or_insert_with(|| info.clone());
            if let Some(doc) = doc_comments.get(name) {
                self.lsp
                    .imported_docs
                    .entry(name.clone())
                    .or_insert_with(|| doc.clone());
            }
        }

        // Handlers: canonical always, bare only when exposed.
        // Uses module_name (canonical) not prefix (alias), matching effects.
        for (name, info) in handlers {
            let canonical = handler_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            self.handlers
                .entry(canonical)
                .or_insert_with(|| info.clone());
            if let Some(surface) = exposed_surface(name) {
                self.handlers
                    .entry(surface.to_string())
                    .or_insert_with(|| info.clone());
            }
            if let Some(doc) = doc_comments.get(name) {
                self.lsp
                    .imported_docs
                    .entry(name.clone())
                    .or_insert_with(|| doc.clone());
            }
        }

        // Type arities: register under canonical (module-qualified) name
        for (name, arity) in type_arity {
            let canonical = type_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            self.type_arity.entry(canonical).or_insert(*arity);
        }
        for (name, kinds) in type_param_kinds {
            let canonical = type_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            self.type_param_kinds
                .entry(canonical)
                .or_insert_with(|| kinds.clone());
        }

        // Type aliases: register under canonical (module-qualified) name.
        // Body uses the source module's var IDs; that's fine because those
        // ids are only used as positional placeholders during substitution.
        for (name, info) in type_aliases {
            let canonical = type_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            self.type_aliases
                .entry(canonical)
                .or_insert_with(|| info.clone());
        }

        // Function effects (for cross-module `with` validation and effect propagation).
        // Only the canonical form is registered; scope_map resolves aliases/bare names.
        for name in effectful_funs {
            let canonical = binding_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            self.effect_meta.known_funs.insert(canonical);
        }

        // --- Inject bindings, constructors, records into checker state ---

        for (name, scheme) in bindings {
            // Canonical: always register under full module path (e.g. "Std.String.replace")
            let canonical = binding_origins
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, name));
            if let Some(&did) = def_ids.get(name.as_str()) {
                self.env
                    .insert_with_def(canonical.clone(), scheme.clone(), did);
            } else {
                self.env.insert(canonical.clone(), scheme.clone());
            }
            // Doc comments: canonical + aliased forms
            if let Some(doc) = doc_comments.get(name) {
                self.lsp
                    .imported_docs
                    .entry(canonical)
                    .or_insert_with(|| doc.clone());
                if let Some(p) = prefix
                    && p != module_name
                {
                    let aliased = format!("{}.{}", p, name);
                    self.lsp
                        .imported_docs
                        .entry(aliased)
                        .or_insert_with(|| doc.clone());
                }
            }
        }

        // Constructors: canonical form only
        for (type_name, ctors) in type_constructors {
            let mut variants = Vec::new();
            for ctor in ctors {
                let canonical = binding_origins
                    .get(ctor)
                    .cloned()
                    .unwrap_or_else(|| format!("{}.{}", module_name, ctor));
                if let Some(&scheme) = binding_map.get(ctor.as_str()) {
                    self.constructors.insert(canonical.clone(), scheme.clone());
                    if let Some(&did) = def_ids.get(ctor.as_str()) {
                        self.lsp.constructor_def_ids.insert(canonical.clone(), did);
                    }
                    variants.push((canonical, ctor_arity(&scheme.ty)));
                }
            }
            if !self.adt_variants.contains_key(type_name) && !variants.is_empty() {
                self.adt_variants.insert(type_name.clone(), variants);
            }
        }

        // Record definitions (canonical key)
        for (rec_name, fields) in record_defs {
            let canonical = type_origins
                .get(rec_name)
                .cloned()
                .unwrap_or_else(|| format!("{}.{}", module_name, rec_name));
            self.records
                .entry(canonical)
                .or_insert_with(|| fields.clone());
        }

        let _ = exposing;
    }
}

/// Build scope_map entries for a module import.
///
/// This is the name resolution logic: given a module's exports and the import
/// parameters (module name, alias prefix, exposing list), compute all the
/// user-visible-name -> canonical-name mappings.
///
/// Validates that all exposed names actually exist in the module's exports.
/// Returns an error message for the first invalid exposed name found.
///
/// Separated from `inject_exports` so name resolution can eventually run as
/// an independent pass before typechecking.
/// Synthesize the explicit `ExposedItem` list equivalent to `(..)` for the
/// given module's exports. Includes every public value binding, type and
/// record name (with their constructors flowing through the existing types
/// branch in `resolve_import`), trait, effect, and handler.
fn synthesize_all_exposed(exports: &ModuleExports, public: bool) -> Vec<crate::ast::ExposedItem> {
    let mut items: Vec<crate::ast::ExposedItem> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    let push =
        |name: &str, items: &mut Vec<crate::ast::ExposedItem>, seen: &mut HashSet<String>| {
            if seen.insert(name.to_string()) {
                items.push(crate::ast::ExposedItem {
                    name: name.to_string(),
                    alias: None,
                    public,
                    span: Span { start: 0, end: 0 },
                });
            }
        };

    // Bindings (values + bare constructors that live in the values namespace)
    for (name, _) in &exports.bindings {
        push(name, &mut items, &mut seen);
    }
    // Types — the items-branch in resolve_import auto-walks the constructors
    // for each exposed type name, so adding the type name alone is enough.
    for name in exports.type_constructors.keys() {
        push(name, &mut items, &mut seen);
    }
    for name in exports.record_defs.keys() {
        push(name, &mut items, &mut seen);
    }
    for name in exports.traits.keys() {
        push(name, &mut items, &mut seen);
    }
    for name in exports.effects.keys() {
        push(name, &mut items, &mut seen);
    }
    for name in exports.handlers.keys() {
        push(name, &mut items, &mut seen);
    }
    items
}

pub(super) fn resolve_import(
    exports: &ModuleExports,
    module_name: &str,
    prefix: &str,
    exposing: Option<&[crate::ast::ExposedItem]>,
) -> Result<super::ScopeMap, String> {
    let mut scope = super::ScopeMap::default();

    let binding_map: std::collections::HashMap<&str, &Scheme> = exports
        .bindings
        .iter()
        .map(|(n, s)| (n.as_str(), s))
        .collect();
    let binding_origin = |name: &str| -> String {
        exports
            .binding_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| super::canonical_join(module_name, name))
    };
    let type_origin = |name: &str| -> String {
        exports
            .type_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| super::canonical_join(module_name, name))
    };
    let trait_origin = |name: &str| -> String {
        exports
            .trait_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| super::canonical_join(module_name, name))
    };
    let effect_origin = |name: &str| -> String {
        exports
            .effect_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| super::canonical_join(module_name, name))
    };
    let handler_origin = |name: &str| -> String {
        exports
            .handler_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| super::canonical_join(module_name, name))
    };

    // Build reverse map: constructor name -> type name
    let mut ctor_to_type: std::collections::HashMap<&str, &str> = std::collections::HashMap::new();
    for (type_name, ctors) in &exports.type_constructors {
        for ctor in ctors {
            ctor_to_type.insert(ctor.as_str(), type_name.as_str());
        }
    }

    // Traits: canonical + aliased qualified forms always available.
    // Bare entries (and bare trait method visibility) are only added when
    // there is no exposing clause; an explicit exposing list adds bare
    // entries for the named traits below.
    for (trait_name, info) in &exports.traits {
        let trait_canonical = trait_origin(trait_name);
        scope
            .traits
            .entry(trait_canonical.clone())
            .or_insert_with(|| trait_canonical.clone());
        let module_qualified = super::canonical_join(module_name, trait_name);
        scope
            .traits
            .entry(module_qualified.clone())
            .or_insert_with(|| trait_canonical.clone());
        let alias_prefix =
            (prefix != module_name).then(|| super::canonical_join(prefix, trait_name));
        if let Some(alias_trait) = &alias_prefix {
            scope
                .traits
                .entry(alias_trait.clone())
                .or_insert_with(|| trait_canonical.clone());
        }
        // Trait method canonical names live in scope.values so qualified
        // (Module.Trait.method) lookups resolve regardless of exposing.
        for method in &info.methods {
            let method_canonical = super::canonical_join(&trait_canonical, &method.name);
            scope
                .values
                .entry(method_canonical.clone())
                .or_insert_with(|| method_canonical.clone());
            let module_method = super::canonical_join(&module_qualified, &method.name);
            scope
                .values
                .entry(module_method)
                .or_insert_with(|| method_canonical.clone());
            if let Some(prefix_canonical) = &alias_prefix {
                let aliased = super::canonical_join(prefix_canonical, &method.name);
                scope.values.entry(aliased).or_insert(method_canonical);
            }
        }
        if exposing.is_none() {
            scope
                .traits
                .entry(trait_name.clone())
                .or_insert_with(|| trait_canonical.clone());
            scope.register_trait_methods(
                &trait_canonical,
                info.methods.iter().map(|m| m.name.as_str()),
            );
        }
    }

    // Effects: canonical + aliased qualified forms
    for effect_name in exports.effects.keys() {
        let effect_canonical = effect_origin(effect_name);
        scope
            .effects
            .entry(effect_canonical.clone())
            .or_insert_with(|| effect_canonical.clone());
        let qualified = super::canonical_join(module_name, effect_name);
        scope
            .effects
            .entry(qualified)
            .or_insert_with(|| effect_canonical.clone());
        if prefix != module_name {
            let aliased = super::canonical_join(prefix, effect_name);
            scope.effects.entry(aliased).or_insert(effect_canonical);
        }
    }

    // Handlers: canonical + aliased qualified forms
    for handler_name in exports.handlers.keys() {
        let handler_canonical = handler_origin(handler_name);
        scope
            .handlers
            .entry(handler_canonical.clone())
            .or_insert_with(|| handler_canonical.clone());
        let qualified = super::canonical_join(module_name, handler_name);
        scope
            .handlers
            .entry(qualified)
            .or_insert_with(|| handler_canonical.clone());
        if prefix != module_name {
            let aliased = super::canonical_join(prefix, handler_name);
            scope.handlers.entry(aliased).or_insert(handler_canonical);
        }
    }

    // Value bindings: canonical + aliased
    for (name, _) in &exports.bindings {
        let canonical = binding_origin(name);
        scope
            .values
            .entry(canonical.clone())
            .or_insert_with(|| canonical.clone());
        let qualified = super::canonical_join(module_name, name);
        scope
            .values
            .entry(qualified)
            .or_insert_with(|| canonical.clone());
        if prefix != module_name {
            let aliased = super::canonical_join(prefix, name);
            scope.values.entry(aliased).or_insert(canonical);
        }
    }

    // Constructors: canonical + aliased
    for ctors in exports.type_constructors.values() {
        for ctor in ctors {
            if binding_map.contains_key(ctor.as_str()) {
                let canonical = binding_origin(ctor);
                scope
                    .constructors
                    .entry(canonical.clone())
                    .or_insert_with(|| canonical.clone());
                let qualified = super::canonical_join(module_name, ctor);
                scope
                    .constructors
                    .entry(qualified)
                    .or_insert_with(|| canonical.clone());
                if prefix != module_name {
                    let aliased = super::canonical_join(prefix, ctor);
                    scope.constructors.entry(aliased).or_insert(canonical);
                }
            }
        }
    }

    // Type names: qualified and aliased -> canonical (always available)
    // Bare entries are only added when there is no exposing clause
    // (i.e. `import Foo` makes all types available, but `import Foo (Bar)`
    // only makes `Bar` available as a bare name).
    for name in exports.type_arity.keys() {
        let type_canonical = type_origin(name);
        scope
            .types
            .entry(type_canonical.clone())
            .or_insert_with(|| type_canonical.clone());
        let qualified = super::canonical_join(module_name, name);
        scope
            .types
            .entry(qualified)
            .or_insert_with(|| type_canonical.clone());
        if prefix != module_name {
            let aliased = super::canonical_join(prefix, name);
            scope
                .types
                .entry(aliased)
                .or_insert_with(|| type_canonical.clone());
        }
        if exposing.is_none() {
            scope
                .types
                .entry(name.clone())
                .or_insert_with(|| type_canonical);
        }
    }

    // Exposed items: bare -> canonical, with validation
    if let Some(exposed) = exposing {
        for item in exposed {
            let name = item.name.as_str();
            let surface = item.surface_name();
            let is_type = name.starts_with(|c: char| c.is_uppercase());
            if is_type {
                let mut found = binding_map.contains_key(name);
                // Bare type value -> canonical
                if found {
                    let type_canonical = binding_origin(name);
                    scope
                        .values
                        .entry(surface.to_string())
                        .or_insert(type_canonical);
                }
                // Bare type name resolves to canonical
                let type_canonical = type_origin(name);
                scope
                    .types
                    .entry(surface.to_string())
                    .or_insert(type_canonical);
                if exports.type_arity.contains_key(name) {
                    found = true;
                }
                // Record types count as found
                if exports.record_defs.contains_key(name) {
                    found = true;
                }
                // Constructors belonging to this type
                if let Some(ctors) = exports.type_constructors.get(name) {
                    found = true;
                    for ctor in ctors {
                        if binding_map.contains_key(ctor.as_str()) {
                            let ctor_canonical = binding_origin(ctor);
                            scope
                                .constructors
                                .entry(ctor.clone())
                                .or_insert_with(|| ctor_canonical.clone());
                            scope.values.entry(ctor.clone()).or_insert(ctor_canonical);
                        }
                    }
                }
                // Exposed constructor-as-name
                if ctor_to_type.contains_key(name) && binding_map.contains_key(name) {
                    let ctor_canonical = binding_origin(name);
                    scope
                        .constructors
                        .entry(surface.to_string())
                        .or_insert_with(|| ctor_canonical.clone());
                    scope
                        .values
                        .entry(surface.to_string())
                        .or_insert(ctor_canonical);
                    found = true;
                }
                // Effects can be exposed by name
                if let Some(info) = exports.effects.get(name) {
                    let effect_canonical = effect_origin(name);
                    scope
                        .effects
                        .entry(surface.to_string())
                        .or_insert(effect_canonical.clone());
                    scope.register_effect_ops(
                        &effect_canonical,
                        info.ops.iter().map(|op| op.name.as_str()),
                    );
                    found = true;
                }
                // Traits can be exposed by name
                if let Some(info) = exports.traits.get(name) {
                    let trait_canonical = trait_origin(name);
                    scope
                        .traits
                        .entry(surface.to_string())
                        .or_insert(trait_canonical.clone());
                    scope.register_trait_methods(
                        &trait_canonical,
                        info.methods.iter().map(|m| m.name.as_str()),
                    );
                    found = true;
                }
                if !found {
                    return Err(format!("'{}' is not exported by module '{}'", name, prefix));
                }
            } else {
                // Bare value -> canonical
                let canonical = binding_origin(name);
                // Validate: must be a function/value in scope, or a handler
                // name. Trait method canonical entries also live in
                // scope.values (so qualified Module.Trait.method resolves),
                // but they are not exposable by bare method name — exposing a
                // method requires exposing its trait. Reject any name that
                // matches a method of an exported trait.
                let is_handler = exports.handlers.contains_key(name);
                let is_trait_method = exports
                    .traits
                    .values()
                    .any(|info| info.methods.iter().any(|m| m.name == name));
                if (is_trait_method || !binding_map.contains_key(name)) && !is_handler {
                    return Err(format!("'{}' is not exported by module '{}'", name, prefix));
                }
                if binding_map.contains_key(name) {
                    scope.values.entry(surface.to_string()).or_insert(canonical);
                }
                if is_handler {
                    let handler_canonical = handler_origin(name);
                    scope
                        .handlers
                        .entry(surface.to_string())
                        .or_insert(handler_canonical);
                }
            }
        }
    }

    // Record origins: every canonical name from this module maps to module_name.
    // Collect all canonical names from the maps we just built.
    let module = module_name.to_string();
    for canonical in scope.values.values() {
        scope
            .origins
            .entry(canonical.clone())
            .or_insert_with(|| module.clone());
    }
    for canonical in scope.handlers.values() {
        scope
            .origins
            .entry(canonical.clone())
            .or_insert_with(|| module.clone());
    }
    for canonical in scope.constructors.values() {
        scope
            .origins
            .entry(canonical.clone())
            .or_insert_with(|| module.clone());
    }
    for canonical in scope.effects.values() {
        scope
            .origins
            .entry(canonical.clone())
            .or_insert_with(|| module.clone());
    }
    for canonical in scope.traits.values() {
        scope
            .origins
            .entry(canonical.clone())
            .or_insert_with(|| module.clone());
    }
    // Types use bare canonical names, but still originate from this module
    for bare_name in scope.types.values() {
        scope
            .origins
            .entry(bare_name.clone())
            .or_insert_with(|| module.clone());
    }

    Ok(scope)
}

/// Collect codegen-relevant info from a module's public declarations.
fn collect_codegen_info(
    module_name: &str,
    program: &[crate::ast::Decl],
    exports: &ModuleExports,
    effects_map: &std::collections::HashMap<String, EffectDefInfo>,
    scope_map: &super::ScopeMap,
    traits_map: &std::collections::HashMap<String, super::TraitInfo>,
) -> ModuleCodegenInfo {
    use crate::ast::Decl;
    fn is_runtime_unit_param(ty: &crate::ast::TypeExpr) -> bool {
        match ty {
            crate::ast::TypeExpr::Named { name, .. } => {
                super::canonicalize_type_name(name) == super::canonicalize_type_name("Unit")
            }
            crate::ast::TypeExpr::Labeled { inner, .. } => is_runtime_unit_param(inner),
            _ => false,
        }
    }

    let canonical_type_name = |name: &str| -> String {
        scope_map
            .resolve_type(name)
            .map(|s| s.to_string())
            .unwrap_or_else(|| super::canonicalize_type_name(name).to_string())
    };

    let canonical_trait_type_args = |args: &[String]| -> Vec<String> {
        args.iter()
            .map(|arg| {
                if arg.starts_with(|c: char| c.is_uppercase()) || arg.contains('.') {
                    canonical_type_name(arg)
                } else {
                    arg.clone()
                }
            })
            .collect()
    };

    let mut effect_defs = Vec::new();
    let mut record_fields = Vec::new();
    let mut handler_defs = Vec::new();
    let mut fun_effects = Vec::new();
    let mut trait_impl_dicts = Vec::new();
    let mut external_funs = Vec::new();
    let mut intrinsic_exports = Vec::new();

    // Erlang module name: "Foo.Bar" -> "foo_bar"
    let erlang_module = module_name
        .split('.')
        .map(|s| s.to_lowercase())
        .collect::<Vec<_>>()
        .join("_");

    for decl in program {
        match decl {
            Decl::EffectDef {
                name,
                type_params,
                operations,
                ..
            } => {
                let canonical_effect = format!("{}.{}", module_name, name);
                let effect_info = effects_map
                    .get(&canonical_effect)
                    .unwrap_or_else(|| panic!("missing effect info for {canonical_effect}"));
                let ops = operations
                    .iter()
                    .map(|op| EffectOpDef {
                        name: op.node.name.clone(),
                        source_param_count: op.node.params.len(),
                        runtime_param_positions: op
                            .node
                            .params
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, (_, ty))| {
                                (!is_runtime_unit_param(ty)).then_some(idx)
                            })
                            .collect(),
                        runtime_param_count: op
                            .node
                            .params
                            .iter()
                            .filter(|(_, ty)| !is_runtime_unit_param(ty))
                            .count(),
                        param_absorbed_effects: effect_info
                            .ops
                            .iter()
                            .find(|sig| sig.name == op.node.name)
                            .map(effect_param_absorbed_effects)
                            .unwrap_or_default(),
                    })
                    .collect();
                // Codegen metadata is internal compiler state, so keep effect
                // op counts even for private effects. Public functions can
                // still `needs {PrivateEffect}`, and imported call sites need
                // the effect's runtime op arity to thread handler callbacks.
                effect_defs.push(EffectDef {
                    name: canonical_effect,
                    ops,
                    type_param_count: type_params.len(),
                });
            }
            Decl::RecordDef {
                public: true,
                name,
                fields,
                ..
            } => {
                let field_names: Vec<String> = fields.iter().map(|f| f.node.0.clone()).collect();
                record_fields.push((name.clone(), field_names));
            }
            Decl::HandlerDef {
                public: true, name, ..
            } => {
                handler_defs.push(format!("{}.{}", module_name, name));
            }
            Decl::FunSignature {
                public: true,
                name,
                effects,
                ..
            } if !effects.is_empty() => {
                // Strip beam-native effects (same as elaboration), canonicalize names
                let mut sorted: Vec<String> = effects
                    .iter()
                    .filter(|e| {
                        !matches!(
                            e.name.as_str(),
                            "Actor" | "Process" | "Monitor" | "Link" | "Timer"
                        )
                    })
                    .map(|e| {
                        // Resolve effect name to canonical via scope_map
                        scope_map
                            .resolve_effect(&e.name)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| {
                                // Fallback: try effects_map directly, or qualify with module
                                if effects_map.contains_key(&e.name) {
                                    e.name.clone()
                                } else {
                                    format!("{}.{}", module_name, e.name)
                                }
                            })
                    })
                    .collect();
                sorted.sort();
                if !sorted.is_empty() {
                    fun_effects.push((name.clone(), sorted));
                }
            }
            Decl::FunSignature {
                name,
                params,
                annotations,
                ..
            } => {
                if annotations.iter().any(|a| a.name == "builtin") {
                    let canonical = format!("{}.{}", module_name, name);
                    let intrinsic = crate::intrinsics::intrinsic_id_for_canonical_name(&canonical)
                        .unwrap_or_else(|| {
                            panic!("@builtin declaration has no IntrinsicId mapping: {canonical}")
                        });
                    intrinsic_exports.push((name.clone(), intrinsic));
                }
                // Collect @external annotations for both public and private functions.
                // Private externals are needed for handler body inlining.
                if let Some(ext) = annotations.iter().find(|a| a.name == "external")
                    && ext.args.len() >= 3
                    && let (
                        crate::ast::Lit::String(erl_mod, _),
                        crate::ast::Lit::String(erl_func, _),
                    ) = (&ext.args[1], &ext.args[2])
                {
                    external_funs.push((
                        name.clone(),
                        erl_mod.clone(),
                        erl_func.clone(),
                        params.len(),
                    ));
                }
            }
            Decl::ImplDef {
                trait_name,
                trait_type_args,
                target_type,
                type_params,
                where_clause,
                needs,
                methods,
                routed_derive_info,
                ..
            } => {
                // Resolve trait name to canonical form via scope_map
                let canonical_trait = scope_map
                    .resolve_trait(trait_name)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("{}.{}", module_name, trait_name));
                let trait_type_arg_names: Vec<String> = trait_type_args
                    .iter()
                    .map(|te| {
                        // Use the head name of an App chain so parameterized
                        // Rep types like `Rep__Box a` reduce to `Rep__Box`
                        // for the dict-name key.
                        let head = te.head_name().unwrap_or("");
                        match te {
                            crate::ast::TypeExpr::Var { name, .. } => name.clone(),
                            _ => scope_map
                                .resolve_type(head)
                                .map(|s| s.to_string())
                                .unwrap_or_else(|| canonical_type_name(head)),
                        }
                    })
                    .collect();
                let canonical_trait_type_args = canonical_trait_type_args(&trait_type_arg_names);
                let canonical_target_type = canonical_type_name(target_type);
                let canonical_target_type =
                    super::arity_keyed_target_name(&canonical_target_type, type_params.len());
                let dict_name = super::make_dict_name(
                    &canonical_trait,
                    &canonical_trait_type_args,
                    &erlang_module,
                    &canonical_target_type,
                );
                let arity = where_clause.iter().map(|b| b.traits.len()).sum::<usize>();
                let var_to_idx: std::collections::HashMap<&str, usize> = type_params
                    .iter()
                    .enumerate()
                    .map(|(i, tp)| (tp.name.as_str(), i))
                    .collect();
                let param_constraints: Vec<(String, usize)> = where_clause
                    .iter()
                    .flat_map(|bound| {
                        let idx = var_to_idx
                            .get(bound.type_var.as_str())
                            .copied()
                            .unwrap_or(0);
                        bound.traits.iter().map(move |tr| {
                            let resolved = scope_map
                                .resolve_trait(&tr.name)
                                .unwrap_or(tr.name.as_str())
                                .to_string();
                            (resolved, idx)
                        })
                    })
                    .collect();
                let mut impl_effects: Vec<String> = needs
                    .iter()
                    .map(|e| {
                        scope_map
                            .resolve_effect(&e.name)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| e.name.clone())
                    })
                    .collect();
                // Routed-derive impls are synthesized with `needs: vec![]`.
                // Source the impl's effect set from the trait method
                // signatures' canonical effect_sigs instead.
                if routed_derive_info.is_some()
                    && let Some(info) = traits_map.get(&canonical_trait)
                {
                    for trait_method in &info.methods {
                        if methods.iter().any(|m| m.node.name == trait_method.name) {
                            impl_effects.extend(trait_method.effect_sig.effects.iter().cloned());
                        }
                    }
                }
                impl_effects.sort();
                impl_effects.dedup();
                trait_impl_dicts.push(TraitImplDict {
                    trait_name: canonical_trait,
                    trait_type_args: canonical_trait_type_args,
                    target_type: canonical_target_type,
                    dict_name,
                    arity,
                    param_constraints,
                    impl_effects,
                });
            }
            _ => {}
        }
    }

    ModuleCodegenInfo {
        exports: exports.bindings.clone(),
        export_origins: exports
            .binding_origins
            .iter()
            .map(|(surface, origin)| (surface.clone(), origin.clone()))
            .collect(),
        effect_origins: exports
            .effect_origins
            .iter()
            .map(|(surface, origin)| (surface.clone(), origin.clone()))
            .collect(),
        effect_defs,
        record_fields,
        handler_defs,
        handler_origins: exports
            .handler_origins
            .iter()
            .map(|(surface, origin)| (surface.clone(), origin.clone()))
            .collect(),
        fun_effects,
        type_constructors: exports.type_constructors.clone().into_iter().collect(),
        trait_impl_dicts,
        external_funs,
        intrinsic_exports,
    }
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
