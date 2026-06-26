use std::collections::HashSet;

use super::ModuleExports;
use crate::token::Span;
use crate::typechecker::{Scheme, ScopeMap, canonical_join};

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
pub(super) fn synthesize_all_exposed(
    exports: &ModuleExports,
    public: bool,
) -> Vec<crate::ast::ExposedItem> {
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
) -> Result<ScopeMap, String> {
    let mut scope = ScopeMap::default();

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
            .unwrap_or_else(|| canonical_join(module_name, name))
    };
    let type_origin = |name: &str| -> String {
        exports
            .type_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| canonical_join(module_name, name))
    };
    let trait_origin = |name: &str| -> String {
        exports
            .trait_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| canonical_join(module_name, name))
    };
    let effect_origin = |name: &str| -> String {
        exports
            .effect_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| canonical_join(module_name, name))
    };
    let handler_origin = |name: &str| -> String {
        exports
            .handler_origins
            .get(name)
            .cloned()
            .unwrap_or_else(|| canonical_join(module_name, name))
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
        let module_qualified = canonical_join(module_name, trait_name);
        scope
            .traits
            .entry(module_qualified.clone())
            .or_insert_with(|| trait_canonical.clone());
        let alias_prefix = (prefix != module_name).then(|| canonical_join(prefix, trait_name));
        if let Some(alias_trait) = &alias_prefix {
            scope
                .traits
                .entry(alias_trait.clone())
                .or_insert_with(|| trait_canonical.clone());
        }
        // Trait method canonical names live in scope.values so qualified
        // (Module.Trait.method) lookups resolve regardless of exposing.
        for method in &info.methods {
            let method_canonical = canonical_join(&trait_canonical, &method.name);
            scope
                .values
                .entry(method_canonical.clone())
                .or_insert_with(|| method_canonical.clone());
            let module_method = canonical_join(&module_qualified, &method.name);
            scope
                .values
                .entry(module_method)
                .or_insert_with(|| method_canonical.clone());
            if let Some(prefix_canonical) = &alias_prefix {
                let aliased = canonical_join(prefix_canonical, &method.name);
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
        let qualified = canonical_join(module_name, effect_name);
        scope
            .effects
            .entry(qualified)
            .or_insert_with(|| effect_canonical.clone());
        if prefix != module_name {
            let aliased = canonical_join(prefix, effect_name);
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
        let qualified = canonical_join(module_name, handler_name);
        scope
            .handlers
            .entry(qualified)
            .or_insert_with(|| handler_canonical.clone());
        if prefix != module_name {
            let aliased = canonical_join(prefix, handler_name);
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
        let qualified = canonical_join(module_name, name);
        scope
            .values
            .entry(qualified)
            .or_insert_with(|| canonical.clone());
        if prefix != module_name {
            let aliased = canonical_join(prefix, name);
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
                let qualified = canonical_join(module_name, ctor);
                scope
                    .constructors
                    .entry(qualified)
                    .or_insert_with(|| canonical.clone());
                if prefix != module_name {
                    let aliased = canonical_join(prefix, ctor);
                    scope.constructors.entry(aliased).or_insert(canonical);
                }
            }
        }
    }

    // Type names: qualified and aliased -> canonical (always available).
    // Bare entries are added only by an explicit exposing list below.
    for name in exports.type_arity.keys() {
        let type_canonical = type_origin(name);
        scope
            .types
            .entry(type_canonical.clone())
            .or_insert_with(|| type_canonical.clone());
        let qualified = canonical_join(module_name, name);
        scope
            .types
            .entry(qualified)
            .or_insert_with(|| type_canonical.clone());
        if prefix != module_name {
            let aliased = canonical_join(prefix, name);
            scope
                .types
                .entry(aliased)
                .or_insert_with(|| type_canonical.clone());
        }
    }

    // Builtin types (Dict, Set, List, ...) are compiler builtins, not declared
    // in any `.saga` file, so they never appear in `exports.type_arity`. Without
    // this, a qualified reference like `Dict.Dict` (or `Std.Dict.Dict`) finds no
    // scope entry and falls through to the resolver's `name.contains('.')`
    // catch-all, minting a phantom `Type::Con("Dict.Dict", ..)` that is nominally
    // distinct from the real builtin `Std.Dict.Dict` yet prints identically —
    // producing the self-contradictory `expected Dict Int Int, got Dict Int Int`.
    // Register the qualified/aliased forms for any builtin whose canonical
    // home is this module so they resolve to the one true builtin canonical.
    // Bare builtin type entries are added only by an explicit exposing list
    // below, matching normal import visibility rules.
    for (bare, canonical) in crate::typechecker::BUILTIN_TYPE_CANONICAL {
        let Some((owner, _)) = canonical.rsplit_once('.') else {
            continue;
        };
        if owner != module_name {
            continue;
        }
        let canonical = (*canonical).to_string();
        // Canonical/module-qualified form (e.g. `Std.Dict.Dict`).
        scope
            .types
            .entry(canonical.clone())
            .or_insert_with(|| canonical.clone());
        // Aliased form (e.g. `Dict.Dict` when imported `as Dict`).
        if prefix != module_name {
            let aliased = canonical_join(prefix, bare);
            scope
                .types
                .entry(aliased)
                .or_insert_with(|| canonical.clone());
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
                // Builtin types (Dict, Set, ...) are compiler builtins whose
                // canonical home is this module. They aren't in `type_arity`,
                // but exposing them is legitimate — the bare registration above
                // already mapped them to their canonical form.
                if crate::typechecker::BUILTIN_TYPE_CANONICAL
                    .iter()
                    .any(|(bare, canonical)| {
                        *bare == name
                            && canonical.rsplit_once('.').map(|(m, _)| m) == Some(module_name)
                    })
                {
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
