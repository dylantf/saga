use std::path::PathBuf;

use super::{Checker, Diagnostic, Scheme};
use crate::token::Span;

mod codegen_info;
mod exports;
mod graph;
mod header;
mod header_lsp;
mod header_register;
mod header_scope;
mod import_scope;
mod scan;
mod scc;

pub use codegen_info::{EffectDef, EffectOpDef, ModuleCodegenInfo, TraitImplDict};
pub use exports::ModuleExports;
pub use graph::*;
pub use header::*;
pub use scan::{
    BUILTIN_MODULES, ModuleMap, ModuleVisibility, ModuleVisibilityMap, builtin_module_source,
    scan_project_modules, scan_source_dir,
};

use codegen_info::{collect_codegen_info, ctor_arity};
use header_scope::resolve_header_import;
use import_scope::{resolve_import, synthesize_all_exposed};

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

        if let Some(headers) = &self.modules.active_scc_headers
            && headers.contains_key(&module_name)
        {
            let header_exposing = exposing.map(HeaderExposing::from_ast);
            let import_scope =
                resolve_header_import(headers, &module_name, &prefix, header_exposing.as_ref())
                    .map_err(|msg| Diagnostic::error_at(span, msg))?;
            self.merge_header_lsp_scope(&import_scope);
            self.scope_map.merge(&import_scope);
            return Ok(());
        }

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
                format!(
                    "internal error: module '{module_name}' is already loading outside the active import SCC"
                ),
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

        if !is_builtin
            && self.modules.active_scc_headers.is_none()
            && let Some(component) = self
                .cyclic_component_containing(&module_name)
                .map_err(|msg| Diagnostic::error_at(span, msg))?
        {
            self.load_module_scc(&component, span)?;
            return self
                .modules
                .exports
                .get(&module_name)
                .cloned()
                .ok_or_else(|| {
                    Diagnostic::error_at(
                        span,
                        format!("internal error: SCC did not produce exports for '{module_name}'"),
                    )
                });
        }

        // Resolve source: builtin modules are embedded, others read from the
        // file path resolved above.
        let source = if let Some(src) = builtin_module_source(module_path) {
            src.to_string()
        } else {
            let file_path = resolved_path.expect("non-builtin path resolved above");
            self.module_source(&file_path).map_err(|e| {
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
        let imported = crate::derive::collect_imported_decls_with_sources(
            &program,
            self.modules.map.as_ref(),
            &self.modules.source_overlay,
        );
        crate::derive::expand_derives(&mut program, &imported);
        crate::desugar::desugar_program(&mut program);

        self.modules
            .programs
            .insert(module_name.clone(), program.clone());

        self.modules.loading.insert(module_name.clone());

        let mut mod_checker = if !is_builtin {
            self.ensure_prelude_snapshot(&project_root);
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
        mod_checker.modules.module_graph = self.modules.module_graph.clone();
        mod_checker.modules.source_overlay = self.modules.source_overlay.clone();
        mod_checker.modules.visibility = self.modules.visibility.clone();
        mod_checker.modules.private_modules = self.modules.private_modules.clone();
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

    fn ensure_prelude_snapshot(&mut self, project_root: &Option<PathBuf>) {
        if self.modules.prelude_snapshot.is_some() {
            return;
        }
        let mut snapshot = match project_root {
            Some(root) => super::Checker::with_project_root(root.clone()),
            None => super::Checker::new(),
        };
        snapshot.modules.map = self.modules.map.clone();
        snapshot.modules.module_graph = self.modules.module_graph.clone();
        snapshot.modules.source_overlay = self.modules.source_overlay.clone();
        snapshot.modules.visibility = self.modules.visibility.clone();
        snapshot.modules.private_modules = self.modules.private_modules.clone();
        let prelude_src = include_str!("../stdlib/prelude.saga");
        let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
            .lex()
            .expect("prelude lex error");
        let mut prelude_program = crate::parser::Parser::new(prelude_tokens)
            .parse_program()
            .expect("prelude parse error");
        crate::derive::expand_derives(&mut prelude_program, &crate::derive::ImportedDecls::empty());
        crate::desugar::desugar_program(&mut prelude_program);
        snapshot
            .check_program_inner(&mut prelude_program)
            .expect("prelude type errors");
        self.modules.prelude_snapshot = Some(Box::new(snapshot));
    }

    fn load_module_scc(&mut self, modules: &[String], span: Span) -> Result<(), Diagnostic> {
        let project_root = self.modules.project_root.clone();
        self.ensure_prelude_snapshot(&project_root);

        let mut programs: std::collections::HashMap<String, crate::ast::Program> =
            std::collections::HashMap::new();
        let module_map = self.modules.map.clone().ok_or_else(|| {
            Diagnostic::error_at(span, "internal error: SCC loading requires a module map")
        })?;

        for module_name in modules {
            if self.modules.exports.contains_key(module_name) {
                continue;
            }
            let path = module_map.get(module_name).ok_or_else(|| {
                Diagnostic::error_at(
                    span,
                    format!("unknown module '{}' in import cycle", module_name),
                )
            })?;
            let source = self.module_source(path).map_err(|e| {
                Diagnostic::error_at(span, format!("cannot read module '{}': {}", module_name, e))
            })?;
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
            let imported = crate::derive::collect_imported_decls_with_sources(
                &program,
                self.modules.map.as_ref(),
                &self.modules.source_overlay,
            );
            crate::derive::expand_derives(&mut program, &imported);
            crate::desugar::desugar_program(&mut program);
            self.modules
                .programs
                .insert(module_name.clone(), program.clone());
            programs.insert(module_name.clone(), program);
        }

        let headers: std::collections::HashMap<String, ModuleHeader> = programs
            .iter()
            .map(|(module, program)| (module.clone(), ModuleHeader::from_program(program)))
            .collect();

        for module_name in modules {
            self.modules.loading.insert(module_name.clone());
        }

        let mut checked_modules = Vec::new();
        for module_name in modules {
            if self.modules.exports.contains_key(module_name) {
                continue;
            }
            let mut program = programs
                .remove(module_name)
                .expect("SCC program missing for uncached module");
            let mut mod_checker = self.seeded_module_checker(project_root.clone(), false);
            mod_checker.modules.active_scc_headers = Some(headers.clone());
            mod_checker.modules.loading = self.modules.loading.clone();
            mod_checker.current_module = Some(module_name.clone());
            if let Err(errors) = mod_checker.check_program_inner(&mut program) {
                for module in modules {
                    self.modules.loading.remove(module);
                }
                return Err(Diagnostic::error_at(
                    span,
                    format!("type error in module '{}': {}", module_name, errors[0]),
                ));
            }

            if mod_checker.next_var > self.next_var {
                self.next_var = mod_checker.next_var;
            }
            for (id, kind) in &mod_checker.var_kinds {
                self.var_kinds.entry(*id).or_insert(*kind);
            }
            for (k, v) in &mod_checker.modules.programs {
                self.modules.programs.entry(k.clone()).or_insert(v.clone());
            }
            for (k, v) in &mod_checker.modules.exports {
                self.modules.exports.entry(k.clone()).or_insert(v.clone());
            }
            for (k, v) in &mod_checker.modules.codegen_info {
                self.modules
                    .codegen_info
                    .entry(k.clone())
                    .or_insert(v.clone());
            }
            for (k, v) in &mod_checker.modules.check_results {
                self.modules
                    .check_results
                    .entry(k.clone())
                    .or_insert(v.clone());
            }
            checked_modules.push((module_name.clone(), program, mod_checker));
        }

        for _ in 0..=checked_modules.len() {
            for (module_name, program, mod_checker) in &mut checked_modules {
                mod_checker.modules.exports = self.modules.exports.clone();
                let exports = ModuleExports::collect(program, mod_checker);
                self.modules.exports.insert(module_name.clone(), exports);
            }
        }

        for (module_name, program, mod_checker) in checked_modules {
            let exports = self
                .modules
                .exports
                .get(&module_name)
                .cloned()
                .ok_or_else(|| {
                    Diagnostic::error_at(
                        span,
                        format!("internal error: missing finalized exports for '{module_name}'"),
                    )
                })?;
            self.modules
                .programs
                .insert(module_name.clone(), program.clone());
            self.modules
                .check_results
                .insert(module_name.clone(), mod_checker.to_result());
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
            self.modules.exports.insert(module_name.clone(), exports);
        }

        for module in modules {
            self.modules.loading.remove(module);
        }
        Ok(())
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
        mc.modules.module_graph = self.modules.module_graph.clone();
        mc.modules.source_overlay = self.modules.source_overlay.clone();
        mc.modules.visibility = self.modules.visibility.clone();
        mc.modules.private_modules = self.modules.private_modules.clone();
        mc.modules.base_trait_impls = self.modules.base_trait_impls.clone();
        mc
    }

    fn module_source(&self, path: &std::path::Path) -> std::io::Result<String> {
        self.modules
            .source_overlay
            .get(path)
            .cloned()
            .map(Ok)
            .unwrap_or_else(|| std::fs::read_to_string(path))
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
            inlinable_constructors,
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

        // Private-type constructors referenced by inlined default-method
        // bodies. Registered by canonical name only — never surfaced in scope —
        // so privacy holds for ordinary references.
        for (type_canonical, ctors) in inlinable_constructors {
            let mut variants = Vec::new();
            for (ctor_canonical, scheme) in ctors {
                self.constructors
                    .entry(ctor_canonical.clone())
                    .or_insert_with(|| scheme.clone());
                variants.push((ctor_canonical.clone(), ctor_arity(&scheme.ty)));
            }
            if !self.adt_variants.contains_key(type_canonical) && !variants.is_empty() {
                self.adt_variants.insert(type_canonical.clone(), variants);
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
