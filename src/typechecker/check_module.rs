use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::{Checker, Diagnostic, EffectDef, EffectOpDef, ModuleCodegenInfo, Scheme, Type};
use crate::token::Span;

/// Count the arity of a constructor from its type (number of Arrow/EffArrow levels).
fn ctor_arity(ty: &Type) -> usize {
    match ty {
        Type::Arrow(_, ret) | Type::EffArrow(_, ret, _) => 1 + ctor_arity(ret),
        _ => 0,
    }
}

/// Map from module name (e.g. "Foo.Bar.Baz") to the file path that declares it.
pub type ModuleMap = HashMap<String, PathBuf>;

/// Scan all .dy files under `root`, extract their `module` declarations,
/// and build a map from declared module name to file path.
pub fn scan_project_modules(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    scan_dir(root, root, &mut map)?;
    Ok(map)
}

fn scan_dir(dir: &Path, root: &Path, map: &mut ModuleMap) -> Result<(), String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {}", dir.display(), e))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("read_dir error: {}", e))?;
        let path = entry.path();
        if path.is_dir() {
            // Skip _build and tests directories
            if path.file_name().is_some_and(|n| n == "_build" || n == "tests") {
                continue;
            }
            scan_dir(&path, root, map)?;
        } else if path.extension().is_some_and(|ext| ext == "dy") {
            match extract_module_name(&path) {
                Ok(Some(module_name)) => {
                    if module_name.starts_with("Std.") || module_name == "Std" {
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

/// Extract the module name from a .dy file by lexing and scanning for the
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
pub fn builtin_module_source(module_path: &[String]) -> Option<&'static str> {
    if module_path.len() == 2 && module_path[0] == "Std" {
        match module_path[1].as_str() {
            "Base" => Some(include_str!("../stdlib/Base.dy")),
            "Maybe" => Some(include_str!("../stdlib/Maybe.dy")),
            "Result" => Some(include_str!("../stdlib/Result.dy")),
            "List" => Some(include_str!("../stdlib/List.dy")),
            "Bool" => Some(include_str!("../stdlib/Bool.dy")),
            "Dict" => Some(include_str!("../stdlib/Dict.dy")),
            "Int" => Some(include_str!("../stdlib/Int.dy")),
            "Float" => Some(include_str!("../stdlib/Float.dy")),
            "String" => Some(include_str!("../stdlib/String.dy")),
            "Regex" => Some(include_str!("../stdlib/Regex.dy")),
            "Tuple" => Some(include_str!("../stdlib/Tuple.dy")),
            "Actor" => Some(include_str!("../stdlib/Actor.dy")),
            "Fail" => Some(include_str!("../stdlib/Fail.dy")),
            "Supervisor" => Some(include_str!("../stdlib/Supervisor.dy")),
            "Async" => Some(include_str!("../stdlib/Async.dy")),
            "IO" => Some(include_str!("../stdlib/IO.dy")),
            "Test" => Some(include_str!("../stdlib/Test.dy")),
            _ => None,
        }
    } else {
        None
    }
}

impl Checker {
    // --- Module import typechecking ---

    pub(crate) fn typecheck_import(
        &mut self,
        module_path: &[String],
        alias: Option<&str>,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let module_name = module_path.join(".");
        let prefix = alias
            .map(|a| a.to_string())
            .unwrap_or_else(|| module_path.last().unwrap().to_string());

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

        // Cache hit: inject cached exports
        if let Some(exports) = self.modules.exports.get(&module_name).cloned() {
            return self.inject_exports(&exports, &prefix, exposing, span);
        }

        // Resolve source: builtin modules are embedded, others looked up via module map
        let source = if let Some(src) = builtin_module_source(module_path) {
            src.to_string()
        } else {
            let file_path = self
                .modules
                .map
                .as_ref()
                .and_then(|m| m.get(&module_name))
                .ok_or_else(|| {
                    Diagnostic::error_at(span, format!("unknown module '{}'", module_name))
                })?
                .clone();
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
        crate::derive::expand_derives(&mut program);

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
                // Load prelude (which imports Std first, then stdlib modules)
                let prelude_src = include_str!("../stdlib/prelude.dy");
                let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
                    .lex()
                    .expect("prelude lex error");
                let mut prelude_program = crate::parser::Parser::new(prelude_tokens)
                    .parse_program()
                    .expect("prelude parse error");
                crate::derive::expand_derives(&mut prelude_program);
                snapshot
                    .check_program_inner(&prelude_program)
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
        mod_checker.current_module = Some(module_name.clone());
        mod_checker.check_program_inner(&program).map_err(|errs| {
            Diagnostic::error_at(
                span,
                format!("type error in module '{}': {}", module_name, errs[0]),
            )
        })?;

        // Collect all public exports into a single struct
        let exports = super::ModuleExports::collect(&program, &mod_checker);

        // Cache the CheckResult for elaboration (avoids re-typechecking in compile_std_modules)
        let mod_result = mod_checker.to_result();
        self.modules.check_results.insert(module_name.clone(), mod_result);

        // Advance the parent's var counter past the module's to keep IDs disjoint.
        if mod_checker.next_var > self.next_var {
            self.next_var = mod_checker.next_var;
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

        // Build codegen info from the module's public declarations
        let codegen_info = collect_codegen_info(&module_name, &program, &exports);
        self.modules
            .codegen_info
            .insert(module_name.clone(), codegen_info);

        // Cache and inject
        self.modules
            .exports
            .insert(module_name.clone(), exports.clone());
        let result = self.inject_exports(&exports, &prefix, exposing, span);

        // After loading the base Std module, snapshot trait impls so builtin
        // module checkers inherit Std's impls (e.g. Ord for Int) without
        // inheriting impls from other modules that haven't been loaded yet.
        if module_name == "Std.Base" {
            self.modules.base_trait_impls = self.trait_impls.clone();
        }

        result
    }

    /// Seed a builtin (Std.*) module checker with the parent's trait definitions,
    /// ADT constructors, and trait impls so it can reference prelude-defined types.
    fn seed_builtin_checker(&self, mc: &mut Checker) {
        for (name, info) in &self.traits {
            if !mc.traits.contains_key(name) {
                mc.traits.insert(name.clone(), info.clone());
                for (method_name, _, _) in &info.methods {
                    if let Some(scheme) = self.env.get(method_name)
                        && mc.env.get(method_name).is_none()
                    {
                        mc.env.insert(method_name.clone(), scheme.clone());
                    }
                }
            }
        }
        for (name, scheme) in &self.constructors {
            if !mc.constructors.contains_key(name) {
                mc.constructors.insert(name.clone(), scheme.clone());
                mc.env.insert(name.clone(), scheme.clone());
            }
        }
        for (name, variants) in &self.adt_variants {
            mc.adt_variants.entry(name.clone()).or_insert_with(|| variants.clone());
        }
        // Share base trait impls from Std.dy (e.g. Ord for Int) so stdlib modules
        // can use comparison operators on primitives. Only base impls are shared,
        // not ones accumulated from other module imports (which would cause duplicates).
        for (key, info) in &self.modules.base_trait_impls {
            mc.trait_impls.entry(key.clone()).or_insert_with(|| info.clone());
        }
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
        mc.modules.base_trait_impls = self.modules.base_trait_impls.clone();
        mc
    }

    /// Inject all exports from a module into this checker.
    /// Destructures ModuleExports so adding a new field is a compile error until handled here.
    fn inject_exports(
        &mut self,
        exports: &super::ModuleExports,
        prefix: &str,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let super::ModuleExports {
            bindings,
            type_constructors,
            record_defs,
            traits,
            trait_impls,
            effects,
            handlers,
        } = exports;

        // Traits and their methods (unqualified, so impl bodies can reference them)
        let binding_map: std::collections::HashMap<&str, &Scheme> =
            bindings.iter().map(|(n, s)| (n.as_str(), s)).collect();
        for (name, info) in traits {
            self.traits
                .entry(name.clone())
                .or_insert_with(|| info.clone());
            for (method_name, _, _) in &info.methods {
                if let Some(&scheme) = binding_map.get(method_name.as_str())
                    && self.env.get(method_name).is_none()
                {
                    self.env.insert(method_name.clone(), scheme.clone());
                }
            }
        }

        // Trait impls
        for (key, info) in trait_impls {
            self.trait_impls
                .entry(key.clone())
                .or_insert_with(|| info.clone());
        }

        // Effects
        for (name, info) in effects {
            self.effects
                .entry(name.clone())
                .or_insert_with(|| info.clone());
        }

        // Handlers
        for (name, info) in handlers {
            self.handlers
                .entry(name.clone())
                .or_insert_with(|| info.clone());
        }

        // Bindings, type constructors, records (qualified + exposing)
        self.inject_scoped_bindings(
            bindings,
            type_constructors,
            record_defs,
            prefix,
            exposing,
            span,
        )
    }

    fn inject_scoped_bindings(
        &mut self,
        bindings: &[(String, Scheme)],
        ctors_map: &std::collections::HashMap<String, Vec<String>>,
        record_defs: &std::collections::HashMap<String, Vec<(String, super::Type)>>,
        prefix: &str,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), Diagnostic> {
        // Build a lookup map for fast access
        let binding_map: std::collections::HashMap<&str, &Scheme> =
            bindings.iter().map(|(n, s)| (n.as_str(), s)).collect();

        // Build reverse map: constructor name -> type name (for exposing constructors by name)
        let mut ctor_to_type: std::collections::HashMap<&str, &str> =
            std::collections::HashMap::new();
        for (type_name, ctors) in ctors_map {
            for ctor in ctors {
                ctor_to_type.insert(ctor.as_str(), type_name.as_str());
            }
        }

        for (name, scheme) in bindings {
            self.env
                .insert(format!("{}.{}", prefix, name), scheme.clone());
        }

        // Always inject record definitions for qualified access
        for (rec_name, fields) in record_defs {
            self.records
                .entry(rec_name.clone())
                .or_insert_with(|| fields.clone());
        }

        if let Some(exposed) = exposing {
            for name in exposed {
                let is_type = name.starts_with(|c: char| c.is_uppercase());
                if is_type {
                    let mut found = binding_map.contains_key(name.as_str());
                    // Hoist the type name itself if it's in bindings
                    if let Some(&scheme) = binding_map.get(name.as_str()) {
                        self.env.insert(name.clone(), scheme.clone());
                    }
                    // If it's a record type, register its fields
                    if let Some(fields) = record_defs.get(name.as_str()) {
                        self.records.insert(name.clone(), fields.clone());
                        found = true;
                    }
                    // Hoist all constructors belonging to this type
                    // (for opaque types, ctors is empty but the type name is still valid)
                    if let Some(ctors) = ctors_map.get(name) {
                        found = true;
                        let mut variants = Vec::new();
                        for ctor in ctors {
                            if let Some(&scheme) = binding_map.get(ctor.as_str()) {
                                self.env.insert(ctor.clone(), scheme.clone());
                                self.constructors.insert(ctor.clone(), scheme.clone());
                                variants.push((ctor.clone(), ctor_arity(&scheme.ty)));
                                found = true;
                            }
                        }
                        if !variants.is_empty() {
                            self.adt_variants.insert(name.clone(), variants);
                        }
                    }
                    // If the exposed name is a constructor (not a type), also add to constructors
                    if ctor_to_type.contains_key(name.as_str())
                        && let Some(&scheme) = binding_map.get(name.as_str())
                    {
                        self.env.insert(name.clone(), scheme.clone());
                        self.constructors.insert(name.clone(), scheme.clone());
                        found = true;
                    }
                    if !found {
                        return Err(Diagnostic::error_at(
                            span,
                            format!("'{}' is not exported by module '{}'", name, prefix),
                        ));
                    }
                } else {
                    let qualified = format!("{}.{}", prefix, name);
                    match self.env.get(&qualified).cloned() {
                        Some(scheme) => {
                            self.env.insert(name.clone(), scheme);
                        }
                        None => {
                            return Err(Diagnostic::error_at(
                                span,
                                format!("'{}' is not exported by module '{}'", name, prefix),
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// Collect codegen-relevant info from a module's public declarations.
fn collect_codegen_info(
    module_name: &str,
    program: &[crate::ast::Decl],
    exports: &super::ModuleExports,
) -> ModuleCodegenInfo {
    use crate::ast::Decl;
    let mut effect_defs = Vec::new();
    let mut record_fields = Vec::new();
    let mut handler_defs = Vec::new();
    let mut fun_effects = Vec::new();
    let mut trait_impl_dicts = Vec::new();

    // Erlang module name: "Foo.Bar" -> "foo_bar"
    let erlang_module = module_name
        .split('.')
        .map(|s| s.to_lowercase())
        .collect::<Vec<_>>()
        .join("_");

    for decl in program {
        match decl {
            Decl::EffectDef {
                public: true,
                name,
                type_params,
                operations,
                ..
            } => {
                let ops = operations
                    .iter()
                    .map(|op| EffectOpDef {
                        name: op.name.clone(),
                        param_count: op.params.len(),
                    })
                    .collect();
                effect_defs.push(EffectDef {
                    name: name.clone(),
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
                let field_names: Vec<String> = fields.iter().map(|(n, _)| n.clone()).collect();
                record_fields.push((name.clone(), field_names));
            }
            Decl::HandlerDef {
                public: true,
                name,
                ..
            } => {
                handler_defs.push(name.clone());
            }
            Decl::FunAnnotation {
                public: true,
                name,
                effects,
                ..
            } if !effects.is_empty() => {
                // Strip beam-native effects (same as elaboration)
                let mut sorted: Vec<String> = effects
                    .iter()
                    .map(|e| e.name.clone())
                    .filter(|n| {
                        !matches!(
                            n.as_str(),
                            "Actor" | "Process" | "Monitor" | "Link" | "Timer"
                        )
                    })
                    .collect();
                sorted.sort();
                if !sorted.is_empty() {
                    fun_effects.push((name.clone(), sorted));
                }
            }
            Decl::ImplDef {
                trait_name,
                target_type,
                type_params,
                where_clause,
                ..
            } => {
                let dict_name = format!("__dict_{}_{}_{}", trait_name, erlang_module, target_type);
                let arity = where_clause.iter().map(|b| b.traits.len()).sum::<usize>();
                let var_to_idx: std::collections::HashMap<&str, usize> = type_params
                    .iter()
                    .enumerate()
                    .map(|(i, name)| (name.as_str(), i))
                    .collect();
                let param_constraints: Vec<(String, usize)> = where_clause
                    .iter()
                    .flat_map(|bound| {
                        let idx = var_to_idx.get(bound.type_var.as_str()).copied().unwrap_or(0);
                        bound.traits.iter().map(move |t| (t.clone(), idx))
                    })
                    .collect();
                trait_impl_dicts.push(super::TraitImplDict {
                    trait_name: trait_name.clone(),
                    target_type: target_type.clone(),
                    dict_name,
                    arity,
                    param_constraints,
                });
            }
            _ => {}
        }
    }

    ModuleCodegenInfo {
        exports: exports.bindings.clone(),
        effect_defs,
        record_fields,
        handler_defs,
        fun_effects,
        type_constructors: exports.type_constructors.clone().into_iter().collect(),
        trait_impl_dicts,
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
            Decl::FunAnnotation {
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
                        names.insert(v.name.clone());
                    }
                }
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
            Decl::ExternalFun {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            Decl::TraitDef {
                public: true,
                methods,
                ..
            } => {
                for m in methods {
                    names.insert(m.name.clone());
                }
            }
            _ => {}
        }
    }
    names
}
