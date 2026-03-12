use super::{Checker, EffectDef, EffectOpDef, ModuleCodegenInfo, Scheme, TypeError};
use crate::token::Span;

/// Returns the embedded source for a builtin stdlib module, if it exists.
fn builtin_module_source(module_path: &[String]) -> Option<&'static str> {
    if module_path.len() == 2 && module_path[0] == "Std" {
        match module_path[1].as_str() {
            "Maybe" => Some(include_str!("../prelude/Std/Maybe.dy")),
            "Result" => Some(include_str!("../prelude/Std/Result.dy")),
            "List" => Some(include_str!("../prelude/Std/List.dy")),
            "Bool" => Some(include_str!("../prelude/Std/Bool.dy")),
            _ => None,
        }
    } else {
        None
    }
}

/// Maps type names to their constructor names, for `type T` hoist support.
fn type_constructors(
    program: &[crate::ast::Decl],
) -> std::collections::HashMap<String, Vec<String>> {
    use crate::ast::Decl;
    let mut map = std::collections::HashMap::new();
    for decl in program {
        match decl {
            Decl::TypeDef {
                public: true,
                name,
                variants,
                ..
            } => {
                let ctors: Vec<String> = variants.iter().map(|v| v.name.clone()).collect();
                map.insert(name.clone(), ctors);
            }
            Decl::RecordDef {
                public: true, name, ..
            } => {
                // Records use their name as the constructor atom
                map.insert(name.clone(), vec![name.clone()]);
            }
            _ => {}
        }
    }
    map
}

impl Checker {
    // --- Module import typechecking ---

    pub(crate) fn typecheck_import(
        &mut self,
        module_path: &[String],
        alias: Option<&str>,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), TypeError> {
        let module_name = module_path.join(".");
        let prefix = alias.unwrap_or(&module_name).to_string();

        let is_builtin = builtin_module_source(module_path).is_some();

        let project_root = match &self.project_root.clone() {
            None if !is_builtin => return Ok(()), // script mode: skip non-builtin imports
            Some(root) => Some(root.clone()),
            None => None,
        };

        if self.tc_loading.contains(&module_name) {
            return Err(TypeError::at(
                span,
                format!("circular import: {}", module_name),
            ));
        }

        // Cache hit: inject cached bindings
        if let Some(cached) = self.tc_loaded.get(&module_name).cloned() {
            let cached_ctors = self
                .tc_type_ctors
                .get(&module_name)
                .cloned()
                .unwrap_or_default();
            let cached_records = self
                .tc_record_defs
                .get(&module_name)
                .cloned()
                .unwrap_or_default();
            // Inject cached trait impls
            if let Some(cached_impls) = self.tc_trait_impls.get(&module_name).cloned() {
                for (key, info) in &cached_impls {
                    self.trait_impls
                        .entry(key.clone())
                        .or_insert_with(|| info.clone());
                }
            }
            self.inject_module_types(
                &cached,
                &cached_ctors,
                &cached_records,
                &prefix,
                exposing,
                span,
            )?;
            return Ok(());
        }

        // Resolve source: builtin modules are embedded, others read from disk
        let source = if let Some(src) = builtin_module_source(module_path) {
            src.to_string()
        } else {
            let root = project_root.as_ref().unwrap();
            let rel: std::path::PathBuf = module_path.iter().collect();
            let file_path = root.join(rel).with_extension("dy");
            std::fs::read_to_string(&file_path).map_err(|e| {
                TypeError::at(span, format!("cannot read module '{}': {}", module_name, e))
            })?
        };

        let tokens = crate::lexer::Lexer::new(&source).lex().map_err(|e| {
            TypeError::at(
                span,
                format!("lex error in module '{}': {}", module_name, e.message),
            )
        })?;
        let program = crate::parser::Parser::new(tokens)
            .parse_program()
            .map_err(|e| {
                TypeError::at(
                    span,
                    format!("parse error in module '{}': {}", module_name, e.message),
                )
            })?;

        self.tc_loading.insert(module_name.clone());

        let mut mod_checker = match project_root {
            Some(root) => super::Checker::with_project_root(root),
            None => super::Checker::new(),
        };
        // Start the module checker's var IDs after the parent's current counter
        // to avoid var ID collisions when module schemes are injected into the parent.
        mod_checker.next_var = self.next_var;
        // Share the module cache so transitive imports benefit from caching
        mod_checker.tc_loaded = self.tc_loaded.clone();
        mod_checker.tc_type_ctors = self.tc_type_ctors.clone();
        mod_checker.tc_codegen_info = self.tc_codegen_info.clone();
        mod_checker.tc_record_defs = self.tc_record_defs.clone();
        mod_checker.tc_trait_impls = self.tc_trait_impls.clone();

        // Run a fresh checker on prelude + module.
        // Builtin Std modules skip the prelude to avoid circular imports
        // (the prelude itself imports Std modules).
        if !is_builtin {
            let prelude_src = include_str!("../prelude/prelude.dy");
            let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
                .lex()
                .expect("prelude lex error");
            let prelude_program = crate::parser::Parser::new(prelude_tokens)
                .parse_program()
                .expect("prelude parse error");
            mod_checker.check_program(&prelude_program).map_err(|e| {
                TypeError::at(
                    span,
                    format!(
                        "type error in prelude (for module '{}'): {}",
                        module_name, e
                    ),
                )
            })?;
        }
        mod_checker.check_program(&program).map_err(|e| {
            TypeError::at(
                span,
                format!("type error in module '{}': {}", module_name, e),
            )
        })?;

        // Determine which names are public
        let pub_names = public_names_for_tc(&program);
        let ctors_map = type_constructors(&program);

        // Collect public type bindings (from env; constructors are in mod_checker.constructors)
        let mut public_bindings: Vec<(String, Scheme)> = Vec::new();
        for name in &pub_names {
            // Check env first, then constructors
            if let Some(scheme) = mod_checker.env.get(name) {
                public_bindings.push((name.clone(), scheme.clone()));
            } else if let Some(scheme) = mod_checker.constructors.get(name) {
                public_bindings.push((name.clone(), scheme.clone()));
            }
        }

        // Collect public record definitions from the module checker
        let mut pub_records: std::collections::HashMap<String, Vec<(String, super::Type)>> =
            std::collections::HashMap::new();
        for decl in &program {
            if let crate::ast::Decl::RecordDef {
                public: true, name, ..
            } = decl
                && let Some(fields) = mod_checker.records.get(name.as_str())
            {
                pub_records.insert(name.clone(), fields.clone());
            }
        }

        // Collect the module's own trait impls (from ImplDef declarations in the source).
        let mut module_trait_impls: std::collections::HashMap<(String, String), super::ImplInfo> =
            std::collections::HashMap::new();
        for decl in &program {
            if let crate::ast::Decl::ImplDef {
                trait_name,
                target_type,
                ..
            } = decl
            {
                let key = (trait_name.clone(), target_type.clone());
                if let Some(info) = mod_checker.trait_impls.get(&key) {
                    module_trait_impls.insert(key, info.clone());
                }
            }
        }

        // Advance the parent's var counter past the module's to keep IDs disjoint.
        if mod_checker.next_var > self.next_var {
            self.next_var = mod_checker.next_var;
        }

        self.tc_loading.remove(&module_name);
        self.tc_loaded
            .insert(module_name.clone(), public_bindings.clone());
        self.tc_type_ctors
            .insert(module_name.clone(), ctors_map.clone());
        self.tc_record_defs
            .insert(module_name.clone(), pub_records.clone());
        self.tc_trait_impls
            .insert(module_name.clone(), module_trait_impls.clone());

        // Build codegen info from the module's public declarations
        let codegen_info = collect_codegen_info(&module_name, &program, &public_bindings);
        self.tc_codegen_info
            .insert(module_name.clone(), codegen_info);

        // Inject the module's trait impls into the parent checker
        for (key, info) in &module_trait_impls {
            self.trait_impls
                .entry(key.clone())
                .or_insert_with(|| info.clone());
        }

        self.inject_module_types(
            &public_bindings,
            &ctors_map,
            &pub_records,
            &prefix,
            exposing,
            span,
        )
    }

    fn inject_module_types(
        &mut self,
        bindings: &[(String, Scheme)],
        ctors_map: &std::collections::HashMap<String, Vec<String>>,
        record_defs: &std::collections::HashMap<String, Vec<(String, super::Type)>>,
        prefix: &str,
        exposing: Option<&[crate::ast::ExposedItem]>,
        span: Span,
    ) -> Result<(), TypeError> {
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
                    if let Some(ctors) = ctors_map.get(name) {
                        for ctor in ctors {
                            if let Some(&scheme) = binding_map.get(ctor.as_str()) {
                                self.env.insert(ctor.clone(), scheme.clone());
                                self.constructors.insert(ctor.clone(), scheme.clone());
                                found = true;
                            }
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
                        return Err(TypeError::at(
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
                            return Err(TypeError::at(
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
    public_bindings: &[(String, Scheme)],
) -> ModuleCodegenInfo {
    use crate::ast::Decl;
    let mut effect_defs = Vec::new();
    let mut record_fields = Vec::new();
    let mut handler_defs = Vec::new();
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
                public: true, name, ..
            } => {
                handler_defs.push(name.clone());
            }
            Decl::ImplDef {
                trait_name,
                target_type,
                where_clause,
                ..
            } => {
                let dict_name = format!("__dict_{}_{}_{}", trait_name, erlang_module, target_type);
                let arity = where_clause.iter().map(|b| b.traits.len()).sum::<usize>();
                trait_impl_dicts.push((trait_name.clone(), target_type.clone(), dict_name, arity));
            }
            _ => {}
        }
    }

    let type_ctors = type_constructors(program);

    ModuleCodegenInfo {
        exports: public_bindings.to_vec(),
        effect_defs,
        record_fields,
        handler_defs,
        type_constructors: type_ctors.into_iter().collect(),
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
                name,
                variants,
                ..
            } => {
                names.insert(name.clone());
                for v in variants {
                    names.insert(v.name.clone());
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
