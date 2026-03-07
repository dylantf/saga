use super::{Checker, Scheme, TypeError};
use crate::token::Span;

impl Checker {
    // --- Module import typechecking ---

    pub(crate) fn typecheck_import(
        &mut self,
        module_path: &[String],
        alias: Option<&str>,
        exposing: Option<&[String]>,
        span: Span,
    ) -> Result<(), TypeError> {
        let module_name = module_path.join(".");
        let prefix = alias.unwrap_or(&module_name).to_string();

        let project_root = match &self.project_root.clone() {
            None => return Ok(()), // script mode: skip typecheck of imports
            Some(root) => root.clone(),
        };

        if self.tc_loading.contains(&module_name) {
            return Err(TypeError::at(
                span,
                format!("circular import: {}", module_name),
            ));
        }

        // Cache hit: inject cached bindings
        if let Some(cached) = self.tc_loaded.get(&module_name).cloned() {
            self.inject_module_types(&cached, &prefix, exposing, span)?;
            return Ok(());
        }

        // Resolve file path
        let rel: std::path::PathBuf = module_path.iter().collect();
        let file_path = project_root.join(rel).with_extension("dy");

        let source = std::fs::read_to_string(&file_path).map_err(|e| {
            TypeError::at(span, format!("cannot read module '{}': {}", module_name, e))
        })?;

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

        // Run a fresh checker on prelude + module
        let prelude_src = include_str!("../prelude.dy");
        let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
            .lex()
            .expect("prelude lex error");
        let prelude_program = crate::parser::Parser::new(prelude_tokens)
            .parse_program()
            .expect("prelude parse error");

        let mut mod_checker = super::Checker::with_project_root(project_root);
        // Share the module cache so transitive imports benefit from caching
        mod_checker.tc_loaded = self.tc_loaded.clone();
        mod_checker.check_program(&prelude_program).map_err(|e| {
            TypeError::at(
                span,
                format!(
                    "type error in prelude (for module '{}'): {}",
                    module_name, e
                ),
            )
        })?;
        mod_checker.check_program(&program).map_err(|e| {
            TypeError::at(
                span,
                format!("type error in module '{}': {}", module_name, e),
            )
        })?;

        // Determine which names are public
        let pub_names = public_names_for_tc(&program);

        // Collect public type bindings
        let mut public_bindings: Vec<(String, Scheme)> = Vec::new();
        for name in &pub_names {
            if let Some(scheme) = mod_checker.env.get(name) {
                public_bindings.push((name.clone(), scheme.clone()));
            }
        }

        self.tc_loading.remove(&module_name);
        self.tc_loaded
            .insert(module_name.clone(), public_bindings.clone());

        self.inject_module_types(&public_bindings, &prefix, exposing, span)
    }

    fn inject_module_types(
        &mut self,
        bindings: &[(String, Scheme)],
        prefix: &str,
        exposing: Option<&[String]>,
        span: Span,
    ) -> Result<(), TypeError> {
        for (name, scheme) in bindings {
            self.env
                .insert(format!("{}.{}", prefix, name), scheme.clone());
        }
        if let Some(exposed) = exposing {
            for name in exposed {
                let qualified = format!("{}.{}", prefix, name);
                match self.env.get(&qualified).cloned() {
                    Some(scheme) => self.env.insert(name.clone(), scheme),
                    None => {
                        return Err(TypeError::at(
                            span,
                            format!("'{}' is not exported by module '{}'", name, prefix),
                        ));
                    }
                }
            }
        }
        Ok(())
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
                variants,
                ..
            } => {
                for v in variants {
                    names.insert(v.name.clone());
                }
            }
            Decl::HandlerDef {
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
