use super::value::{Env, EvalResult, Value};
use crate::ast::Decl;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
    rc::Rc,
};

// --- Module loader ---

#[derive(Clone)]
pub struct ModuleLoader(pub(super) Rc<RefCell<ModuleLoaderInner>>);

pub(super) struct ModuleLoaderInner {
    /// Project root. None = script mode (imports not allowed).
    pub(super) project_root: Option<PathBuf>,
    /// Builtins + prelude, evaluated once. Each module gets extend() of this.
    pub(super) base_env: Env,
    /// Cache: module name -> exported bindings.
    pub(super) loaded: HashMap<String, HashMap<String, Value>>,
    /// Modules currently being loaded (for cycle detection).
    pub(super) loading: HashSet<String>,
}

impl ModuleLoader {
    pub fn script() -> Self {
        ModuleLoader(Rc::new(RefCell::new(ModuleLoaderInner {
            project_root: None,
            base_env: Env::new(),
            loaded: HashMap::new(),
            loading: HashSet::new(),
        })))
    }

    pub fn project(root: PathBuf) -> Self {
        ModuleLoader(Rc::new(RefCell::new(ModuleLoaderInner {
            project_root: Some(root),
            base_env: Env::new(),
            loaded: HashMap::new(),
            loading: HashSet::new(),
        })))
    }
}

/// Collect the names exported by a module (public functions, type constructors,
/// handlers, trait methods, impl dispatch keys).
fn public_names(program: &[Decl]) -> HashSet<String> {
    let mut names = HashSet::new();
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
                    names.insert(format!("__ctor_type_{}", v.name));
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
            Decl::ExternalFun {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            Decl::ImplDef {
                trait_name,
                target_type,
                methods,
                ..
            } => {
                for (method_name, ..) in methods {
                    names.insert(format!(
                        "__impl_{}_{}_{}",
                        trait_name, target_type, method_name
                    ));
                }
            }
            _ => {}
        }
    }
    names
}

/// Verifies that the file on disk has the exact expected case for its name.
fn check_filename_case(file_path: &Path) -> Result<(), String> {
    let dir = file_path.parent().unwrap_or(Path::new("."));
    let expected = match file_path.file_name() {
        Some(n) => n.to_string_lossy().into_owned(),
        None => return Ok(()),
    };
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let actual = entry.file_name().to_string_lossy().into_owned();
            if actual.to_lowercase() == expected.to_lowercase() && actual != expected {
                return Err(format!(
                    "module file '{}' found but expected '{}' -- file name must match module name exactly",
                    actual, expected
                ));
            }
        }
    }
    Ok(())
}

/// Returns the embedded source for a builtin stdlib module, if it exists.
fn builtin_module_source(module_path: &[String]) -> Option<&'static str> {
    if module_path.len() == 2 && module_path[0] == "Std" {
        match module_path[1].as_str() {
            "Maybe"  => Some(include_str!("../prelude/Std/Maybe.dy")),
            "Result" => Some(include_str!("../prelude/Std/Result.dy")),
            "List"   => Some(include_str!("../prelude/Std/List.dy")),
            "Bool"   => Some(include_str!("../prelude/Std/Bool.dy")),
            "Dict"   => Some(include_str!("../prelude/Std/Dict.dy")),
            "Int"    => Some(include_str!("../prelude/Std/Int.dy")),
            "Float"  => Some(include_str!("../prelude/Std/Float.dy")),
            _ => None,
        }
    } else {
        None
    }
}

/// Load, evaluate, and inject a module's public bindings into `env`.
pub(super) fn load_module(
    module_path: &[String],
    alias: Option<&str>,
    exposing: Option<&[crate::ast::ExposedItem]>,
    env: &Env,
    loader: &ModuleLoader,
) -> EvalResult {
    let module_name = module_path.join(".");
    let prefix = alias.unwrap_or(&module_name);

    let is_builtin = builtin_module_source(module_path).is_some();

    let project_root = {
        let inner = loader.0.borrow();
        match &inner.project_root {
            None if !is_builtin => {
                return EvalResult::error(
                    "imports are not supported in script mode (run without a filename to use project mode)",
                );
            }
            Some(root) => Some(root.clone()),
            None => None,
        }
    };

    // Cycle detection
    if loader.0.borrow().loading.contains(&module_name) {
        return EvalResult::error(format!("circular import detected: {}", module_name));
    }

    // Cache hit
    let cached = loader.0.borrow().loaded.get(&module_name).cloned();
    let public_bindings = if let Some(bindings) = cached {
        bindings
    } else {
        // Resolve source: builtin modules are embedded, others read from disk
        let source = if let Some(src) = builtin_module_source(module_path) {
            src.to_string()
        } else {
            let root = project_root.as_ref().unwrap();
            let rel: PathBuf = module_path.iter().collect();
            let file_path = root.join(rel).with_extension("dy");

            if let Err(e) = check_filename_case(&file_path) {
                return EvalResult::error(e);
            }

            match std::fs::read_to_string(&file_path) {
                Ok(s) => s,
                Err(e) => {
                    return EvalResult::error(format!(
                        "cannot read module '{}' ({}): {}",
                        module_name,
                        file_path.display(),
                        e
                    ));
                }
            }
        };

        let tokens = match crate::lexer::Lexer::new(&source).lex() {
            Ok(t) => t,
            Err(e) => {
                return EvalResult::error(format!(
                    "lex error in module '{}': {}",
                    module_name, e.message
                ));
            }
        };
        let program = match crate::parser::Parser::new(tokens).parse_program() {
            Ok(p) => p,
            Err(e) => {
                return EvalResult::error(format!(
                    "parse error in module '{}': {}",
                    module_name, e.message
                ));
            }
        };

        // Mark as loading
        loader.0.borrow_mut().loading.insert(module_name.clone());

        // Builtin Std modules get a fresh env with just builtins (they are
        // the foundation and don't need the prelude). User modules extend
        // loader.base_env which has builtins + prelude.
        let mod_env = if is_builtin {
            let env = Env::new();
            super::register_builtins(&env);
            env
        } else {
            loader.0.borrow().base_env.extend()
        };
        match super::eval_decls(&program, 0, &mod_env, loader) {
            EvalResult::Ok(_) => {}
            EvalResult::Effect { name, .. } => {
                loader.0.borrow_mut().loading.remove(&module_name);
                return EvalResult::error(format!(
                    "unhandled effect '{}' at module level in '{}'",
                    name, module_name
                ));
            }
            other => {
                loader.0.borrow_mut().loading.remove(&module_name);
                return other;
            }
        }

        // Collect public bindings
        let pub_names = public_names(&program);
        let mut bindings = HashMap::new();
        for name in &pub_names {
            if let Some(val) = mod_env.get(name) {
                bindings.insert(name.clone(), val);
            }
        }

        loader.0.borrow_mut().loading.remove(&module_name);
        loader
            .0
            .borrow_mut()
            .loaded
            .insert(module_name.clone(), bindings.clone());
        bindings
    };

    // Inject qualified bindings: Math.abs, Math.max, ...
    let prefix = prefix.to_string();
    for (name, val) in &public_bindings {
        env.set(format!("{}.{}", prefix, name), val.clone());
    }

    // Inject unqualified bindings from exposing list.
    // Capital names are inferred as types: hoist the type + its constructors.
    // Lowercase names are plain values.
    if let Some(exposed) = exposing {
        for name in exposed {
            let is_type = name.starts_with(|c: char| c.is_uppercase());
            if is_type {
                // Hoist the type name itself (if exported)
                let mut found = public_bindings.contains_key(name);
                if let Some(val) = public_bindings.get(name) {
                    env.set(name.clone(), val.clone());
                }
                // Hoist all constructors belonging to this type
                for (k, v) in &public_bindings {
                    if let Some(ctor_name) = k.strip_prefix("__ctor_type_")
                        && let Value::String(owner) = v
                        && owner == name
                        && let Some(ctor_val) = public_bindings.get(ctor_name)
                    {
                        env.set(ctor_name.to_string(), ctor_val.clone());
                        found = true;
                    }
                }
                if !found {
                    return EvalResult::error(format!(
                        "'{}' is not exported by module '{}'",
                        name, module_name
                    ));
                }
            } else {
                match public_bindings.get(name) {
                    Some(val) => env.set(name.clone(), val.clone()),
                    None => {
                        return EvalResult::error(format!(
                            "'{}' is not exported by module '{}'",
                            name, module_name
                        ));
                    }
                }
            }
        }
    }

    EvalResult::Ok(Value::Unit)
}
