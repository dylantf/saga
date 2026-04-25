use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use super::{
    Checker, Diagnostic, EffectDefInfo, HandlerInfo, ImplInfo, RecordInfo, Scheme, ScopeMap,
    TraitInfo, Type,
};
use crate::token::Span;

// --- Module export types ---

/// All public items exported by a typechecked module, cached as a single unit.
#[derive(Debug, Clone, Default)]
pub struct ModuleExports {
    /// Public type bindings: name -> scheme.
    pub bindings: Vec<(String, Scheme)>,
    /// Type name -> constructor names (empty vec for opaque types).
    pub type_constructors: HashMap<String, Vec<String>>,
    /// Record name -> record info (type params + field types).
    pub record_defs: HashMap<String, RecordInfo>,
    /// Trait name -> trait info.
    pub traits: HashMap<String, TraitInfo>,
    /// (trait_name, trait_type_args, target_type) -> impl info.
    pub trait_impls: HashMap<(String, Vec<String>, String), ImplInfo>,
    /// Effect name -> effect def info.
    pub effects: HashMap<String, EffectDefInfo>,
    /// Handler name -> handler info.
    pub handlers: HashMap<String, HandlerInfo>,
    /// Type name -> declared parameter count (for arity checking across modules).
    pub type_arity: HashMap<String, usize>,
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
        let mut def_ids: HashMap<String, crate::ast::NodeId> = HashMap::new();
        for name in &pub_names {
            if let Some(scheme) = checker.env.get(name) {
                bindings.push((name.to_string(), scheme.clone()));
                if let Some(did) = checker.env.def_id(name) {
                    def_ids.insert(name.to_string(), did);
                }
            } else if let Some(scheme) = checker.constructors.get(name) {
                bindings.push((name.to_string(), scheme.clone()));
                if let Some(&did) = checker.lsp.constructor_def_ids.get(name) {
                    def_ids.insert(name.to_string(), did);
                }
            }
        }

        // Type constructors
        let mut type_constructors: HashMap<String, Vec<String>> = HashMap::new();
        for decl in program {
            match decl {
                Decl::TypeDef {
                    public: true,
                    opaque,
                    name,
                    variants,
                    ..
                } => {
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
                    type_constructors.insert(name.clone(), vec![name.clone()]);
                }
                _ => {}
            }
        }

        // Records, traits, trait impls, effects, handlers: all from AST + checker state
        let mut record_defs: HashMap<String, RecordInfo> = HashMap::new();
        let mut traits: HashMap<String, TraitInfo> = HashMap::new();
        let mut trait_impls: HashMap<(String, Vec<String>, String), ImplInfo> = HashMap::new();
        let mut effects: HashMap<String, EffectDefInfo> = HashMap::new();
        let mut handlers: HashMap<String, HandlerInfo> = HashMap::new();

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
                    }
                }
                Decl::ImplDef {
                    id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    ..
                } => {
                    let resolved_trait = checker.resolved_impl_trait_name(*id, trait_name);
                    let resolved_target = checker.resolved_impl_target_type_name(*id, target_type);
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
                    }
                }
                _ => {}
            }
        }

        // Collect type arities for all exported types.
        // The checker stores type_arity under canonical names, but exports use bare names.
        let mut type_arity: HashMap<String, usize> = HashMap::new();
        let module_prefix = checker.current_module.as_deref().unwrap_or("");
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
                Decl::Val {
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

        ModuleExports {
            bindings,
            type_constructors,
            record_defs,
            traits,
            trait_impls,
            effects,
            handlers,
            type_arity,
            effectful_funs,
            def_ids,
            doc_comments,
        }
    }
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
}

/// Information about a module's exports needed by the lowerer/codegen.
/// Populated during typechecking alongside `tc_modules`.
#[derive(Debug, Clone, Default)]
pub struct ModuleCodegenInfo {
    /// Public type bindings: name -> scheme.
    pub exports: Vec<(String, Scheme)>,
    /// Public effect definitions.
    pub effect_defs: Vec<EffectDef>,
    /// Public record definitions: record name -> ordered field names.
    pub record_fields: Vec<(String, Vec<String>)>,
    /// Public handler names.
    pub handler_defs: Vec<String>,
    /// Public function effect annotations: name -> sorted effect names.
    pub fun_effects: Vec<(String, Vec<String>)>,
    /// Public type constructors: type name -> [constructor names].
    pub type_constructors: Vec<(String, Vec<String>)>,
    /// Trait impl dicts exported by this module.
    pub trait_impl_dicts: Vec<TraitImplDict>,
    /// External function mappings: (saga_name, erlang_module, erlang_func, arity).
    /// Includes both public and private externals (private ones are needed for handler inlining).
    pub external_funs: Vec<(String, String, String, usize)>,
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

/// Scan all .saga files under `root`, extract their `module` declarations,
/// and build a map from declared module name to file path.
pub fn scan_project_modules(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    scan_dir(root, root, &mut map, &["_build", "deps", "tests"])?;
    Ok(map)
}

/// Scan a source directory for modules without skipping `tests/` subdirectories.
pub fn scan_source_dir(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    scan_dir(root, root, &mut map, &["_build", "deps"])?;
    Ok(map)
}

fn scan_dir(
    dir: &Path,
    root: &Path,
    map: &mut ModuleMap,
    skip_dirs: &[&str],
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
            scan_dir(&path, root, map, skip_dirs)?;
        } else if path.extension().is_some_and(|ext| ext == "saga") {
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
    ("Std.Array", include_str!("../stdlib/Array.saga")),
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
            return self.inject_exports(&exports, &module_name, &prefix, exposing, span);
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
                // Load prelude (which imports Std first, then stdlib modules)
                let prelude_src = include_str!("../stdlib/prelude.saga");
                let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
                    .lex()
                    .expect("prelude lex error");
                let mut prelude_program = crate::parser::Parser::new(prelude_tokens)
                    .parse_program()
                    .expect("prelude parse error");
                crate::derive::expand_derives(&mut prelude_program);
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
        );
        self.modules
            .codegen_info
            .insert(module_name.clone(), codegen_info);

        // Cache and inject
        self.modules
            .exports
            .insert(module_name.clone(), exports.clone());
        let result = self.inject_exports(&exports, &module_name, &prefix, exposing, span);

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

        result
    }

    /// Seed a builtin (Std.*) module checker with the parent's trait definitions,
    /// ADT constructors, and trait impls so it can reference prelude-defined types.
    fn seed_builtin_checker(&self, mc: &mut Checker) {
        for (name, info) in &self.trait_state.traits {
            if !mc.trait_state.traits.contains_key(name) {
                mc.trait_state.traits.insert(name.clone(), info.clone());
                for (method_name, _, _, _) in &info.methods {
                    if let Some(scheme) = self.env.get(method_name) {
                        if mc.env.get(method_name).is_none() {
                            mc.env.insert(method_name.clone(), scheme.clone());
                        }
                        // Also copy canonical name entries so the resolve pass
                        // can rewrite bare Var names to canonical form.
                        for (user, canonical) in &self.scope_map.values {
                            if user == method_name
                                && canonical != method_name
                                && mc.env.get(canonical).is_none()
                            {
                                mc.env.insert(canonical.clone(), scheme.clone());
                            }
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
        // Build and merge scope_map from the standalone resolver
        let import_scope = resolve_import(exports, module_name, prefix, exposing)
            .map_err(|msg| Diagnostic::error_at(span, msg))?;
        self.scope_map.merge(&import_scope);

        let ModuleExports {
            bindings,
            type_constructors,
            record_defs,
            traits,
            trait_impls,
            effects,
            handlers,
            type_arity,
            effectful_funs,
            def_ids,
            doc_comments,
        } = exports;

        // Traits and their methods: registered under both bare name (for local
        // impl bodies) and canonical name (for the resolve pass to rewrite to).
        let binding_map: std::collections::HashMap<&str, &Scheme> =
            bindings.iter().map(|(n, s)| (n.as_str(), s)).collect();
        for (name, info) in traits {
            let trait_canonical = format!("{}.{}", module_name, name);
            self.trait_state
                .traits
                .entry(trait_canonical)
                .or_insert_with(|| info.clone());
            // Register doc comments for the trait itself
            if let Some(doc) = doc_comments.get(name) {
                self.lsp
                    .imported_docs
                    .entry(name.clone())
                    .or_insert_with(|| doc.clone());
            }
            for (method_name, _, _, _) in &info.methods {
                if let Some(&scheme) = binding_map.get(method_name.as_str()) {
                    // Bare name (for local references and impl bodies)
                    if self.env.get(method_name).is_none() {
                        if let Some(&did) = def_ids.get(method_name.as_str()) {
                            self.env
                                .insert_with_def(method_name.clone(), scheme.clone(), did);
                        } else {
                            self.env.insert(method_name.clone(), scheme.clone());
                        }
                    }
                    // Canonical name (Module.Trait.method) for after resolve pass rewrites
                    let canonical = format!("{}.{}.{}", module_name, name, method_name);
                    if self.env.get(&canonical).is_none() {
                        self.env.insert(canonical, scheme.clone());
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
        let is_exposed =
            |item: &str| -> bool { exposing.is_some_and(|list| list.iter().any(|e| e == item)) };
        for (name, info) in effects {
            // One canonical entry: Module.Effect (e.g. Std.Fail.Fail)
            let canonical = format!("{}.{}", module_name, name);
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
            let canonical = format!("{}.{}", module_name, name);
            self.handlers
                .entry(canonical)
                .or_insert_with(|| info.clone());
            if is_exposed(name) {
                self.handlers
                    .entry(name.clone())
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
            let canonical = format!("{}.{}", module_name, name);
            self.type_arity.entry(canonical).or_insert(*arity);
        }

        // Function effects (for cross-module `with` validation and effect propagation).
        // Only the canonical form is registered; scope_map resolves aliases/bare names.
        for name in effectful_funs {
            let canonical = format!("{}.{}", module_name, name);
            self.effect_meta.known_funs.insert(canonical);
        }

        // --- Inject bindings, constructors, records into checker state ---

        for (name, scheme) in bindings {
            // Canonical: always register under full module path (e.g. "Std.String.replace")
            let canonical = format!("{}.{}", module_name, name);
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
                if prefix != module_name {
                    let aliased = format!("{}.{}", prefix, name);
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
                let canonical = format!("{}.{}", module_name, ctor);
                if let Some(&scheme) = binding_map.get(ctor.as_str()) {
                    self.constructors.insert(canonical.clone(), scheme.clone());
                    if let Some(&did) = def_ids.get(ctor.as_str()) {
                        self.lsp.constructor_def_ids.insert(canonical, did);
                    }
                    variants.push((ctor.clone(), ctor_arity(&scheme.ty)));
                }
            }
            if !self.adt_variants.contains_key(type_name) && !variants.is_empty() {
                self.adt_variants.insert(type_name.clone(), variants);
            }
        }

        // Record definitions (canonical key)
        for (rec_name, fields) in record_defs {
            let canonical = format!("{}.{}", module_name, rec_name);
            self.records
                .entry(canonical)
                .or_insert_with(|| fields.clone());
        }

        // Exposed items: LSP metadata, records, adt_variants.
        // Validation and scope_map entries are handled by resolve_import above.
        if let Some(exposed) = exposing {
            // Build reverse map for constructor-as-name detection
            let mut ctor_to_type: std::collections::HashMap<&str, &str> =
                std::collections::HashMap::new();
            for (type_name, ctors) in type_constructors {
                for ctor in ctors {
                    ctor_to_type.insert(ctor.as_str(), type_name.as_str());
                }
            }

            for name in exposed {
                let is_type = name.starts_with(|c: char| c.is_uppercase());
                if is_type {
                    if let Some(fields) = record_defs.get(name.as_str()) {
                        let record_canonical = format!("{}.{}", module_name, name);
                        self.records.insert(record_canonical, fields.clone());
                    }
                    if let Some(ctors) = type_constructors.get(name) {
                        let mut variants = Vec::new();
                        for ctor in ctors {
                            if let Some(&scheme) = binding_map.get(ctor.as_str()) {
                                if let Some(&did) = def_ids.get(ctor.as_str()) {
                                    self.lsp
                                        .constructor_def_ids
                                        .entry(ctor.clone())
                                        .or_insert(did);
                                }
                                variants.push((ctor.clone(), ctor_arity(&scheme.ty)));
                            }
                        }
                        if !variants.is_empty() {
                            self.adt_variants.insert(name.clone(), variants);
                        }
                    }
                    if ctor_to_type.contains_key(name.as_str())
                        && let Some(&did) = def_ids.get(name.as_str())
                    {
                        self.lsp
                            .constructor_def_ids
                            .entry(name.clone())
                            .or_insert(did);
                    }
                }
                if let Some(doc) = doc_comments.get(name.as_str()) {
                    self.lsp
                        .imported_docs
                        .entry(name.clone())
                        .or_insert_with(|| doc.clone());
                }
            }
        }

        Ok(())
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

    // Build reverse map: constructor name -> type name
    let mut ctor_to_type: std::collections::HashMap<&str, &str> = std::collections::HashMap::new();
    for (type_name, ctors) in &exports.type_constructors {
        for ctor in ctors {
            ctor_to_type.insert(ctor.as_str(), type_name.as_str());
        }
    }

    // Traits: canonical + aliased + bare (traits are always available for impl/where
    // when the module is imported, regardless of exposing clause)
    for trait_name in exports.traits.keys() {
        ScopeMap::register_qualified(&mut scope.traits, module_name, prefix, trait_name);
        // Traits also get a bare entry (always available without qualification)
        let trait_canonical = format!("{}.{}", module_name, trait_name);
        scope
            .traits
            .entry(trait_name.clone())
            .or_insert_with(|| trait_canonical);
    }

    // Trait methods: bare -> Module.Trait.method
    // Trait methods are always unqualified in user code; the canonical form
    // is used by the resolve pass to rewrite Var nodes.
    for (trait_name, info) in &exports.traits {
        for (method_name, _, _, _) in &info.methods {
            let canonical = format!("{}.{}.{}", module_name, trait_name, method_name);
            scope.values.entry(method_name.clone()).or_insert(canonical);
        }
    }

    // Effects: canonical + aliased qualified forms
    for effect_name in exports.effects.keys() {
        ScopeMap::register_qualified(&mut scope.effects, module_name, prefix, effect_name);
    }

    // Handlers: canonical + aliased qualified forms
    for handler_name in exports.handlers.keys() {
        ScopeMap::register_qualified(&mut scope.handlers, module_name, prefix, handler_name);
    }

    // Value bindings: canonical + aliased
    for (name, _) in &exports.bindings {
        ScopeMap::register_qualified(&mut scope.values, module_name, prefix, name);
    }

    // Constructors: canonical + aliased
    for ctors in exports.type_constructors.values() {
        for ctor in ctors {
            if binding_map.contains_key(ctor.as_str()) {
                ScopeMap::register_qualified(&mut scope.constructors, module_name, prefix, ctor);
            }
        }
    }

    // Type names: qualified and aliased -> canonical (always available)
    // Bare entries are only added when there is no exposing clause
    // (i.e. `import Foo` makes all types available, but `import Foo (Bar)`
    // only makes `Bar` available as a bare name).
    for name in exports.type_arity.keys() {
        ScopeMap::register_qualified(&mut scope.types, module_name, prefix, name);
        if exposing.is_none() {
            let type_canonical = format!("{}.{}", module_name, name);
            scope
                .types
                .entry(name.clone())
                .or_insert_with(|| type_canonical);
        }
    }

    // Exposed items: bare -> canonical, with validation
    if let Some(exposed) = exposing {
        for name in exposed {
            let is_type = name.starts_with(|c: char| c.is_uppercase());
            if is_type {
                let mut found = binding_map.contains_key(name.as_str());
                // Bare type value -> canonical
                if found {
                    let type_canonical = format!("{}.{}", module_name, name);
                    scope.values.entry(name.clone()).or_insert(type_canonical);
                }
                // Bare type name resolves to canonical
                let type_canonical = format!("{}.{}", module_name, name);
                scope.types.entry(name.clone()).or_insert(type_canonical);
                // Record types count as found
                if exports.record_defs.contains_key(name.as_str()) {
                    found = true;
                }
                // Constructors belonging to this type
                if let Some(ctors) = exports.type_constructors.get(name) {
                    found = true;
                    for ctor in ctors {
                        if binding_map.contains_key(ctor.as_str()) {
                            let ctor_canonical = format!("{}.{}", module_name, ctor);
                            scope
                                .constructors
                                .entry(ctor.clone())
                                .or_insert_with(|| ctor_canonical.clone());
                            scope.values.entry(ctor.clone()).or_insert(ctor_canonical);
                        }
                    }
                }
                // Exposed constructor-as-name
                if ctor_to_type.contains_key(name.as_str())
                    && binding_map.contains_key(name.as_str())
                {
                    let ctor_canonical = format!("{}.{}", module_name, name);
                    scope
                        .constructors
                        .entry(name.clone())
                        .or_insert_with(|| ctor_canonical.clone());
                    scope.values.entry(name.clone()).or_insert(ctor_canonical);
                    found = true;
                }
                // Effects can be exposed by name
                if let Some(info) = exports.effects.get(name) {
                    let effect_canonical = format!("{}.{}", module_name, name);
                    scope
                        .effects
                        .entry(name.clone())
                        .or_insert(effect_canonical.clone());
                    scope.register_effect_ops(
                        &effect_canonical,
                        info.ops.iter().map(|op| op.name.as_str()),
                    );
                    found = true;
                }
                // Traits can be exposed by name
                if exports.traits.contains_key(name) {
                    let trait_canonical = format!("{}.{}", module_name, name);
                    scope.traits.entry(name.clone()).or_insert(trait_canonical);
                    found = true;
                }
                if !found {
                    return Err(format!("'{}' is not exported by module '{}'", name, prefix));
                }
            } else {
                // Bare value -> canonical
                let canonical = format!("{}.{}", module_name, name);
                // Validate: must be a function/value in scope, or a handler name
                let is_handler = exports.handlers.contains_key(name);
                if !scope.values.contains_key(&canonical) && !is_handler {
                    return Err(format!("'{}' is not exported by module '{}'", name, prefix));
                }
                if scope.values.contains_key(&canonical) {
                    scope.values.entry(name.clone()).or_insert(canonical);
                }
                if is_handler {
                    let handler_canonical = format!("{}.{}", module_name, name);
                    scope
                        .handlers
                        .entry(name.clone())
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
                ..
            } => {
                // Resolve trait name to canonical form via scope_map
                let canonical_trait = scope_map
                    .resolve_trait(trait_name)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("{}.{}", module_name, trait_name));
                let trait_type_arg_names: Vec<String> = trait_type_args
                    .iter()
                    .map(|te| match te {
                        crate::ast::TypeExpr::Var { name, .. } => name.clone(),
                        _ => scope_map
                            .resolve_type(te.simple_name())
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| canonical_type_name(te.simple_name())),
                    })
                    .collect();
                let canonical_trait_type_args = canonical_trait_type_args(&trait_type_arg_names);
                let canonical_target_type = canonical_type_name(target_type);
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
                    .map(|(i, name)| (name.as_str(), i))
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
                trait_impl_dicts.push(TraitImplDict {
                    trait_name: canonical_trait,
                    trait_type_args: canonical_trait_type_args,
                    target_type: canonical_target_type,
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
        external_funs,
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
            Decl::RecordDef {
                public: true, name, ..
            } => {
                names.insert(name.clone());
            }
            Decl::Val {
                public: true, name, ..
            }
            | Decl::HandlerDef {
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
                    names.insert(m.node.name.clone());
                }
            }
            _ => {}
        }
    }
    names
}
