//! Name resolution for the lowerer.
//!
//! Runs after elaboration, before lowering. Produces:
//! - `ConstructorAtoms`: constructor name -> mangled Erlang atom
//! - `ResolutionMap`: NodeId -> ResolvedName for every Var/QualifiedName node
//!
//! The lowerer consumes these tables instead of re-deriving name resolution
//! from scratch, eliminating name collisions and fragile dispatch logic.

use std::collections::HashMap;

use crate::ast::{self, ComprehensionQualifier, Decl, Expr, ExprKind, NodeId, Program, Stmt};
use crate::codegen::lower::init::extract_external;
use crate::typechecker::ModuleCodegenInfo;

/// Map from constructor name -> mangled Erlang atom.
/// Contains both bare ("NotFound") and qualified ("Std.File.NotFound") entries.
pub type ConstructorAtoms = HashMap<String, String>;

/// BEAM convention overrides: constructors that map to specific Erlang atoms
/// regardless of which module they're defined in.
fn beam_override(name: &str) -> Option<&'static str> {
    match name {
        "Ok" => Some("ok"),
        "Err" => Some("error"),
        "Nothing" => Some("undefined"),
        "True" => Some("true"),
        "False" => Some("false"),
        "Normal" => Some("normal"),
        "Shutdown" => Some("shutdown"),
        "Killed" => Some("killed"),
        "Noproc" => Some("noproc"),
        _ => None,
    }
}

/// Build the constructor atom lookup table for a module.
///
/// Scans local type/record definitions and imported modules' type_constructors
/// to produce a single table the lowerer can use for both expressions and patterns.
pub fn build_constructor_atoms(
    module_name: &str,
    program: &Program,
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
) -> ConstructorAtoms {
    let mut atoms = ConstructorAtoms::new();

    // Register BEAM overrides (these win over any module-prefixed version)
    for name in &[
        "Ok", "Err", "Nothing", "True", "False", "Normal", "Shutdown", "Killed", "Noproc",
    ] {
        if let Some(atom) = beam_override(name) {
            atoms.insert(name.to_string(), atom.to_string());
        }
    }

    // Local type constructors: TypeDef variants
    for decl in program {
        match decl {
            Decl::TypeDef { variants, .. } => {
                for variant in variants {
                    let ctor = &variant.node.name;
                    if !atoms.contains_key(ctor) {
                        atoms.insert(
                            ctor.clone(),
                            format!("{}_{}", module_name, ctor),
                        );
                    }
                }
            }
            Decl::RecordDef { name, .. } => {
                if !atoms.contains_key(name) {
                    atoms.insert(
                        name.clone(),
                        format!("{}_{}", module_name, name),
                    );
                }
            }
            _ => {}
        }
    }

    // Imported constructors from codegen_info
    for (mod_name, info) in codegen_info {
        let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
        let erlang_name = module_name_to_erlang(&mod_path);
        // The last segment is the module alias (e.g. "File" from "Std.File")
        let alias = mod_path.last().map(|s| s.as_str()).unwrap_or("");

        for (type_name, ctors) in &info.type_constructors {
            for ctor in ctors {
                // Register bare name (e.g. "NotFound") if not already taken by a local def
                if !atoms.contains_key(ctor) {
                    if let Some(atom) = beam_override(ctor) {
                        atoms.insert(ctor.clone(), atom.to_string());
                    } else {
                        atoms.insert(ctor.clone(), format!("{}_{}", erlang_name, ctor));
                    }
                }
                // Register qualified forms for disambiguation:
                // "Std.File.NotFound" and "File.NotFound"
                if beam_override(ctor).is_none() {
                    let mangled = format!("{}_{}", erlang_name, ctor);
                    atoms.insert(format!("{}.{}", mod_name, ctor), mangled.clone());
                    // Also register alias-qualified: "File.NotFound"
                    if !alias.is_empty() {
                        atoms.insert(format!("{}.{}", alias, ctor), mangled.clone());
                    }
                    // Also register type-qualified: "FileError.NotFound"
                    atoms.insert(
                        format!("{}.{}", type_name, ctor),
                        mangled,
                    );
                }
            }
        }
    }

    atoms
}

/// Convert a module path like ["Std", "List"] to an Erlang module name "std_list".
fn module_name_to_erlang(path: &[String]) -> String {
    path.iter()
        .map(|s| s.to_lowercase())
        .collect::<Vec<_>>()
        .join("_")
}

// ---------------------------------------------------------------------------
// Phase 2+3: Function/variable name resolution
// ---------------------------------------------------------------------------

/// How a name resolves at a particular Var or QualifiedName usage site.
#[derive(Debug, Clone)]
pub enum ResolvedName {
    /// A top-level function defined in the current module.
    LocalFun {
        name: String,
        arity: usize,
        effects: Vec<String>,
    },
    /// A function imported from another module (non-external).
    ImportedFun {
        erlang_mod: String,
        name: String,
        arity: usize,
        effects: Vec<String>,
    },
    /// An @external function (maps to a specific Erlang module:function).
    ExternalFun {
        erlang_mod: String,
        erlang_func: String,
        arity: usize,
    },
}

/// Resolution table: maps each AST NodeId to its resolved meaning.
pub type ResolutionMap = HashMap<NodeId, ResolvedName>;

/// Internal representation of a name in scope during resolution.
#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
enum ScopedName {
    LocalFun { name: String, arity: usize, effects: Vec<String> },
    ImportedFun { erlang_mod: String, name: String, arity: usize, effects: Vec<String> },
    ExternalFun { erlang_mod: String, erlang_func: String, arity: usize },
}

/// Build the resolution map for a module.
///
/// Walks the elaborated AST and, for each `ExprKind::Var` and `ExprKind::QualifiedName`
/// node, determines whether it refers to a local function, an imported function,
/// an external function, or a local variable.
pub fn resolve_names(
    program: &Program,
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
    prelude_imports: &[Decl],
) -> ResolutionMap {
    let mut scope: HashMap<String, ScopedName> = HashMap::new();
    let mut qualified_scope: HashMap<String, ScopedName> = HashMap::new();

    // Step 1: Register local functions (highest priority)
    let mut local_funs: HashMap<String, usize> = HashMap::new();
    let mut local_externals: HashMap<String, (String, String, usize)> = HashMap::new();
    for decl in program {
        match decl {
            Decl::FunBinding { name, params, .. } => {
                local_funs.entry(name.clone()).or_insert(params.len());
            }
            Decl::FunSignature {
                name,
                params,
                annotations,
                ..
            } => {
                if let Some((erl_mod, erl_func)) = extract_external(annotations) {
                    let arity = params.len();
                    local_externals.insert(name.clone(), (erl_mod, erl_func, arity));
                } else {
                    // Signature without body: register arity from params
                    local_funs.entry(name.clone()).or_insert(params.len());
                }
            }
            _ => {}
        }
    }

    // Register local externals
    for (name, (erl_mod, erl_func, arity)) in &local_externals {
        scope.insert(
            name.clone(),
            ScopedName::ExternalFun {
                erlang_mod: erl_mod.clone(),
                erlang_func: erl_func.clone(),
                arity: *arity,
            },
        );
    }

    // Register local functions (overrides externals with same name).
    // Effects for local functions are tracked by the lowerer's fun_info (from init_module).
    for (name, arity) in &local_funs {
        scope.insert(
            name.clone(),
            ScopedName::LocalFun {
                name: name.clone(),
                arity: *arity,
                effects: Vec::new(),
            },
        );
    }

    // Step 2: Register imports (lower priority than local, prelude < user)
    // Process prelude imports first, then user imports override them.
    let import_decls: Vec<&Decl> = prelude_imports
        .iter()
        .chain(program.iter().filter(|d| matches!(d, Decl::Import { .. })))
        .collect();

    for decl in &import_decls {
        if let Decl::Import {
            module_path,
            exposing,
            ..
        } = decl
        {
            let mod_name = module_path.join(".");
            let mod_path_strs: Vec<String> = module_path.to_vec();
            let erlang_mod = module_name_to_erlang(&mod_path_strs);
            let alias = module_path.last().map(|s| s.as_str()).unwrap_or("");

            let info = match codegen_info.get(&mod_name) {
                Some(info) => info,
                None => continue,
            };

            let is_exposed = |name: &str| -> bool {
                match exposing {
                    None => true, // glob import
                    Some(names) => names.iter().any(|n| n == name),
                }
            };

            // Build a lookup of external functions for this module
            let ext_map: HashMap<String, (String, String, usize)> = info
                .external_funs
                .iter()
                .map(|(name, erl_mod, erl_func, arity)| {
                    (name.clone(), (erl_mod.clone(), erl_func.clone(), *arity))
                })
                .collect();

            // Build effect lookup for this module
            let fun_effects_map: HashMap<&str, &Vec<String>> = info
                .fun_effects
                .iter()
                .map(|(n, effs)| (n.as_str(), effs))
                .collect();

            // Register exported functions
            for (name, scheme) in &info.exports {
                let qualified = format!("{}.{}", alias, name);
                let (arity, _) = crate::codegen::lower::util::arity_and_effects_from_type(
                    &scheme.ty,
                );
                let dict_params =
                    crate::codegen::lower::util::dict_param_count(&scheme.constraints);
                let expanded_arity = arity + dict_params;
                let effects = fun_effects_map
                    .get(name.as_str())
                    .cloned()
                    .cloned()
                    .unwrap_or_default();

                // Check if this is an @external function
                let scoped = if let Some((erl_mod, erl_func, ext_arity)) = ext_map.get(name) {
                    ScopedName::ExternalFun {
                        erlang_mod: erl_mod.clone(),
                        erlang_func: erl_func.clone(),
                        arity: *ext_arity,
                    }
                } else {
                    ScopedName::ImportedFun {
                        erlang_mod: erlang_mod.clone(),
                        name: name.clone(),
                        arity: expanded_arity,
                        effects,
                    }
                };

                qualified_scope
                    .entry(qualified)
                    .or_insert_with(|| scoped.clone());

                // Register unqualified form only if exposed and not shadowed by local
                if is_exposed(name) && !local_funs.contains_key(name) && !local_externals.contains_key(name) {
                    scope.entry(name.clone()).or_insert(scoped);
                }
            }

            // Register private externals (needed for handler body inlining)
            for (name, erl_mod, erl_func, arity) in &info.external_funs {
                // Only register if not already in scope (don't override public exports)
                scope.entry(name.clone()).or_insert(ScopedName::ExternalFun {
                    erlang_mod: erl_mod.clone(),
                    erlang_func: erl_func.clone(),
                    arity: *arity,
                });
            }
        }
    }

    // Step 3: Register trait impl dicts from all modules.
    // The elaborator generates DictRef nodes that reference dicts from any module,
    // not just explicitly imported ones.
    for (mod_name, info) in codegen_info {
        let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
        let erlang_mod = module_name_to_erlang(&mod_path);
        for d in &info.trait_impl_dicts {
            scope.entry(d.dict_name.clone()).or_insert(ScopedName::ImportedFun {
                erlang_mod: erlang_mod.clone(),
                name: d.dict_name.clone(),
                arity: d.arity,
                effects: Vec::new(),
            });
        }
    }

    // Step 4: Walk the AST and resolve every Var and QualifiedName node.
    // Resolution maps from imported modules are merged in by the caller
    // (emit_module_with_context), so we only need to walk our own program.
    let mut map = ResolutionMap::new();
    resolve_program(program, &scope, &qualified_scope, &mut map);

    map
}

/// Walk a program and resolve Var/QualifiedName nodes.
fn resolve_program(
    program: &Program,
    scope: &HashMap<String, ScopedName>,
    qualified_scope: &HashMap<String, ScopedName>,
    map: &mut ResolutionMap,
) {
    for decl in program {
        resolve_decl(decl, scope, qualified_scope, map);
    }
}

fn resolve_decl(
    decl: &Decl,
    scope: &HashMap<String, ScopedName>,
    qualified_scope: &HashMap<String, ScopedName>,
    map: &mut ResolutionMap,
) {
    match decl {
        Decl::FunBinding { body, .. } => resolve_expr(body, scope, qualified_scope, map),
        Decl::Let { value, .. } => resolve_expr(value, scope, qualified_scope, map),
        Decl::HandlerDef {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                resolve_expr(&arm.node.body, scope, qualified_scope, map);
            }
            if let Some(rc) = return_clause {
                resolve_expr(&rc.body, scope, qualified_scope, map);
            }
        }
        Decl::ImplDef { methods, .. } => {
            for method in methods {
                resolve_expr(&method.node.body, scope, qualified_scope, map);
            }
        }
        Decl::DictConstructor { methods, .. } => {
            for method in methods {
                resolve_expr(method, scope, qualified_scope, map);
            }
        }
        _ => {}
    }
}

fn resolve_expr(
    expr: &Expr,
    scope: &HashMap<String, ScopedName>,
    qualified_scope: &HashMap<String, ScopedName>,
    map: &mut ResolutionMap,
) {
    match &expr.kind {
        ExprKind::Var { name, .. } => {
            if let Some(scoped) = scope.get(name) {
                map.insert(expr.id, scoped_to_resolved(scoped));
            }
            // If not in scope, it's a local variable - we don't insert anything,
            // and the lowerer defaults to CExpr::Var.
        }
        ExprKind::QualifiedName {
            module, name, ..
        } => {
            let qualified = format!("{}.{}", module, name);
            if let Some(scoped) = qualified_scope.get(&qualified) {
                map.insert(expr.id, scoped_to_resolved(scoped));
            }
        }
        ExprKind::App { func, arg, .. } => {
            resolve_expr(func, scope, qualified_scope, map);
            resolve_expr(arg, scope, qualified_scope, map);
        }
        ExprKind::Lambda { body, .. } => {
            resolve_expr(body, scope, qualified_scope, map);
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                match &stmt.node {
                    Stmt::Expr(e) | Stmt::Let { value: e, .. } => {
                        resolve_expr(e, scope, qualified_scope, map);
                    }
                    Stmt::LetFun { body, .. } => {
                        resolve_expr(body, scope, qualified_scope, map);
                    }
                }
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            resolve_expr(cond, scope, qualified_scope, map);
            resolve_expr(then_branch, scope, qualified_scope, map);
            resolve_expr(else_branch, scope, qualified_scope, map);
        }
        ExprKind::Case { scrutinee, arms, .. } => {
            resolve_expr(scrutinee, scope, qualified_scope, map);
            for arm in arms {
                if let Some(g) = &arm.node.guard {
                    resolve_expr(g, scope, qualified_scope, map);
                }
                resolve_expr(&arm.node.body, scope, qualified_scope, map);
            }
        }
        ExprKind::With { expr: inner, handler, .. } => {
            resolve_expr(inner, scope, qualified_scope, map);
            match handler.as_ref() {
                ast::Handler::Named(_, _) => {}
                ast::Handler::Inline {
                    arms,
                    return_clause,
                    ..
                } => {
                    for arm in arms {
                        resolve_expr(&arm.node.body, scope, qualified_scope, map);
                    }
                    if let Some(rc) = return_clause {
                        resolve_expr(&rc.body, scope, qualified_scope, map);
                    }
                }
            }
        }
        ExprKind::BinOp { left, right, .. } => {
            resolve_expr(left, scope, qualified_scope, map);
            resolve_expr(right, scope, qualified_scope, map);
        }
        ExprKind::UnaryMinus { expr: inner, .. }
        | ExprKind::Ascription { expr: inner, .. } => {
            resolve_expr(inner, scope, qualified_scope, map);
        }
        ExprKind::Tuple { elements, .. } => {
            for e in elements {
                resolve_expr(e, scope, qualified_scope, map);
            }
        }
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, e) in fields {
                resolve_expr(e, scope, qualified_scope, map);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            resolve_expr(record, scope, qualified_scope, map);
            for (_, _, e) in fields {
                resolve_expr(e, scope, qualified_scope, map);
            }
        }
        ExprKind::FieldAccess { expr: record, .. } => {
            resolve_expr(record, scope, qualified_scope, map);
        }
        ExprKind::EffectCall { .. } => {
            // Effect calls are resolved dynamically by the lowerer
        }
        ExprKind::Resume { value, .. } => {
            resolve_expr(value, scope, qualified_scope, map);
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, e) in bindings {
                resolve_expr(e, scope, qualified_scope, map);
            }
            resolve_expr(success, scope, qualified_scope, map);
            for arm in else_arms {
                if let Some(g) = &arm.node.guard {
                    resolve_expr(g, scope, qualified_scope, map);
                }
                resolve_expr(&arm.node.body, scope, qualified_scope, map);
            }
        }
        ExprKind::Receive { arms, after_clause, .. } => {
            for arm in arms {
                if let Some(g) = &arm.node.guard {
                    resolve_expr(g, scope, qualified_scope, map);
                }
                resolve_expr(&arm.node.body, scope, qualified_scope, map);
            }
            if let Some((timeout, body)) = after_clause {
                resolve_expr(timeout, scope, qualified_scope, map);
                resolve_expr(body, scope, qualified_scope, map);
            }
        }
        ExprKind::DictMethodAccess { dict, .. } => {
            resolve_expr(dict, scope, qualified_scope, map);
        }
        ExprKind::DictRef { name, .. } => {
            // Dict refs are trait dictionary constructors - resolve like Var
            if let Some(scoped) = scope.get(name) {
                map.insert(expr.id, scoped_to_resolved(scoped));
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                resolve_expr(arg, scope, qualified_scope, map);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(e) = part {
                    resolve_expr(e, scope, qualified_scope, map);
                }
            }
        }
        ExprKind::ListComprehension {
            body, qualifiers, ..
        } => {
            resolve_expr(body, scope, qualified_scope, map);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Guard(e)
                    | ComprehensionQualifier::Let(_, e) => {
                        resolve_expr(e, scope, qualified_scope, map);
                    }
                }
            }
        }
        // Leaf nodes that don't contain sub-expressions
        ExprKind::Lit { .. }
        | ExprKind::Constructor { .. }
        => {}

        // Sugar nodes should be desugared before this pass
        ExprKind::Pipe { segments } => {
            for seg in segments {
                resolve_expr(&seg.node, scope, qualified_scope, map);
            }
        }
        ExprKind::PipeBack { segments }
        | ExprKind::ComposeForward { segments }
        | ExprKind::ComposeBack { segments } => {
            for seg in segments {
                resolve_expr(&seg.node, scope, qualified_scope, map);
            }
        }
        ExprKind::Cons { head, tail, .. } => {
            resolve_expr(head, scope, qualified_scope, map);
            resolve_expr(tail, scope, qualified_scope, map);
        }
        ExprKind::ListLit { elements, .. } => {
            for e in elements {
                resolve_expr(e, scope, qualified_scope, map);
            }
        }
    }
}

fn scoped_to_resolved(scoped: &ScopedName) -> ResolvedName {
    match scoped {
        ScopedName::LocalFun { name, arity, effects } => ResolvedName::LocalFun {
            name: name.clone(),
            arity: *arity,
            effects: effects.clone(),
        },
        ScopedName::ImportedFun {
            erlang_mod,
            name,
            arity,
            effects,
        } => ResolvedName::ImportedFun {
            erlang_mod: erlang_mod.clone(),
            name: name.clone(),
            arity: *arity,
            effects: effects.clone(),
        },
        ScopedName::ExternalFun {
            erlang_mod,
            erlang_func,
            arity,
        } => ResolvedName::ExternalFun {
            erlang_mod: erlang_mod.clone(),
            erlang_func: erlang_func.clone(),
            arity: *arity,
        },
    }
}
