//! Name resolution for the lowerer.
//!
//! Runs after elaboration, before lowering. Produces:
//! - `ConstructorAtoms`: constructor name -> mangled Erlang atom
//! - `ResolutionMap`: NodeId -> ResolvedName for every Var/QualifiedName node
//!
//! The lowerer consumes these tables instead of re-deriving name resolution
//! from scratch, eliminating name collisions and fragile dispatch logic.
//!
//! Name resolution is **scope-aware**: the AST walker maintains a stack of
//! local binding frames (function params, let bindings, lambda params, case
//! pattern bindings, etc.). A name that is locally bound shadows any
//! module-level or imported name with the same spelling.

use std::collections::{HashMap, HashSet};

use crate::ast::{self, ComprehensionQualifier, Decl, Expr, ExprKind, NodeId, Pat, Program, Stmt};
use crate::codegen::lower::init::extract_external;
use crate::typechecker::{ModuleCodegenInfo, ResolutionResult as FrontResolutionResult};

/// Map from constructor name -> mangled Erlang atom.
/// Contains both bare ("NotFound") and qualified ("Std.File.NotFound") entries.
pub type ConstructorAtoms = HashMap<String, String>;

/// BEAM convention overrides: constructors that map to specific Erlang atoms
/// regardless of which module they're defined in.
fn beam_override(name: &str) -> Option<&'static str> {
    match name {
        "Ok" => Some("ok"),
        "Err" => Some("error"),
        "Just" => Some("just"),
        "Nothing" => Some("nothing"),
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
    prelude_imports: &[Decl],
) -> ConstructorAtoms {
    let mut atoms = ConstructorAtoms::new();

    // Register BEAM overrides (these win over any module-prefixed version)
    for name in &[
        "Ok", "Err", "Just", "Nothing", "True", "False", "Normal", "Shutdown", "Killed", "Noproc",
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
                        atoms.insert(ctor.clone(), format!("{}_{}", module_name, ctor));
                    }
                }
            }
            Decl::RecordDef { name, .. } => {
                if !atoms.contains_key(name) {
                    atoms.insert(name.clone(), format!("{}_{}", module_name, name));
                }
            }
            _ => {}
        }
    }

    // Build a map of module name -> import alias from import declarations
    let mut import_aliases: HashMap<String, String> = HashMap::new();
    for decl in prelude_imports.iter().chain(program.iter()) {
        if let Decl::Import {
            module_path,
            alias: Some(a),
            ..
        } = decl
        {
            import_aliases.insert(module_path.join("."), a.clone());
        }
    }

    // Imported constructors from codegen_info
    for (mod_name, info) in codegen_info {
        let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
        let erlang_name = module_name_to_erlang(&mod_path);
        let last_segment = mod_path.last().map(|s| s.as_str()).unwrap_or("");
        let alias = import_aliases
            .get(mod_name)
            .map(|s| s.as_str())
            .unwrap_or(last_segment);

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
                    atoms.insert(format!("{}.{}", type_name, ctor), mangled);
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

fn source_module_name(program: &Program, module_name: &str) -> String {
    program
        .iter()
        .find_map(|decl| {
            if let Decl::ModuleDecl { path, .. } = decl {
                Some(path.join("."))
            } else {
                None
            }
        })
        .unwrap_or_else(|| module_name.to_string())
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
        source_module: Option<String>,
        canonical_name: String,
        arity: usize,
        effects: Vec<String>,
    },
    /// A function imported from another module (non-external).
    ImportedFun {
        erlang_mod: String,
        name: String,
        source_module: String,
        canonical_name: String,
        arity: usize,
        effects: Vec<String>,
    },
}

/// Resolution table: maps each AST NodeId to its resolved meaning.
pub type ResolutionMap = HashMap<NodeId, ResolvedName>;

/// Internal representation of a name in scope during resolution.
#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
enum ScopedName {
    LocalFun {
        name: String,
        source_module: Option<String>,
        canonical_name: String,
        arity: usize,
        effects: Vec<String>,
    },
    ImportedFun {
        erlang_mod: String,
        name: String,
        source_module: String,
        canonical_name: String,
        arity: usize,
        effects: Vec<String>,
    },
}

// ---------------------------------------------------------------------------
// Lexical scope tracking
// ---------------------------------------------------------------------------

/// Tracks both module-level names and a stack of local binding frames.
///
/// There are two kinds of local names:
/// - **Variables** (function params, let bindings, lambda params, case bindings):
///   block module-scope resolution -> the lowerer emits `CExpr::Var`.
/// - **Local functions** (`let f x = ...` / LetFun): shadow module-scope names
///   AND resolve as `LocalFun` -> the lowerer emits `CExpr::FunRef`.
///
/// Resolution order (first match wins):
/// 1. Local variables -> None (not in map -> lowerer defaults to CExpr::Var)
/// 2. Local functions -> Some(LocalFun { .. })
/// 3. Module-level scope -> Some(LocalFun/ImportedFun/ExternalFun)
struct Scope<'a> {
    /// Module-level unqualified names (local funs, exposed imports, trait dicts).
    module: &'a HashMap<String, ScopedName>,
    /// Qualified names (e.g. "List.map", "Std.List.map").
    qualified: &'a HashMap<String, ScopedName>,
    /// Stack of local variable binding frames (params, let, lambda, case).
    /// Names here block resolution entirely.
    locals: Vec<HashSet<String>>,
    /// Stack of local function frames (LetFun).
    /// Names here shadow module scope but still resolve as LocalFun.
    local_funs: Vec<HashMap<String, ScopedName>>,
}

impl<'a> Scope<'a> {
    fn new(
        module: &'a HashMap<String, ScopedName>,
        qualified: &'a HashMap<String, ScopedName>,
    ) -> Self {
        Self {
            module,
            qualified,
            locals: Vec::new(),
            local_funs: Vec::new(),
        }
    }

    /// Push a new local variable binding frame.
    fn push(&mut self, names: HashSet<String>) {
        self.locals.push(names);
    }

    /// Pop the top local variable binding frame.
    fn pop(&mut self) {
        self.locals.pop();
    }

    /// Push a new local function frame.
    fn push_funs(&mut self, funs: HashMap<String, ScopedName>) {
        self.local_funs.push(funs);
    }

    /// Pop the top local function frame.
    fn pop_funs(&mut self) {
        self.local_funs.pop();
    }

    fn has_local_var(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|frame| frame.contains(name))
    }

    fn resolve_local_fun(&self, name: &str) -> Option<&ScopedName> {
        for frame in self.local_funs.iter().rev() {
            if let Some(scoped) = frame.get(name) {
                return Some(scoped);
            }
        }
        None
    }

    /// Resolve an unqualified name.
    /// Returns None if it's a local variable (block resolution).
    /// Returns Some(ScopedName) if it's a local function, module-level, or imported.
    fn resolve_unqualified(&self, name: &str) -> Option<&ScopedName> {
        // 1. Local variables shadow everything
        if self.has_local_var(name) {
            return None;
        }
        // 2. Local functions shadow module scope
        if let Some(scoped) = self.resolve_local_fun(name) {
            return Some(scoped);
        }
        // 3. Module scope
        self.module.get(name)
    }

    /// Resolve a qualified name (e.g. "List.map").
    fn resolve_qualified(&self, qualified: &str) -> Option<&ScopedName> {
        self.qualified.get(qualified)
    }

    fn resolve_global_lookup(&self, lookup_name: &str) -> Option<&ScopedName> {
        if lookup_name.contains('.') {
            self.qualified
                .get(lookup_name)
                .or_else(|| self.module.get(lookup_name))
        } else {
            self.module
                .get(lookup_name)
                .or_else(|| self.qualified.get(lookup_name))
        }
    }
}

// ---------------------------------------------------------------------------
// Extract bound variable names from patterns
// ---------------------------------------------------------------------------

/// Collect all variable names bound by a pattern.
fn collect_pat_vars(pat: &Pat) -> HashSet<String> {
    let mut vars = HashSet::new();
    collect_pat_vars_into(pat, &mut vars);
    vars
}

/// Collect all variable names bound by multiple patterns.
fn collect_pats_vars(pats: &[Pat]) -> HashSet<String> {
    let mut vars = HashSet::new();
    for pat in pats {
        collect_pat_vars_into(pat, &mut vars);
    }
    vars
}

fn collect_pat_vars_into(pat: &Pat, vars: &mut HashSet<String>) {
    match pat {
        Pat::Var { name, .. } => {
            vars.insert(name.clone());
        }
        Pat::Constructor { args, .. } => {
            for arg in args {
                collect_pat_vars_into(arg, vars);
            }
        }
        Pat::Tuple { elements, .. } => {
            for elem in elements {
                collect_pat_vars_into(elem, vars);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            for (field_name, alias_pat) in fields {
                if let Some(alias) = alias_pat {
                    // `{ status: s }` — `s` is bound
                    collect_pat_vars_into(alias, vars);
                } else {
                    // `{ status }` — `status` is bound as a variable
                    vars.insert(field_name.clone());
                }
            }
            if let Some(name) = as_name {
                vars.insert(name.clone());
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (field_name, alias_pat) in fields {
                if let Some(alias) = alias_pat {
                    collect_pat_vars_into(alias, vars);
                } else {
                    vars.insert(field_name.clone());
                }
            }
        }
        Pat::StringPrefix { rest, .. } => {
            collect_pat_vars_into(rest, vars);
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_vars_into(head, vars);
            collect_pat_vars_into(tail, vars);
        }
        Pat::ListPat { elements, .. } => {
            for elem in elements {
                collect_pat_vars_into(elem, vars);
            }
        }
        Pat::BitStringPat { segments, .. } => {
            for seg in segments {
                collect_pat_vars_into(&seg.value, vars);
            }
        }
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
        Pat::Or { .. } => unreachable!("or-patterns should be desugared before resolve"),
    }
}

// ---------------------------------------------------------------------------
// Build module-level scope (unchanged logic, minus the external leak)
// ---------------------------------------------------------------------------

/// Build the resolution map for a module.
///
/// Walks the elaborated AST and, for each `ExprKind::Var` and `ExprKind::QualifiedName`
/// node, determines whether it refers to a local function, an imported function,
/// an external function, or a local variable (by absence from the map).
pub fn resolve_names(
    module_name: &str,
    program: &Program,
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
    prelude_imports: &[Decl],
    front_resolution: &FrontResolutionResult,
) -> ResolutionMap {
    let source_module_name = source_module_name(program, module_name);
    let mut scope: HashMap<String, ScopedName> = HashMap::new();
    let mut qualified_scope: HashMap<String, ScopedName> = HashMap::new();
    let local_funs = collect_local_fun_arities(program);
    register_local_scope_funs(&mut scope, &local_funs, &source_module_name);
    let effect_op_counts = build_effect_op_counts(codegen_info);
    register_import_scopes(
        program,
        prelude_imports,
        codegen_info,
        &local_funs,
        &effect_op_counts,
        &mut scope,
        &mut qualified_scope,
    );
    register_trait_impl_dicts(codegen_info, &mut scope);

    // Step 4: Walk the AST with scope-aware resolution.
    let mut lexical = Scope::new(&scope, &qualified_scope);
    let mut map = ResolutionMap::new();
    resolve_program(program, &mut lexical, &mut map, front_resolution);

    map
}

// ---------------------------------------------------------------------------
// Scope-aware AST walk
// ---------------------------------------------------------------------------

fn resolve_program(
    program: &Program,
    scope: &mut Scope<'_>,
    map: &mut ResolutionMap,
    front_resolution: &FrontResolutionResult,
) {
    for decl in program {
        resolve_decl(decl, scope, map, front_resolution);
    }
}

fn resolve_decl(
    decl: &Decl,
    scope: &mut Scope<'_>,
    map: &mut ResolutionMap,
    front_resolution: &FrontResolutionResult,
) {
    match decl {
        Decl::FunBinding { params, body, .. } => {
            // Function parameters shadow module-level names within the body
            let param_vars = collect_pats_vars(params);
            scope.push(param_vars);
            resolve_expr(body, scope, map, front_resolution);
            scope.pop();
        }
        Decl::Let { value, .. } | Decl::Val { value, .. } => {
            resolve_expr(value, scope, map, front_resolution);
        }
        Decl::HandlerDef { body, .. } => {
            resolve_handler_body_names(body, scope, map, front_resolution);
        }
        Decl::ImplDef { methods, .. } => {
            for method in methods {
                let param_vars = collect_pats_vars(&method.node.params);
                scope.push(param_vars);
                resolve_expr(&method.node.body, scope, map, front_resolution);
                scope.pop();
            }
        }
        Decl::DictConstructor { methods, .. } => {
            for method in methods {
                resolve_expr(method, scope, map, front_resolution);
            }
        }
        _ => {}
    }
}

fn resolve_handler_body_names(
    body: &ast::HandlerBody,
    scope: &mut Scope<'_>,
    map: &mut ResolutionMap,
    front_resolution: &FrontResolutionResult,
) {
    for arm in &body.arms {
        let param_names: HashSet<String> =
            arm.node.params.iter().flat_map(collect_pat_vars).collect();
        scope.push(param_names);
        resolve_expr(&arm.node.body, scope, map, front_resolution);
        if let Some(ref fb) = arm.node.finally_block {
            resolve_expr(fb, scope, map, front_resolution);
        }
        scope.pop();
    }
    if let Some(rc) = &body.return_clause {
        let param_names: HashSet<String> = rc.params.iter().flat_map(collect_pat_vars).collect();
        scope.push(param_names);
        resolve_expr(&rc.body, scope, map, front_resolution);
        scope.pop();
    }
}

fn resolve_expr(
    expr: &Expr,
    scope: &mut Scope<'_>,
    map: &mut ResolutionMap,
    front_resolution: &FrontResolutionResult,
) {
    match &expr.kind {
        ExprKind::Var { name, .. } => {
            if scope.has_local_var(name) {
                // Locally bound variable, not a function ref.
            } else if let Some(scoped) = scope.resolve_local_fun(name) {
                map.insert(expr.id, scoped_to_resolved(scoped));
            } else {
                match front_resolution.value(expr.id) {
                    Some(crate::typechecker::ResolvedValue::Local { .. }) => {}
                    Some(crate::typechecker::ResolvedValue::Global { lookup_name }) => {
                        if let Some(scoped) = scope.resolve_global_lookup(lookup_name) {
                            map.insert(expr.id, scoped_to_resolved(scoped));
                        }
                    }
                    None => {}
                }
            }
            // If locally bound or not in module scope -> not in map ->
            // lowerer treats as local variable (CExpr::Var).
        }
        ExprKind::QualifiedName { module, name, .. } => {
            if let Some(crate::typechecker::ResolvedValue::Global { lookup_name }) =
                front_resolution.value(expr.id)
                && let Some(scoped) = scope.resolve_global_lookup(lookup_name)
            {
                map.insert(expr.id, scoped_to_resolved(scoped));
            } else {
                let qualified = format!("{}.{}", module, name);
                #[cfg(debug_assertions)]
                eprintln!(
                    "debug: backend resolve fell back to string-based QualifiedName lookup for '{}' ({:?})",
                    qualified, expr.id
                );
                if let Some(scoped) = scope.resolve_qualified(&qualified) {
                    map.insert(expr.id, scoped_to_resolved(scoped));
                }
            }
        }
        ExprKind::App { func, arg, .. } => {
            resolve_expr(func, scope, map, front_resolution);
            resolve_expr(arg, scope, map, front_resolution);
        }
        ExprKind::Lambda { params, body, .. } => {
            let param_vars = collect_pats_vars(params);
            scope.push(param_vars);
            resolve_expr(body, scope, map, front_resolution);
            scope.pop();
        }
        ExprKind::Block { stmts, .. } => {
            // Let bindings are visible to subsequent statements in the block.
            // We accumulate frames for variable bindings and local function defs.
            let mut block_locals = HashSet::new();
            let mut block_funs: HashMap<String, ScopedName> = HashMap::new();
            scope.push(block_locals.clone());
            scope.push_funs(block_funs.clone());
            for stmt in stmts {
                match &stmt.node {
                    Stmt::Let { pattern, value, .. } => {
                        // Resolve the value BEFORE adding the binding (no self-reference)
                        resolve_expr(value, scope, map, front_resolution);
                        // Add pattern vars to the block frame for subsequent stmts
                        let new_vars = collect_pat_vars(pattern);
                        block_locals.extend(new_vars);
                        // Update the top frame
                        scope.pop();
                        scope.push(block_locals.clone());
                    }
                    Stmt::LetFun {
                        name, params, body, ..
                    } => {
                        // LetFun defines a local *function*, not a variable.
                        // It resolves as LocalFun (for FunRef codegen) and shadows imports.
                        let arity = params.len();
                        block_funs.insert(
                            name.clone(),
                            ScopedName::LocalFun {
                                name: name.clone(),
                                source_module: None,
                                canonical_name: name.clone(),
                                arity,
                                effects: Vec::new(),
                            },
                        );
                        // Update the local funs frame (visible to subsequent stmts + own body for recursion)
                        scope.pop_funs();
                        scope.push_funs(block_funs.clone());
                        // Params shadow within the body
                        let param_vars = collect_pats_vars(params);
                        scope.push(param_vars);
                        resolve_expr(body, scope, map, front_resolution);
                        scope.pop();
                    }
                    Stmt::Expr(e) => {
                        resolve_expr(e, scope, map, front_resolution);
                    }
                }
            }
            scope.pop_funs();
            scope.pop();
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            resolve_expr(cond, scope, map, front_resolution);
            resolve_expr(then_branch, scope, map, front_resolution);
            resolve_expr(else_branch, scope, map, front_resolution);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            resolve_expr(scrutinee, scope, map, front_resolution);
            for arm in arms {
                // Pattern vars are in scope for the guard and body
                let arm_vars = collect_pat_vars(&arm.node.pattern);
                scope.push(arm_vars);
                if let Some(g) = &arm.node.guard {
                    resolve_expr(g, scope, map, front_resolution);
                }
                resolve_expr(&arm.node.body, scope, map, front_resolution);
                scope.pop();
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
            ..
        } => {
            resolve_expr(inner, scope, map, front_resolution);
            match handler.as_ref() {
                ast::Handler::Named(_) => {}
                ast::Handler::Inline { items, .. } => {
                    for ann in items {
                        let arm = match &ann.node {
                            ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => arm,
                            ast::HandlerItem::Named(_) => continue,
                        };
                        let param_names: HashSet<String> =
                            arm.params.iter().flat_map(collect_pat_vars).collect();
                        scope.push(param_names);
                        resolve_expr(&arm.body, scope, map, front_resolution);
                        if let Some(ref fb) = arm.finally_block {
                            resolve_expr(fb, scope, map, front_resolution);
                        }
                        scope.pop();
                    }
                }
            }
        }
        ExprKind::BinOp { left, right, .. } => {
            resolve_expr(left, scope, map, front_resolution);
            resolve_expr(right, scope, map, front_resolution);
        }
        ExprKind::UnaryMinus { expr: inner, .. } | ExprKind::Ascription { expr: inner, .. } => {
            resolve_expr(inner, scope, map, front_resolution);
        }
        ExprKind::Tuple { elements, .. } => {
            for e in elements {
                resolve_expr(e, scope, map, front_resolution);
            }
        }
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, e) in fields {
                resolve_expr(e, scope, map, front_resolution);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            resolve_expr(record, scope, map, front_resolution);
            for (_, _, e) in fields {
                resolve_expr(e, scope, map, front_resolution);
            }
        }
        ExprKind::FieldAccess { expr: record, .. } => {
            resolve_expr(record, scope, map, front_resolution);
        }
        ExprKind::EffectCall { .. } => {
            // Effect calls are resolved dynamically by the lowerer
        }
        ExprKind::Resume { value, .. } => {
            resolve_expr(value, scope, map, front_resolution);
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            // Each binding's pattern vars are visible to subsequent bindings
            // and the success expression.
            let mut do_locals = HashSet::new();
            scope.push(do_locals.clone());
            for (pat, e) in bindings {
                resolve_expr(e, scope, map, front_resolution);
                let new_vars = collect_pat_vars(pat);
                do_locals.extend(new_vars);
                scope.pop();
                scope.push(do_locals.clone());
            }
            resolve_expr(success, scope, map, front_resolution);
            scope.pop();
            // Else arms have their own pattern scopes
            for arm in else_arms {
                let arm_vars = collect_pat_vars(&arm.node.pattern);
                scope.push(arm_vars);
                if let Some(g) = &arm.node.guard {
                    resolve_expr(g, scope, map, front_resolution);
                }
                resolve_expr(&arm.node.body, scope, map, front_resolution);
                scope.pop();
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                let arm_vars = collect_pat_vars(&arm.node.pattern);
                scope.push(arm_vars);
                if let Some(g) = &arm.node.guard {
                    resolve_expr(g, scope, map, front_resolution);
                }
                resolve_expr(&arm.node.body, scope, map, front_resolution);
                scope.pop();
            }
            if let Some((timeout, body)) = after_clause {
                resolve_expr(timeout, scope, map, front_resolution);
                resolve_expr(body, scope, map, front_resolution);
            }
        }
        ExprKind::HandlerExpr { body } => {
            resolve_handler_body_names(body, scope, map, front_resolution);
        }
        ExprKind::DictMethodAccess { dict, .. } => {
            resolve_expr(dict, scope, map, front_resolution);
        }
        ExprKind::DictRef { name, .. } => {
            // Dict refs are trait dictionary constructors - resolve like Var
            if let Some(scoped) = scope.resolve_unqualified(name) {
                map.insert(expr.id, scoped_to_resolved(scoped));
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                resolve_expr(arg, scope, map, front_resolution);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(e) = part {
                    resolve_expr(e, scope, map, front_resolution);
                }
            }
        }
        ExprKind::ListComprehension {
            body, qualifiers, ..
        } => {
            // Generator and let bindings accumulate through qualifiers
            let mut comp_locals = HashSet::new();
            scope.push(comp_locals.clone());
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(pat, e) => {
                        resolve_expr(e, scope, map, front_resolution);
                        let new_vars = collect_pat_vars(pat);
                        comp_locals.extend(new_vars);
                        scope.pop();
                        scope.push(comp_locals.clone());
                    }
                    ComprehensionQualifier::Let(pat, e) => {
                        resolve_expr(e, scope, map, front_resolution);
                        let new_vars = collect_pat_vars(pat);
                        comp_locals.extend(new_vars);
                        scope.pop();
                        scope.push(comp_locals.clone());
                    }
                    ComprehensionQualifier::Guard(e) => {
                        resolve_expr(e, scope, map, front_resolution);
                    }
                }
            }
            resolve_expr(body, scope, map, front_resolution);
            scope.pop();
        }
        ExprKind::BitString { segments } => {
            for seg in segments {
                resolve_expr(&seg.value, scope, map, front_resolution);
                if let Some(size) = &seg.size {
                    resolve_expr(size, scope, map, front_resolution);
                }
            }
        }
        // Leaf nodes that don't contain sub-expressions
        ExprKind::Lit { .. } | ExprKind::Constructor { .. } => {}

        // Sugar nodes should be desugared before this pass
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                resolve_expr(&seg.node, scope, map, front_resolution);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                resolve_expr(&seg.node, scope, map, front_resolution);
            }
        }
        ExprKind::Cons { head, tail, .. } => {
            resolve_expr(head, scope, map, front_resolution);
            resolve_expr(tail, scope, map, front_resolution);
        }
        ExprKind::ListLit { elements, .. } => {
            for e in elements {
                resolve_expr(e, scope, map, front_resolution);
            }
        }
    }
}

fn scoped_to_resolved(scoped: &ScopedName) -> ResolvedName {
    match scoped {
        ScopedName::LocalFun {
            name,
            source_module,
            canonical_name,
            arity,
            effects,
        } => ResolvedName::LocalFun {
            name: name.clone(),
            source_module: source_module.clone(),
            canonical_name: canonical_name.clone(),
            arity: *arity,
            effects: effects.clone(),
        },
        ScopedName::ImportedFun {
            erlang_mod,
            name,
            source_module,
            canonical_name,
            arity,
            effects,
        } => ResolvedName::ImportedFun {
            erlang_mod: erlang_mod.clone(),
            name: name.clone(),
            source_module: source_module.clone(),
            canonical_name: canonical_name.clone(),
            arity: *arity,
            effects: effects.clone(),
        },
    }
}

fn collect_local_fun_arities(program: &Program) -> HashMap<String, usize> {
    let mut local_funs: HashMap<String, usize> = HashMap::new();
    for decl in program {
        match decl {
            Decl::FunBinding { name, params, .. } => {
                local_funs.entry(name.clone()).or_insert(params.len());
            }
            Decl::Val { name, .. } => {
                local_funs.entry(name.clone()).or_insert(0);
            }
            Decl::FunSignature {
                name,
                params,
                annotations,
                ..
            } => {
                let _ = extract_external(annotations);
                local_funs.entry(name.clone()).or_insert(params.len());
            }
            _ => {}
        }
    }
    local_funs
}

fn register_local_scope_funs(
    scope: &mut HashMap<String, ScopedName>,
    local_funs: &HashMap<String, usize>,
    source_module_name: &str,
) {
    for (name, arity) in local_funs {
        scope.insert(
            name.clone(),
            ScopedName::LocalFun {
                name: name.clone(),
                source_module: Some(source_module_name.to_string()),
                canonical_name: format!("{}.{}", source_module_name, name),
                arity: *arity,
                effects: Vec::new(),
            },
        );
    }
}

fn build_effect_op_counts(
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
) -> HashMap<String, usize> {
    let mut effect_op_counts: HashMap<String, usize> = HashMap::new();
    for info in codegen_info.values() {
        for eff_def in &info.effect_defs {
            effect_op_counts
                .entry(eff_def.name.clone())
                .or_insert(eff_def.ops.len());
        }
    }
    effect_op_counts
}

fn register_import_scopes(
    program: &Program,
    prelude_imports: &[Decl],
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
    local_funs: &HashMap<String, usize>,
    effect_op_counts: &HashMap<String, usize>,
    scope: &mut HashMap<String, ScopedName>,
    qualified_scope: &mut HashMap<String, ScopedName>,
) {
    let import_decls: Vec<&Decl> = prelude_imports
        .iter()
        .chain(program.iter().filter(|d| matches!(d, Decl::Import { .. })))
        .collect();

    for decl in &import_decls {
        if let Decl::Import {
            module_path,
            alias: import_alias,
            exposing,
            ..
        } = decl
        {
            let mod_name = module_path.join(".");
            let mod_path_strs: Vec<String> = module_path.to_vec();
            let erlang_mod = module_name_to_erlang(&mod_path_strs);
            let alias = import_alias
                .as_deref()
                .unwrap_or_else(|| module_path.last().map(|s| s.as_str()).unwrap_or(""));
            let alias_differs = alias != mod_name;

            let info = match codegen_info.get(&mod_name) {
                Some(info) => info,
                None => continue,
            };

            let is_exposed = |name: &str| -> bool {
                match exposing {
                    None => false,
                    Some(names) => names.iter().any(|n| n == name),
                }
            };

            let fun_effects_map: HashMap<&str, &Vec<String>> = info
                .fun_effects
                .iter()
                .map(|(n, effs)| (n.as_str(), effs))
                .collect();

            for (name, scheme) in &info.exports {
                let (arity, _) =
                    crate::codegen::lower::util::arity_and_effects_from_type(&scheme.ty);
                let dict_params =
                    crate::codegen::lower::util::dict_param_count(&scheme.constraints);
                let effects = fun_effects_map
                    .get(name.as_str())
                    .cloned()
                    .cloned()
                    .unwrap_or_default();
                let handler_param_count: usize = effects
                    .iter()
                    .map(|eff| effect_op_counts.get(eff).copied().unwrap_or(0))
                    .sum();
                let return_k = if handler_param_count > 0 { 1 } else { 0 };
                let expanded_arity = arity + dict_params + handler_param_count + return_k;

                let scoped = ScopedName::ImportedFun {
                    erlang_mod: erlang_mod.clone(),
                    name: name.clone(),
                    source_module: mod_name.clone(),
                    canonical_name: format!("{}.{}", mod_name, name),
                    arity: expanded_arity,
                    effects,
                };

                let canonical = format!("{}.{}", mod_name, name);
                qualified_scope
                    .entry(canonical)
                    .or_insert_with(|| scoped.clone());

                if alias_differs {
                    let aliased = format!("{}.{}", alias, name);
                    qualified_scope
                        .entry(aliased)
                        .or_insert_with(|| scoped.clone());
                }

                if is_exposed(name) && !local_funs.contains_key(name) {
                    scope.entry(name.clone()).or_insert(scoped);
                }
            }
        }
    }
}

fn register_trait_impl_dicts(
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
    scope: &mut HashMap<String, ScopedName>,
) {
    for (mod_name, info) in codegen_info {
        let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
        let erlang_mod = module_name_to_erlang(&mod_path);
        for d in &info.trait_impl_dicts {
            scope
                .entry(d.dict_name.clone())
                .or_insert(ScopedName::ImportedFun {
                    erlang_mod: erlang_mod.clone(),
                    name: d.dict_name.clone(),
                    source_module: mod_name.clone(),
                    canonical_name: d.dict_name.clone(),
                    arity: d.arity,
                    effects: Vec::new(),
                });
        }
    }
}
