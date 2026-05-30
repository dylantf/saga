//! Name resolution for the lowerer.
//!
//! Runs after elaboration, before lowering. Produces:
//! - `ConstructorAtoms`: constructor name -> mangled Erlang atom
//! - `ResolutionMap`: NodeId -> ResolvedSymbol for every Var/QualifiedName node
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
use crate::codegen::external::extract_external;
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
    let source_module = source_module_name(program, module_name);

    // Register BEAM overrides (these win over any module-prefixed version)
    for name in &[
        "Ok", "Err", "True", "False", "Normal", "Shutdown", "Killed", "Noproc",
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
                    let mangled = format!("{}_{}", module_name, ctor);
                    if !atoms.contains_key(ctor) {
                        atoms.insert(ctor.clone(), mangled.clone());
                    }
                    atoms.insert(format!("{}.{}", source_module, ctor), mangled);
                }
            }
            Decl::RecordDef { name, .. } => {
                let mangled = format!("{}_{}", module_name, name);
                if !atoms.contains_key(name) {
                    atoms.insert(name.clone(), mangled.clone());
                }
                atoms.insert(format!("{}.{}", source_module, name), mangled);
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

/// How lowering should treat a resolved value reference.
#[derive(Debug, Clone)]
pub enum ResolvedCodegenKind {
    /// A normal Saga function. `erlang_mod == None` means call/apply in the
    /// current emitted module; `Some` means emit a remote BEAM call/fun ref.
    BeamFunction {
        erlang_mod: Option<String>,
        name: String,
        arity: usize,
        effects: Vec<String>,
    },
    /// A Saga declaration implemented by an Erlang function. Normal calls go
    /// through the Saga wrapper, because effectful Saga calls may have
    /// evidence/continuation arity that native Erlang functions cannot accept.
    /// The native target is retained for the imported-handler/private-helper
    /// bridge path.
    ExternalFunction {
        erlang_mod: String,
        name: String,
        target_erlang_mod: String,
        target_name: String,
        arity: usize,
        effects: Vec<String>,
    },
    /// A compiler intrinsic selected by declaration identity, never spelling.
    /// Intrinsics lower via `lower_intrinsic` and never flow through the
    /// effect-bearing call path, so no `effects` field is carried.
    Intrinsic {
        id: crate::intrinsics::IntrinsicId,
        arity: usize,
    },
    /// An `@inline val`; lowering clones the canonical lowered RHS.
    InlineVal,
}

impl ResolvedCodegenKind {
    pub fn arity(&self) -> usize {
        match self {
            ResolvedCodegenKind::BeamFunction { arity, .. }
            | ResolvedCodegenKind::ExternalFunction { arity, .. }
            | ResolvedCodegenKind::Intrinsic { arity, .. } => *arity,
            ResolvedCodegenKind::InlineVal => 0,
        }
    }

    pub fn effects(&self) -> &[String] {
        match self {
            ResolvedCodegenKind::BeamFunction { effects, .. }
            | ResolvedCodegenKind::ExternalFunction { effects, .. } => effects,
            ResolvedCodegenKind::Intrinsic { .. } | ResolvedCodegenKind::InlineVal => &[],
        }
    }
}

/// How a name resolves at a particular Var or QualifiedName usage site.
#[derive(Debug, Clone)]
pub struct ResolvedSymbol {
    pub name: String,
    pub source_module: Option<String>,
    pub canonical_name: String,
    pub kind: ResolvedCodegenKind,
}

impl ResolvedSymbol {
    pub fn arity(&self) -> usize {
        self.kind.arity()
    }

    pub fn effects(&self) -> &[String] {
        self.kind.effects()
    }
}

/// Resolution table: maps each AST NodeId to its resolved meaning.
pub type ResolutionMap = HashMap<NodeId, ResolvedSymbol>;

/// Internal representation of a name in scope during resolution.
#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
enum ScopedName {
    Symbol {
        name: String,
        source_module: Option<String>,
        canonical_name: String,
        kind: ResolvedCodegenKind,
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
    register_local_scope_funs(
        &mut scope,
        &local_funs,
        &source_module_name,
        codegen_info.get(&source_module_name),
    );
    let effect_op_counts = build_effect_op_counts(codegen_info);
    // Canonical-form qualified entries are driven by what's been *loaded*
    // (every module in `codegen_info`), independent of explicit imports.
    // Imports below add the bare/alias surface on top.
    register_canonical_qualified_scope(
        codegen_info,
        &source_module_name,
        &effect_op_counts,
        &mut qualified_scope,
    );
    register_import_aliases(
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
                // eprintln!(
                //     "debug: backend resolve fell back to string-based QualifiedName lookup for '{}' ({:?})",
                //     qualified, expr.id
                // );
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
                            ScopedName::Symbol {
                                name: name.clone(),
                                source_module: None,
                                canonical_name: name.clone(),
                                kind: ResolvedCodegenKind::BeamFunction {
                                    erlang_mod: None,
                                    name: name.clone(),
                                    arity,
                                    effects: Vec::new(),
                                },
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
        ExprKind::Lit { .. } | ExprKind::Constructor { .. } | ExprKind::SymbolIntrinsic { .. } => {}

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

fn scoped_to_resolved(scoped: &ScopedName) -> ResolvedSymbol {
    match scoped {
        ScopedName::Symbol {
            name,
            source_module,
            canonical_name,
            kind,
        } => ResolvedSymbol {
            name: name.clone(),
            source_module: source_module.clone(),
            canonical_name: canonical_name.clone(),
            kind: kind.clone(),
        },
    }
}

fn collect_local_fun_arities(program: &Program) -> HashMap<String, usize> {
    let mut local_funs: HashMap<String, usize> = HashMap::new();
    // First pass: prefer `FunBinding.params.len()` — after elaboration this
    // includes dict params prepended for `where {T: Trait}` constraints, so
    // the value matches the actually-exported function arity. `FunSignature`
    // alone (e.g. `@external` decls with no binding) carries only the source
    // user-param count.
    for decl in program {
        if let Decl::FunBinding { name, params, .. } = decl {
            local_funs.insert(name.clone(), params.len());
        }
    }
    // Second pass: fill in entries not seen in the first pass. `Val` is
    // always arity-0; `FunSignature` is the source arity (used when there
    // is no FunBinding to refine it — e.g. `@external` wrappers).
    // `DictConstructor` exposes the dict tuple at `dict_params.len()` user
    // args; under the new path the uniform calling convention adds the
    // `_Evidence`/`_ReturnK` pair at the call site via the `__dict_…`
    // branch of `uniform_value_arity`.
    for decl in program {
        match decl {
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
            Decl::DictConstructor {
                name, dict_params, ..
            } => {
                local_funs.entry(name.clone()).or_insert(dict_params.len());
            }
            _ => {}
        }
    }
    local_funs
}

/// Classify a declaration into its codegen kind by consulting the module's
/// `intrinsic_exports` / `inline_vals` / `external_funs` tables. Shared by
/// local-scope registration (`erlang_mod_for_beam = None`) and imported-scope
/// registration (`erlang_mod_for_beam = Some(...)`).
///
/// `erlang_mod_for_external` is the erlang module name of the *defining*
/// module — used as `ExternalFunction.erlang_mod` (the Saga wrapper's home).
fn classify_codegen_kind(
    info: Option<&ModuleCodegenInfo>,
    name: &str,
    declared_arity: usize,
    arity: usize,
    erlang_mod_for_beam: Option<String>,
    erlang_mod_for_external: &str,
    effects: Vec<String>,
) -> ResolvedCodegenKind {
    if let Some((_, intrinsic)) =
        info.and_then(|info| info.intrinsic_exports.iter().find(|(n, _)| n == name))
    {
        return ResolvedCodegenKind::Intrinsic {
            id: *intrinsic,
            arity,
        };
    }
    if info.is_some_and(|info| info.inline_vals.iter().any(|(n, _)| n == name)) {
        return ResolvedCodegenKind::InlineVal;
    }
    if let Some((_, target_mod, target_fun, _)) = info.and_then(|info| {
        info.external_funs
            .iter()
            .find(|(n, _, _, external_arity)| n == name && *external_arity == declared_arity)
    }) {
        return ResolvedCodegenKind::ExternalFunction {
            erlang_mod: erlang_mod_for_external.to_string(),
            name: name.to_string(),
            target_erlang_mod: target_mod.clone(),
            target_name: target_fun.clone(),
            arity,
            effects,
        };
    }
    ResolvedCodegenKind::BeamFunction {
        erlang_mod: erlang_mod_for_beam,
        name: name.to_string(),
        arity,
        effects,
    }
}

fn register_local_scope_funs(
    scope: &mut HashMap<String, ScopedName>,
    local_funs: &HashMap<String, usize>,
    source_module_name: &str,
    info: Option<&ModuleCodegenInfo>,
) {
    let source_erlang_mod = module_name_to_erlang(
        &source_module_name
            .split('.')
            .map(String::from)
            .collect::<Vec<_>>(),
    );
    for (name, arity) in local_funs {
        let kind = classify_codegen_kind(
            info,
            name,
            *arity,
            *arity,
            None,
            &source_erlang_mod,
            Vec::new(),
        );
        scope.insert(
            name.clone(),
            ScopedName::Symbol {
                name: name.clone(),
                source_module: Some(source_module_name.to_string()),
                canonical_name: format!("{}.{}", source_module_name, name),
                kind,
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

/// Build the `ScopedName::ImportedFun` for a single module export, applying
/// the standard arity/effect/evidence-param expansion. Shared by canonical
/// and alias registration so both compute the same scoped value.
fn build_imported_fun_scoped(
    mod_name: &str,
    erlang_mod: &str,
    name: &str,
    scheme: &crate::typechecker::Scheme,
    info: &ModuleCodegenInfo,
    fun_effects_map: &HashMap<&str, &Vec<String>>,
    effect_op_counts: &HashMap<String, usize>,
) -> ScopedName {
    let (arity, mut effects) = crate::codegen::type_shape::arity_and_effects_from_type(&scheme.ty);
    let dict_params = crate::codegen::type_shape::dict_param_count(&scheme.constraints);
    // Merge with fun_effects (which strips beam-native effects in
    // check_module.rs but is otherwise the authoritative annotation list).
    // Effects from the type include beam-native ones; the lowered function
    // threads evidence covering *all* of them, so the resolver's arity
    // calculation must match. This mirrors the supplementation in `lower/init.rs`.
    if let Some(ann_effs) = fun_effects_map.get(name) {
        for eff in ann_effs.iter() {
            if !effects.contains(eff) {
                effects.push(eff.clone());
            }
        }
    }
    effects.sort();
    let handler_param_count: usize = effects
        .iter()
        .map(|eff| effect_op_counts.get(eff).copied().unwrap_or(0))
        .sum();
    // Effectful callees take an `_Evidence` parameter and a `_ReturnK`
    // (gated together by `has_effects`).
    let extras = if handler_param_count > 0 { 2 } else { 0 };
    let expanded_arity = arity + dict_params + extras;
    let canonical_name = format!("{}.{}", mod_name, name);

    let kind = classify_codegen_kind(
        Some(info),
        name,
        arity,
        expanded_arity,
        Some(erlang_mod.to_string()),
        erlang_mod,
        effects,
    );

    ScopedName::Symbol {
        name: name.to_string(),
        source_module: Some(mod_name.to_string()),
        canonical_name,
        kind,
    }
}

/// Register canonical-form (`Module.name`) entries in `qualified_scope` for
/// every loaded module. Driven purely by `codegen_info` — the set of modules
/// the front end has loaded — not by the program's `Decl::Import` nodes.
///
/// This is the codegen analogue of `register_module_canonical_exports` in the
/// typechecker: canonical names are global, available the moment a module is
/// loaded. Imports only add bare/alias surface on top (see
/// `register_import_aliases`).
fn register_canonical_qualified_scope(
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
    source_module_name: &str,
    effect_op_counts: &HashMap<String, usize>,
    qualified_scope: &mut HashMap<String, ScopedName>,
) {
    for (mod_name, info) in codegen_info {
        // The current module's own functions are registered through
        // `register_local_scope_funs` as LocalFun, not as imports.
        if mod_name == source_module_name {
            continue;
        }
        let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
        let erlang_mod = module_name_to_erlang(&mod_path);
        let fun_effects_map: HashMap<&str, &Vec<String>> = info
            .fun_effects
            .iter()
            .map(|(n, effs)| (n.as_str(), effs))
            .collect();
        for (name, scheme) in &info.exports {
            let scoped = build_imported_fun_scoped(
                mod_name,
                &erlang_mod,
                name,
                scheme,
                info,
                &fun_effects_map,
                effect_op_counts,
            );
            let canonical = format!("{}.{}", mod_name, name);
            qualified_scope.entry(canonical).or_insert(scoped);
        }
    }
}

/// Register the *aliased* and *exposed* surfaces for each `Decl::Import`:
/// alias-prefix qualified names (`MyAlias.fn`) and exposed bare names (`fn`).
/// Canonical entries are handled separately by
/// `register_canonical_qualified_scope` and are not the responsibility of
/// import nodes.
fn register_import_aliases(
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
            let erlang_mod = module_name_to_erlang(module_path);
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
                    Some(e) => e.exposes(name),
                }
            };

            let fun_effects_map: HashMap<&str, &Vec<String>> = info
                .fun_effects
                .iter()
                .map(|(n, effs)| (n.as_str(), effs))
                .collect();

            for (name, scheme) in &info.exports {
                if !alias_differs && !is_exposed(name) {
                    continue;
                }
                let scoped = build_imported_fun_scoped(
                    &mod_name,
                    &erlang_mod,
                    name,
                    scheme,
                    info,
                    &fun_effects_map,
                    effect_op_counts,
                );
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
                .or_insert(ScopedName::Symbol {
                    name: d.dict_name.clone(),
                    source_module: Some(mod_name.clone()),
                    canonical_name: d.dict_name.clone(),
                    kind: ResolvedCodegenKind::BeamFunction {
                        erlang_mod: Some(erlang_mod.clone()),
                        name: d.dict_name.clone(),
                        arity: d.arity,
                        effects: Vec::new(),
                    },
                });
        }
    }
}
