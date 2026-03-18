mod check_decl;
mod check_module;
pub use check_module::{ModuleMap, builtin_module_source, scan_project_modules};
mod check_traits;
pub(crate) mod exhaustiveness;
mod infer;
mod result;
pub use result::CheckResult;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, ExprKind};
use crate::token::Span;

/// Returns the span of the first effect call found in `expr`, if any.
/// Used to reject effect calls inside guard expressions.
pub(crate) fn find_effect_call(expr: &Expr) -> Option<Span> {
    match &expr.kind {
        ExprKind::EffectCall { .. } => Some(expr.span),
        ExprKind::App { func, arg, .. } => find_effect_call(func).or_else(|| find_effect_call(arg)),
        ExprKind::BinOp { left, right, .. } => {
            find_effect_call(left).or_else(|| find_effect_call(right))
        }
        ExprKind::UnaryMinus { expr: inner, .. } => find_effect_call(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_effect_call(cond)
            .or_else(|| find_effect_call(then_branch))
            .or_else(|| find_effect_call(else_branch)),
        _ => None,
    }
}

// --- Type representation ---

/// Internal type representation used during inference.
/// Separate from ast::TypeExpr, which is surface syntax.
/// All types (including primitives like Int, Bool) are represented as `Con`.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// Unification variable, solved during inference
    Var(u32),
    /// Function type: a -> b
    Arrow(Box<Type>, Box<Type>),
    /// Function type with effect annotation: a -> b needs {Eff1, Eff2 T}
    /// Used for HOF parameter types that declare which effects they absorb.
    /// Each effect is (name, type_args), e.g. ("Actor", [CounterMsg]).
    EffArrow(Box<Type>, Box<Type>, Vec<(String, Vec<Type>)>),
    /// Named type constructor with args: Int = Con("Int", []), List a = Con("List", [a])
    Con(std::string::String, Vec<Type>),
    /// Error recovery type: unifies with everything, suppresses cascading errors.
    Error,
}

/// Convenience constructors for built-in types
impl Type {
    pub fn con(name: &str) -> Type {
        Type::Con(name.into(), vec![])
    }
    pub fn int() -> Type {
        Type::con("Int")
    }
    pub fn float() -> Type {
        Type::con("Float")
    }
    pub fn string() -> Type {
        Type::con("String")
    }
    pub fn bool() -> Type {
        Type::con("Bool")
    }
    pub fn unit() -> Type {
        Type::con("Unit")
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(id) => write!(f, "?{}", id),
            Type::Arrow(a, b) | Type::EffArrow(a, b, _) => match a.as_ref() {
                Type::Arrow(_, _) | Type::EffArrow(_, _, _) => write!(f, "({}) -> {}", a, b),
                _ => write!(f, "{} -> {}", a, b),
            },
            Type::Con(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}", name)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    Ok(())
                }
            }
            Type::Error => write!(f, "<error>"),
        }
    }
}

// --- Substitution ---

/// Maps type variable IDs to their solved types.
#[derive(Debug, Default, Clone)]
pub struct Substitution {
    map: HashMap<u32, Type>,
}

impl Substitution {
    pub fn new() -> Self {
        Self::default()
    }

    /// Apply the substitution to a type, following chains of variables.
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.apply(resolved)
                } else {
                    ty.clone()
                }
            }
            Type::Arrow(a, b) => Type::Arrow(Box::new(self.apply(a)), Box::new(self.apply(b))),
            Type::EffArrow(a, b, effs) => Type::EffArrow(
                Box::new(self.apply(a)),
                Box::new(self.apply(b)),
                effs.iter()
                    .map(|(name, args)| {
                        (name.clone(), args.iter().map(|t| self.apply(t)).collect())
                    })
                    .collect(),
            ),
            Type::Con(name, args) => {
                Type::Con(name.clone(), args.iter().map(|a| self.apply(a)).collect())
            }
            Type::Error => Type::Error,
        }
    }

    /// Bind a type variable to a type, with occurs check.
    fn bind(&mut self, id: u32, ty: &Type) -> Result<(), Diagnostic> {
        if let Type::Var(other) = ty
            && *other == id
        {
            return Ok(());
        }

        if self.occurs(id, ty) {
            return Err(Diagnostic::error(
                format!("infinite type: ?{} occurs in {}", id, ty),
            ));
        }
        self.map.insert(id, ty.clone());
        Ok(())
    }

    /// Check if a type variable occurs inside a type (prevents infinite types).
    fn occurs(&self, id: u32, ty: &Type) -> bool {
        match ty {
            Type::Var(other) => {
                if *other == id {
                    return true;
                }
                if let Some(resolved) = self.map.get(other) {
                    self.occurs(id, resolved)
                } else {
                    false
                }
            }
            Type::Arrow(a, b) => self.occurs(id, a) || self.occurs(id, b),
            Type::EffArrow(a, b, effs) => {
                self.occurs(id, a)
                    || self.occurs(id, b)
                    || effs
                        .iter()
                        .any(|(_, args)| args.iter().any(|t| self.occurs(id, t)))
            }
            Type::Con(_, args) => args.iter().any(|a| self.occurs(id, a)),
            Type::Error => false,
        }
    }
}

// --- Type scheme (polymorphism) ---

/// A polymorphic type: forall [vars]. constraints => ty
/// e.g. `forall a. Show a => a -> String`
#[derive(Debug, Clone)]
pub struct Scheme {
    pub forall: Vec<u32>,
    /// Trait constraints: (trait_name, type_var_id)
    pub constraints: Vec<(String, u32)>,
    pub ty: Type,
}

impl Scheme {
    /// Map forall var IDs to readable names (a, b, c, ...)
    fn var_names(&self) -> HashMap<u32, String> {
        self.forall
            .iter()
            .enumerate()
            .map(|(i, &id)| {
                let name = ((b'a' + i as u8) as char).to_string();
                (id, name)
            })
            .collect()
    }

    /// Return the type with forall variables replaced by readable names (a, b, c, ...).
    /// Apply a substitution first to resolve any solved variables.
    pub fn display_type(&self, sub: &Substitution) -> Type {
        let resolved = sub.apply(&self.ty);
        if self.forall.is_empty() {
            return resolved;
        }
        rename_vars(&resolved, &self.var_names())
    }

    /// Format the type with constraints as a string, e.g. "a -> Unit where {a: Show}"
    pub fn display_with_constraints(&self, sub: &Substitution) -> String {
        let ty = self.display_type(sub);
        if self.constraints.is_empty() {
            return format!("{}", ty);
        }
        let names = self.var_names();
        // Group constraints by type variable
        let mut bounds: HashMap<String, Vec<String>> = HashMap::new();
        for (trait_name, var_id) in &self.constraints {
            let var_name = names
                .get(var_id)
                .cloned()
                .unwrap_or_else(|| format!("?{}", var_id));
            bounds.entry(var_name).or_default().push(trait_name.clone());
        }
        let mut parts: Vec<String> = bounds
            .iter()
            .map(|(var, traits)| format!("{}: {}", var, traits.join(" + ")))
            .collect();
        parts.sort();
        format!("{} where {{{}}}", ty, parts.join(", "))
    }
}

/// Replace `Type::Var(id)` with `Type::Con(name, [])` for display purposes.
fn rename_vars(ty: &Type, names: &HashMap<u32, String>) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(name) = names.get(id) {
                Type::Con(name.clone(), vec![])
            } else {
                ty.clone()
            }
        }
        Type::Arrow(a, b) => Type::Arrow(
            Box::new(rename_vars(a, names)),
            Box::new(rename_vars(b, names)),
        ),
        Type::EffArrow(a, b, effs) => Type::EffArrow(
            Box::new(rename_vars(a, names)),
            Box::new(rename_vars(b, names)),
            effs.iter()
                .map(|(name, args)| {
                    (
                        name.clone(),
                        args.iter().map(|t| rename_vars(t, names)).collect(),
                    )
                })
                .collect(),
        ),
        Type::Con(name, args) => Type::Con(
            name.clone(),
            args.iter().map(|a| rename_vars(a, names)).collect(),
        ),
        Type::Error => Type::Error,
    }
}

// --- Module exports ---

/// All public items exported by a typechecked module, cached as a single unit.
#[derive(Debug, Clone, Default)]
pub struct ModuleExports {
    /// Public type bindings: name -> scheme.
    pub bindings: Vec<(String, Scheme)>,
    /// Type name -> constructor names (empty vec for opaque types).
    pub type_constructors: HashMap<String, Vec<String>>,
    /// Record name -> ordered field types.
    pub record_defs: HashMap<String, Vec<(String, Type)>>,
    /// Trait name -> trait info.
    pub traits: HashMap<String, TraitInfo>,
    /// (trait_name, target_type) -> impl info.
    pub trait_impls: HashMap<(String, String), ImplInfo>,
    /// Effect name -> effect def info.
    pub(crate) effects: HashMap<String, EffectDefInfo>,
    /// Handler name -> handler info.
    pub(crate) handlers: HashMap<String, HandlerInfo>,
}

impl ModuleExports {
    /// Collect all public exports from a typechecked module.
    pub fn collect(program: &[crate::ast::Decl], checker: &Checker) -> Self {
        use crate::ast::Decl;

        let pub_names = crate::typechecker::check_module::public_names_for_tc(program);

        // Bindings: from env and constructors
        let mut bindings: Vec<(String, Scheme)> = Vec::new();
        for name in &pub_names {
            if let Some(scheme) = checker.env.get(name) {
                bindings.push((name.to_string(), scheme.clone()));
            } else if let Some(scheme) = checker.constructors.get(name) {
                bindings.push((name.to_string(), scheme.clone()));
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
                        let ctors: Vec<String> = variants.iter().map(|v| v.name.clone()).collect();
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
        let mut record_defs: HashMap<String, Vec<(String, Type)>> = HashMap::new();
        let mut traits: HashMap<String, TraitInfo> = HashMap::new();
        let mut trait_impls: HashMap<(String, String), ImplInfo> = HashMap::new();
        let mut effects: HashMap<String, EffectDefInfo> = HashMap::new();
        let mut handlers: HashMap<String, HandlerInfo> = HashMap::new();

        for decl in program {
            match decl {
                Decl::RecordDef {
                    public: true, name, ..
                } => {
                    if let Some(fields) = checker.records.get(name.as_str()) {
                        record_defs.insert(name.clone(), fields.clone());
                    }
                }
                Decl::TraitDef {
                    public: true, name, ..
                } => {
                    if let Some(info) = checker.traits.get(name.as_str()) {
                        traits.insert(name.clone(), info.clone());
                    }
                }
                Decl::ImplDef {
                    trait_name,
                    target_type,
                    ..
                } => {
                    let key = (trait_name.clone(), target_type.clone());
                    if let Some(info) = checker.trait_impls.get(&key) {
                        trait_impls.insert(key, info.clone());
                    }
                }
                Decl::EffectDef {
                    public: true, name, ..
                } => {
                    if let Some(info) = checker.effects.get(name) {
                        effects.insert(name.clone(), info.clone());
                    }
                }
                Decl::HandlerDef {
                    public: true, name, ..
                } => {
                    if let Some(info) = checker.handlers.get(name) {
                        handlers.insert(name.clone(), info.clone());
                    }
                }
                _ => {}
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
        }
    }
}

// --- Module codegen info ---

/// An effect operation definition for codegen: operation name and parameter count.
#[derive(Debug, Clone)]
pub struct EffectOpDef {
    pub name: String,
    pub param_count: usize,
}

/// An effect definition for codegen: effect name, its operations, and type parameter count.
#[derive(Debug, Clone)]
pub struct EffectDef {
    pub name: String,
    pub ops: Vec<EffectOpDef>,
    pub type_param_count: usize,
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
    /// Trait impl dicts: (trait_name, target_type, dict_name, arity).
    /// The dict_name is module-qualified (e.g. `__dict_Show_animals_Animal`).
    pub trait_impl_dicts: Vec<(String, String, String, usize)>,
}

// --- Type environment ---

/// Maps variable names to their type schemes.
#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
    bindings: HashMap<std::string::String, Scheme>,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: std::string::String, scheme: Scheme) {
        self.bindings.insert(name, scheme);
    }

    pub fn get(&self, name: &str) -> Option<&Scheme> {
        self.bindings.get(name)
    }

    pub fn remove(&mut self, name: &str) {
        self.bindings.remove(name);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Scheme)> {
        self.bindings.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Free type variables in the environment (used for generalization).
    fn free_vars(&self, sub: &Substitution) -> Vec<u32> {
        let mut vars = Vec::new();
        for scheme in self.bindings.values() {
            free_vars_in_type(&sub.apply(&scheme.ty), &scheme.forall, &mut vars);
        }
        vars
    }
}

fn free_vars_in_type(ty: &Type, bound: &[u32], out: &mut Vec<u32>) {
    match ty {
        Type::Var(id) => {
            if !bound.contains(id) && !out.contains(id) {
                out.push(*id);
            }
        }
        Type::Arrow(a, b) => {
            free_vars_in_type(a, bound, out);
            free_vars_in_type(b, bound, out);
        }
        Type::EffArrow(a, b, effs) => {
            free_vars_in_type(a, bound, out);
            free_vars_in_type(b, bound, out);
            for (_, args) in effs {
                for t in args {
                    free_vars_in_type(t, bound, out);
                }
            }
        }
        Type::Con(_, args) => {
            for arg in args {
                free_vars_in_type(arg, bound, out);
            }
        }
        Type::Error => {}
    }
}

// --- Errors ---

#[derive(Debug, Clone)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: std::string::String,
    pub span: Option<Span>,
}

impl Diagnostic {
    pub(crate) fn new(severity: Severity, message: impl Into<std::string::String>) -> Self {
        Diagnostic {
            severity,
            message: message.into(),
            span: None,
        }
    }

    pub(crate) fn at(
        span: Span,
        severity: Severity,
        message: impl Into<std::string::String>,
    ) -> Self {
        Diagnostic {
            severity,
            message: message.into(),
            span: Some(span),
        }
    }

    /// Convenience: error with no span.
    pub(crate) fn error(message: impl Into<std::string::String>) -> Self {
        Self::new(Severity::Error, message)
    }

    /// Convenience: error at a specific span.
    pub(crate) fn error_at(span: Span, message: impl Into<std::string::String>) -> Self {
        Self::at(span, Severity::Error, message)
    }

    /// Convenience: warning at a specific span.
    pub(crate) fn warning_at(span: Span, message: impl Into<std::string::String>) -> Self {
        Self::at(span, Severity::Warning, message)
    }

    pub(crate) fn with_span(mut self, span: Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

// --- Internal types used by inference ---

#[derive(Debug, Clone)]
pub struct EffectOpSig {
    pub name: std::string::String,
    pub params: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct EffectDefInfo {
    /// Fresh var IDs for the effect's type parameters (empty for non-parameterized effects)
    pub type_params: Vec<u32>,
    pub ops: Vec<EffectOpSig>,
    /// op_name -> span of the op declaration in the effect block (for LSP go-to-def)
    pub op_spans: HashMap<String, Span>,
    /// Which module this effect is defined in (None = main file).
    pub source_module: Option<String>,
}

#[derive(Debug, Clone)]
pub struct HandlerInfo {
    /// Which effects this handler handles
    pub effects: Vec<std::string::String>,
    /// Return clause: (param_var_id, body_type). Used to compute the `with` expression type.
    pub return_type: Option<(u32, Type)>,
    /// op_name -> span of the handler arm (for LSP go-to-def and with-stack)
    pub arm_spans: HashMap<String, Span>,
    /// Which module this handler is defined in (None = main file).
    pub source_module: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TraitInfo {
    // TODO: type_param will be used for kind checking (maybe, if we implement it :P )
    #[allow(dead_code)]
    pub type_param: String,
    pub supertraits: Vec<String>,
    /// Method signatures: name -> (param_types, return_type)
    pub methods: Vec<(String, Vec<Type>, Type)>,
}

#[derive(Debug, Clone)]
pub struct ImplInfo {
    /// Constraints on type parameters: (trait_name, param_index)
    /// e.g. Show for List requires Show on param 0 (the element type)
    pub param_constraints: Vec<(String, usize)>,
    pub span: Option<Span>,
}

/// Evidence that a trait constraint was resolved during typechecking.
/// Used by the elaboration pass to insert dictionary arguments.
#[derive(Debug, Clone)]
pub struct TraitEvidence {
    pub node_id: crate::ast::NodeId,
    pub trait_name: String,
    /// The concrete type that satisfied the constraint.
    /// None if resolved via a where-bound type variable (polymorphic passthrough).
    pub resolved_type: Option<(String, Vec<Type>)>,
    /// For polymorphic evidence, the name of the type variable that was bounded.
    /// Used to select the correct dict param when multiple where-clause bounds
    /// exist for the same trait (e.g. `where {e: Show, a: Show}`).
    pub type_var_name: Option<String>,
}

// --- Inference engine ---

#[derive(Clone)]
pub struct Checker {
    pub(crate) next_var: u32,
    pub(crate) sub: Substitution,
    pub(crate) env: TypeEnv,
    /// Constructor types from type definitions: name -> (arity, type scheme)
    pub(crate) constructors: HashMap<std::string::String, Scheme>,
    /// Record definitions: record name -> vec of (field_name, field_type)
    pub(crate) records: HashMap<std::string::String, Vec<(std::string::String, Type)>>,
    /// Effect definitions: effect name -> definition info (type params + operations)
    pub(crate) effects: HashMap<std::string::String, EffectDefInfo>,
    /// Named handler definitions: handler name -> info
    pub(crate) handlers: HashMap<std::string::String, HandlerInfo>,
    /// Context for resume typing: when inside a handler arm, the return type of the op being handled
    pub(crate) resume_type: Option<Type>,
    /// Effects used in the current function body (accumulated during inference)
    pub(crate) current_effects: HashSet<String>,
    /// Per-scope cache of instantiated effect type params: effect name -> mapping from original var IDs to fresh vars.
    /// Ensures all ops from the same effect share type params within a function scope.
    pub(crate) effect_type_param_cache: HashMap<String, HashMap<u32, Type>>,
    /// Known effect requirements for named functions: name -> set of effect names
    pub(crate) fun_effects: HashMap<String, HashSet<String>>,
    /// Annotation-provided effect type constraints: fn name -> [(effect_name, [concrete types])]
    pub(crate) fun_effect_type_constraints: HashMap<String, Vec<(String, Vec<Type>)>>,
    /// Trait definitions: trait name -> info
    pub(crate) traits: HashMap<String, TraitInfo>,
    /// Impl registry: (trait_name, target_type) -> impl info
    pub(crate) trait_impls: HashMap<(String, String), ImplInfo>,
    /// Pending trait constraints to check: (trait_name, type, span_for_errors, node_id)
    pub(crate) pending_constraints: Vec<(String, Type, Span, crate::ast::NodeId)>,
    /// Per-variable record candidate narrowing for field access: var_id -> (candidate record names, span).
    /// Tracks which records are still candidates for an unresolved type variable based on
    /// the intersection of all fields accessed on it. Checked at end of each function body.
    pub(crate) field_candidates: FieldCandidates,
    /// Where clause bounds: var_id -> set of trait names assumed satisfied
    pub(crate) where_bounds: HashMap<u32, HashSet<String>>,
    /// Reverse map from type var ID to original type parameter name (for polymorphic evidence)
    pub(crate) where_bound_var_names: HashMap<u32, String>,
    /// Module system state: caches, project root, import tracking.
    pub(crate) modules: ModuleContext,
    /// Reverse map: type name -> list of (constructor_name, arity) pairs (for exhaustiveness checking)
    pub(crate) adt_variants: HashMap<std::string::String, Vec<(std::string::String, usize)>>,
    /// Evidence collected during constraint solving for the elaboration pass.
    pub(crate) evidence: Vec<TraitEvidence>,
    /// Diagnostics collected during block inference (for multi-error reporting).
    pub(crate) collected_diagnostics: Vec<Diagnostic>,
    /// Per-node type information for Expr nodes (LSP hover, go-to-def, etc.).
    /// Types are stored unresolved (may contain type variables); apply `sub`
    /// at lookup time to get the final resolved type.
    pub(crate) type_at_node: HashMap<crate::ast::NodeId, Type>,
    /// Per-span type information for Pat bindings (which don't have NodeIds).
    pub(crate) type_at_span: HashMap<Span, Type>,
    /// When true, function annotations without matching bodies are allowed
    /// (used for builtin stdlib modules where implementations are in Rust).
    pub(crate) allow_bodyless_annotations: bool,
    /// Set to the module name when checking a module file; None for the main file.
    pub(crate) current_module: Option<String>,
    /// Stack of (op_name -> (arm_span, source_module)) maps for nested `with` expressions.
    /// Innermost handler is last. Used to record which arm handles each effect call.
    pub(crate) with_arm_stacks: Vec<HashMap<String, (Span, Option<String>)>>,
    /// Maps effect call span -> (handler arm span, source module) (for LSP go-to-def, level 1).
    pub(crate) effect_call_targets: HashMap<Span, (Span, Option<String>)>,
    /// Maps handler arm span -> (effect op definition span, source module) (for LSP go-to-def, level 2).
    pub(crate) handler_arm_targets: HashMap<Span, (Span, Option<String>)>,
}

/// Module system state: caches, project root, and import tracking.
#[derive(Clone, Default)]
pub struct ModuleContext {
    /// Project root for resolving imports. None = script mode.
    pub(crate) project_root: Option<std::path::PathBuf>,
    /// Map from declared module name to file path. Built by scanning the project at startup.
    pub map: Option<check_module::ModuleMap>,
    /// Cache of already-typechecked modules: module name -> all public exports.
    pub(crate) exports: HashMap<String, ModuleExports>,
    /// Cache of codegen-relevant info for each typechecked module.
    pub codegen_info: HashMap<String, ModuleCodegenInfo>,
    /// Cache of parsed programs for each typechecked module.
    pub programs: HashMap<String, crate::ast::Program>,
    /// Cached checker state after prelude has been loaded.
    pub(crate) prelude_snapshot: Option<Box<Checker>>,
    /// Trait impls from Std.dy (base layer). Shared with builtin module checkers
    /// so they can resolve constraints on primitives (e.g. Ord for Int).
    pub(crate) base_trait_impls: HashMap<(String, String), ImplInfo>,
    /// Modules currently being typechecked (cycle detection).
    pub(crate) loading: HashSet<String>,
}

/// Per-variable record candidate narrowing: var_id -> (candidate record names, span).
pub(crate) type FieldCandidates = HashMap<u32, (Vec<String>, Span)>;

/// Snapshot of per-function-body inference state, saved before checking a body
/// and restored afterward. Prevents effect tracking and field candidate narrowing
/// from one body leaking into the next.
pub(crate) struct BodyScope {
    effects: HashSet<String>,
    effect_cache: HashMap<String, HashMap<u32, Type>>,
    field_candidates: FieldCandidates,
}

impl Default for Checker {
    fn default() -> Self {
        Self::new()
    }
}

impl Checker {
    pub fn new() -> Self {
        let mut checker = Checker {
            next_var: 0,
            sub: Substitution::new(),
            env: TypeEnv::new(),
            constructors: HashMap::new(),
            records: HashMap::new(),
            effects: HashMap::new(),
            handlers: HashMap::new(),
            resume_type: None,
            current_effects: HashSet::new(),
            effect_type_param_cache: HashMap::new(),
            fun_effects: HashMap::new(),
            fun_effect_type_constraints: HashMap::new(),
            traits: HashMap::new(),
            trait_impls: HashMap::new(),
            pending_constraints: Vec::new(),
            field_candidates: HashMap::new(),
            where_bounds: HashMap::new(),
            where_bound_var_names: HashMap::new(),
            modules: ModuleContext::default(),
            adt_variants: HashMap::new(),
            evidence: Vec::new(),
            collected_diagnostics: Vec::new(),
            type_at_node: HashMap::new(),
            type_at_span: HashMap::new(),
            allow_bodyless_annotations: false,
            current_module: None,
            with_arm_stacks: Vec::new(),
            effect_call_targets: HashMap::new(),
            handler_arm_targets: HashMap::new(),
        };
        checker.register_builtins();
        checker
    }

    pub fn with_project_root(root: std::path::PathBuf) -> Self {
        let mut checker = Self::new();
        checker.modules.project_root = Some(root);
        checker
    }

    /// Snapshot current trait impls as the base layer (from Std.dy).
    /// Called after loading Std.dy so builtin module checkers inherit these impls.
    pub fn snapshot_base_trait_impls(&mut self) {
        self.modules.base_trait_impls = self.trait_impls.clone();
    }

    /// Create a checker with the prelude loaded and (optionally) a project
    /// root with its module map. This is the standard entry point for both
    /// the CLI and the LSP.
    pub fn with_prelude(
        project_root: Option<std::path::PathBuf>,
    ) -> std::result::Result<Self, Diagnostic> {
        let mut checker = match &project_root {
            Some(root) => Self::with_project_root(root.clone()),
            None => Self::new(),
        };

        if let Some(root) = &project_root
            && let Ok(module_map) = check_module::scan_project_modules(root)
        {
            checker.set_module_map(module_map);
        }

        // Load prelude (which imports Std first, then stdlib modules).
        // Std.dy defines base traits (Show, Ord) and is loaded as a real module
        // via `import Std` in the prelude.
        let prelude_src = include_str!("../stdlib/prelude.dy");
        let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
            .lex()
            .expect("prelude lex");
        let mut prelude_program = crate::parser::Parser::new(prelude_tokens)
            .parse_program()
            .expect("prelude parse");
        crate::derive::expand_derives(&mut prelude_program);
        checker
            .check_program_inner(&prelude_program)
            .map_err(|errs| errs.into_iter().next().unwrap())?;

        checker.modules.prelude_snapshot = Some(Box::new(checker.clone()));
        Ok(checker)
    }

    /// Drain errors from collected_diagnostics, leaving warnings in place.
    pub(crate) fn drain_errors(&mut self) -> Vec<Diagnostic> {
        let (errors, rest): (Vec<_>, Vec<_>) = std::mem::take(&mut self.collected_diagnostics)
            .into_iter()
            .partition(|d| matches!(d.severity, Severity::Error));
        self.collected_diagnostics = rest;
        errors
    }

    /// Record the type of an expression node (by NodeId).
    pub(crate) fn record_type(&mut self, node_id: crate::ast::NodeId, ty: &Type) {
        self.type_at_node.entry(node_id).or_insert_with(|| ty.clone());
    }

    /// Record the type of a pattern binding (by Span, since Pat has no NodeId).
    pub(crate) fn record_type_at_span(&mut self, span: Span, ty: &Type) {
        self.type_at_span.entry(span).or_insert_with(|| ty.clone());
    }

    pub fn effect_names(&self) -> Vec<String> {
        self.effects.keys().cloned().collect()
    }

    pub fn handler_names(&self) -> Vec<String> {
        self.handlers.keys().cloned().collect()
    }

    pub fn set_module_map(&mut self, map: check_module::ModuleMap) {
        self.modules.map = Some(map);
    }

    pub(crate) fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    /// Save and clear the per-body inference state (effects, effect cache, field candidates).
    /// Call `restore_body_scope` after checking the body to get back the collected effects.
    pub(crate) fn save_body_scope(&mut self) -> BodyScope {
        BodyScope {
            effects: std::mem::take(&mut self.current_effects),
            effect_cache: std::mem::take(&mut self.effect_type_param_cache),
            field_candidates: std::mem::take(&mut self.field_candidates),
        }
    }

    /// Restore the saved scope, returning the effects and field candidates that
    /// the body accumulated while it was active.
    pub(crate) fn restore_body_scope(
        &mut self,
        scope: BodyScope,
    ) -> (HashSet<String>, FieldCandidates) {
        let body_effects = std::mem::replace(&mut self.current_effects, scope.effects);
        self.effect_type_param_cache = scope.effect_cache;
        let body_field_candidates =
            std::mem::replace(&mut self.field_candidates, scope.field_candidates);
        (body_effects, body_field_candidates)
    }

    /// Check that all effects used in a body are covered by the declared `needs` set.
    /// Returns an error if any undeclared effects are found.
    /// `label` is used in the error message (e.g. "function 'foo'", "handler 'bar'").
    pub(crate) fn check_undeclared_effects(
        body_effects: &HashSet<String>,
        declared_effects: &HashSet<String>,
        label: &str,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let undeclared: Vec<_> = body_effects.difference(declared_effects).collect();
        if undeclared.is_empty() {
            return Ok(());
        }
        let mut effects: Vec<_> = undeclared.into_iter().cloned().collect();
        effects.sort();
        if declared_effects.is_empty() {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "{} uses effects {{{}}} but has no 'needs' declaration",
                    label,
                    effects.join(", ")
                ),
            ))
        } else {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "{} uses effects {{{}}} not declared in its 'needs' clause",
                    label,
                    effects.join(", ")
                ),
            ))
        }
    }

    fn register_builtins(&mut self) {
        // Note: Show and Ord traits are defined in Std.dy (loaded before
        // stdlib modules). Eq is built-in (BEAM BIF dispatch).

        // Built-in Num trait (arithmetic: +, -, *, /, %, unary -)
        self.traits.insert(
            "Num".into(),
            TraitInfo {
                type_param: "a".into(),
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float"] {
            self.trait_impls.insert(
                ("Num".into(), prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    span: None,
                },
            );
        }

        // Built-in Eq trait (==, !=)
        self.traits.insert(
            "Eq".into(),
            TraitInfo {
                type_param: "a".into(),
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float", "String", "Bool", "Unit"] {
            self.trait_impls.insert(
                ("Eq".into(), prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    span: None,
                },
            );
        }

        // Ord impls for primitives are defined in Std.Int, Std.Float, Std.String
        // (they provide real dict constructors for `compare`).

        // panic : String -> a (crashes at runtime, polymorphic return type)
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.env.insert(
            "panic".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![],
                ty: Type::Arrow(Box::new(Type::string()), Box::new(a)),
            },
        );

        // todo : String -> a (type hole, crashes at runtime with "not implemented")
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.env.insert(
            "todo".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![],
                ty: Type::Arrow(Box::new(Type::string()), Box::new(a)),
            },
        );

        // List constructors
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.constructors.insert(
            "Nil".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![],
                ty: Type::Con("List".into(), vec![a.clone()]),
            },
        );

        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let list_a = Type::Con("List".into(), vec![a.clone()]);
        self.constructors.insert(
            "Cons".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![],
                ty: Type::Arrow(
                    Box::new(a),
                    Box::new(Type::Arrow(Box::new(list_a.clone()), Box::new(list_a))),
                ),
            },
        );

        // Bool constructors
        self.constructors.insert(
            "True".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::bool(),
            },
        );
        self.constructors.insert(
            "False".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::bool(),
            },
        );

        // Built-in ADT variant maps (for exhaustiveness checking)
        self.adt_variants
            .insert("List".into(), vec![("Nil".into(), 0), ("Cons".into(), 2)]);
        self.adt_variants
            .insert("Bool".into(), vec![("True".into(), 0), ("False".into(), 0)]);

        // Show and Eq for Tuple (any arity -- all params must satisfy the trait)
        // We use "Tuple" as the type name; param_constraints are checked dynamically
        // based on actual type args at constraint resolution time
        self.trait_impls.insert(
            ("Show".into(), "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );
        self.trait_impls.insert(
            ("Eq".into(), "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );

        // --- Dict type ---

        // Eq for Dict k v: requires Eq on both k and v
        self.trait_impls.insert(
            ("Eq".into(), "Dict".into()),
            ImplInfo {
                param_constraints: vec![("Eq".into(), 0), ("Eq".into(), 1)],
                span: None,
            },
        );

        // Dict.empty : forall k v. Dict k v
        {
            let k = self.fresh_var();
            let k_id = match &k {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            let v = self.fresh_var();
            let v_id = match &v {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            self.env.insert(
                "Dict.empty".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![],
                    ty: Type::Con("Dict".into(), vec![k, v]),
                },
            );
        }

        // Dict.get : forall k v. Eq k => k -> Dict k v -> Maybe v
        {
            let k = self.fresh_var();
            let k_id = match &k {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            let v = self.fresh_var();
            let v_id = match &v {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            let dict_kv = Type::Con("Dict".into(), vec![k.clone(), v.clone()]);
            let maybe_v = Type::Con("Maybe".into(), vec![v]);
            self.env.insert(
                "Dict.get".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![("Eq".into(), k_id)],
                    ty: Type::Arrow(
                        Box::new(k),
                        Box::new(Type::Arrow(Box::new(dict_kv), Box::new(maybe_v))),
                    ),
                },
            );
        }

        // --- Conversion builtins ---

        // Int.parse : String -> Maybe Int
        self.env.insert(
            "Int.parse".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::Arrow(
                    Box::new(Type::string()),
                    Box::new(Type::Con("Maybe".into(), vec![Type::int()])),
                ),
            },
        );

        // Float.parse : String -> Maybe Float
        self.env.insert(
            "Float.parse".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::Arrow(
                    Box::new(Type::string()),
                    Box::new(Type::Con("Maybe".into(), vec![Type::float()])),
                ),
            },
        );
    }

    // --- Unification ---

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        let a = self.sub.apply(a);
        let b = self.sub.apply(b);

        match (&a, &b) {
            _ if a == b => Ok(()),

            // Error type unifies with anything (suppresses cascading errors)
            (Type::Error, _) | (_, Type::Error) => Ok(()),

            (Type::Var(id), _) => self.sub.bind(*id, &b),
            (_, Type::Var(id)) => self.sub.bind(*id, &a),

            (Type::Arrow(a1, a2), Type::Arrow(b1, b2))
            | (Type::Arrow(a1, a2), Type::EffArrow(b1, b2, _))
            | (Type::EffArrow(a1, a2, _), Type::Arrow(b1, b2)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)
            }
            (Type::EffArrow(a1, a2, effs1), Type::EffArrow(b1, b2, effs2)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)?;
                // Unify effect type args pairwise (matched by effect name)
                for (name, args1) in effs1 {
                    if let Some((_, args2)) = effs2.iter().find(|(n, _)| n == name) {
                        for (t1, t2) in args1.iter().zip(args2.iter()) {
                            self.unify(t1, t2)?;
                        }
                    }
                }
                Ok(())
            }

            (Type::Con(n1, args1), Type::Con(n2, args2))
                if n1 == n2 && args1.len() == args2.len() =>
            {
                for (a, b) in args1.iter().zip(args2.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }

            _ => {
                let a_display = self.prettify_type(&a);
                let b_display = self.prettify_type(&b);
                Err(Diagnostic::error(
                    format!("type mismatch: expected {}, got {}", a_display, b_display),
                ))
            }
        }
    }

    /// Format a type for error messages: apply substitutions, then replace
    /// any remaining unresolved type variables with readable names (a, b, c, ...).
    fn prettify_type(&self, ty: &Type) -> Type {
        let resolved = self.sub.apply(ty);
        let mut vars = Vec::new();
        collect_free_vars(&resolved, &mut vars);
        if vars.is_empty() {
            return resolved;
        }
        let names: HashMap<u32, String> = vars
            .iter()
            .enumerate()
            .map(|(i, &id)| {
                let name = ((b'a' + i as u8) as char).to_string();
                (id, name)
            })
            .collect();
        rename_vars(&resolved, &names)
    }

    /// Unify with span context: if unification fails, attach the span to the error.
    pub(crate) fn unify_at(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), Diagnostic> {
        self.unify(a, b).map_err(|e| e.with_span(span))
    }

    // --- Instantiation & Generalization ---

    /// Replace forall'd variables with fresh type variables.
    /// Returns the instantiated type and any trait constraints (remapped to fresh vars).
    pub(crate) fn instantiate(&mut self, scheme: &Scheme) -> (Type, Vec<(String, Type)>) {
        let mapping: HashMap<u32, Type> = scheme
            .forall
            .iter()
            .map(|&id| (id, self.fresh_var()))
            .collect();
        let ty = self.replace_vars(&scheme.ty, &mapping);
        let constraints = scheme
            .constraints
            .iter()
            .map(|(trait_name, var_id)| {
                let fresh = mapping.get(var_id).cloned().unwrap_or(Type::Var(*var_id));
                (trait_name.clone(), fresh)
            })
            .collect();
        (ty, constraints)
    }

    pub(crate) fn replace_vars(&self, ty: &Type, mapping: &HashMap<u32, Type>) -> Type {
        match ty {
            Type::Var(id) => mapping.get(id).cloned().unwrap_or_else(|| ty.clone()),
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.replace_vars(a, mapping)),
                Box::new(self.replace_vars(b, mapping)),
            ),
            Type::EffArrow(a, b, effs) => Type::EffArrow(
                Box::new(self.replace_vars(a, mapping)),
                Box::new(self.replace_vars(b, mapping)),
                effs.iter()
                    .map(|(name, args)| {
                        (
                            name.clone(),
                            args.iter().map(|t| self.replace_vars(t, mapping)).collect(),
                        )
                    })
                    .collect(),
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter().map(|a| self.replace_vars(a, mapping)).collect(),
            ),
            Type::Error => Type::Error,
        }
    }

    /// Generalize a type over variables not free in the environment.
    pub(crate) fn generalize(&self, ty: &Type) -> Scheme {
        let resolved = self.sub.apply(ty);
        let env_vars = self.env.free_vars(&self.sub);
        // Collect effect type param vars that must not be generalized --
        // these are shared across ops of the same effect within a function scope.
        let effect_vars: HashSet<u32> = self
            .effect_type_param_cache
            .values()
            .flat_map(|mapping| {
                mapping.values().filter_map(|ty| {
                    let resolved = self.sub.apply(ty);
                    if let Type::Var(id) = resolved {
                        Some(id)
                    } else {
                        None
                    }
                })
            })
            .collect();
        let mut forall = Vec::new();
        collect_free_vars(&resolved, &mut forall);
        forall.retain(|v| !env_vars.contains(v) && !effect_vars.contains(v));
        Scheme {
            forall,
            constraints: vec![],
            ty: resolved,
        }
    }

    /// Convert a surface TypeExpr to our internal Type representation.
    pub(crate) fn convert_type_expr(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
    ) -> Type {
        match texpr {
            crate::ast::TypeExpr::Named(name) => Type::Con(name.clone(), vec![]),
            crate::ast::TypeExpr::Var(name) => {
                if let Some((_, id)) = params.iter().find(|(n, _)| n == name) {
                    Type::Var(*id)
                } else {
                    // New type variable -- create fresh and remember for reuse
                    let id = self.next_var;
                    self.next_var += 1;
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            }
            crate::ast::TypeExpr::App(func, arg) => {
                let func_ty = self.convert_type_expr(func, params);
                let arg_ty = self.convert_type_expr(arg, params);
                // Type application: push arg into Con's args list
                match func_ty {
                    Type::Con(name, mut args) => {
                        args.push(arg_ty);
                        Type::Con(name, args)
                    }
                    _ => {
                        // Shouldn't happen with well-formed type exprs
                        Type::Con("?".into(), vec![func_ty, arg_ty])
                    }
                }
            }
            crate::ast::TypeExpr::Arrow(a, b, needs) => {
                let a_ty = self.convert_type_expr(a, params);
                let b_ty = self.convert_type_expr(b, params);
                if needs.is_empty() {
                    Type::Arrow(Box::new(a_ty), Box::new(b_ty))
                } else {
                    let effect_refs: Vec<(String, Vec<Type>)> = needs
                        .iter()
                        .map(|e| {
                            let args = e
                                .type_args
                                .iter()
                                .map(|te| self.convert_type_expr(te, params))
                                .collect();
                            (e.name.clone(), args)
                        })
                        .collect();
                    Type::EffArrow(Box::new(a_ty), Box::new(b_ty), effect_refs)
                }
            }
        }
    }
}

pub(crate) fn collect_free_vars(ty: &Type, out: &mut Vec<u32>) {
    match ty {
        Type::Var(id) => {
            if !out.contains(id) {
                out.push(*id);
            }
        }
        Type::Arrow(a, b) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
        }
        Type::EffArrow(a, b, effs) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
            for (_, args) in effs {
                for t in args {
                    collect_free_vars(t, out);
                }
            }
        }
        Type::Con(_, args) => {
            for arg in args {
                collect_free_vars(arg, out);
            }
        }
        Type::Error => {}
    }
}
