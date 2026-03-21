mod builtins;
mod check_decl;
mod check_module;
pub use check_module::{ModuleMap, builtin_module_source, scan_project_modules};
mod check_traits;
mod effects;
pub(crate) mod exhaustiveness;
mod handlers;
mod infer;
mod patterns;
mod records;
mod result;
mod unify;
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
    /// Anonymous record type: `{ street: String, city: String }`
    /// Fields are sorted by name for canonical comparison.
    Record(Vec<(std::string::String, Type)>),
    /// Error recovery type: unifies with everything, suppresses cascading errors.
    Error,
    /// Bottom type: the type of expressions that never produce a value (panic, exit).
    /// Unifies with any type.
    Never,
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
            Type::Record(fields) => {
                write!(f, "{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, ty)?;
                }
                write!(f, " }}")
            }
            Type::Error => write!(f, "<error>"),
            Type::Never => write!(f, "Never"),
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
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.apply(ty)))
                    .collect(),
            ),
            Type::Error => Type::Error,
            Type::Never => Type::Never,
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
            return Err(Diagnostic::error(format!(
                "infinite type: ?{} occurs in {}",
                id, ty
            )));
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
            Type::Record(fields) => fields.iter().any(|(_, ty)| self.occurs(id, ty)),
            Type::Error | Type::Never => false,
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

// Module export types are defined in check_module.rs and re-exported here.
pub use check_module::{
    EffectDef, EffectOpDef, ModuleCodegenInfo, ModuleExports, TraitImplDict,
};

// --- Type environment ---

/// Maps variable names to their type schemes.
#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
    bindings: HashMap<std::string::String, Scheme>,
    /// Tracks the definition-site NodeId for each binding (for find-all-references).
    def_ids: HashMap<std::string::String, crate::ast::NodeId>,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: std::string::String, scheme: Scheme) {
        self.bindings.insert(name, scheme);
    }

    /// Insert a binding along with its definition-site NodeId.
    pub fn insert_with_def(
        &mut self,
        name: std::string::String,
        scheme: Scheme,
        def_id: crate::ast::NodeId,
    ) {
        self.bindings.insert(name.clone(), scheme);
        self.def_ids.insert(name, def_id);
    }

    pub fn get(&self, name: &str) -> Option<&Scheme> {
        self.bindings.get(name)
    }

    /// Look up the definition-site NodeId for a binding.
    pub fn def_id(&self, name: &str) -> Option<crate::ast::NodeId> {
        self.def_ids.get(name).copied()
    }

    pub fn remove(&mut self, name: &str) {
        self.bindings.remove(name);
        // Note: we intentionally keep def_ids entries. The definition identity
        // persists even when the binding is temporarily removed (e.g., for
        // generalization in build_fun_scheme).
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Scheme)> {
        self.bindings.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// All (name, def_id) pairs in the environment.
    pub fn all_def_ids(&self) -> impl Iterator<Item = (String, crate::ast::NodeId)> + '_ {
        self.def_ids.iter().map(|(k, v)| (k.clone(), *v))
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
        Type::Record(fields) => {
            for (_, ty) in fields {
                free_vars_in_type(ty, bound, out);
            }
        }
        Type::Error | Type::Never => {}
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
    pub params: Vec<(String, Type)>,
    pub return_type: Type,
}

/// Record definition info: type parameter var IDs + field types (with those vars).
/// Instantiate the type_params to fresh vars before using the field types.
#[derive(Debug, Clone)]
pub struct RecordInfo {
    /// Fresh var IDs for the record's type parameters (empty for monomorphic records)
    pub type_params: Vec<u32>,
    /// Field name -> field type (may reference vars from type_params)
    pub fields: Vec<(String, Type)>,
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
    pub type_param: String,
    pub supertraits: Vec<String>,
    /// Method signatures: name -> (param_types, return_type, trait_param_var_id)
    pub methods: Vec<(String, Vec<Type>, Type, Option<u32>)>,
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

/// Warnings deferred until after inference, when substitutions are complete.
#[derive(Clone)]
pub enum PendingWarning {
    /// A non-unit value was discarded in a block (not the last statement).
    DiscardedValue { span: Span, ty: Type },
    /// A local variable binding was never referenced.
    UnusedVariable { span: Span, name: String },
    /// A function declares effects in its `needs` clause that it never uses.
    UnusedEffects {
        span: Span,
        fun_name: String,
        effects: Vec<String>,
    },
}

// --- Inference engine ---

#[derive(Clone)]
pub struct Checker {
    pub(crate) next_var: u32,
    pub(crate) sub: Substitution,
    pub(crate) env: TypeEnv,
    /// Constructor types from type definitions: name -> (arity, type scheme)
    pub(crate) constructors: HashMap<std::string::String, Scheme>,
    /// Record definitions: record name -> info (type params + field types)
    pub(crate) records: HashMap<std::string::String, RecordInfo>,
    /// Effect definitions: effect name -> definition info (type params + operations)
    pub(crate) effects: HashMap<std::string::String, EffectDefInfo>,
    /// Named handler definitions: handler name -> info
    pub(crate) handlers: HashMap<std::string::String, HandlerInfo>,
    /// Context for resume typing: when inside a handler arm, the return type of the op being handled
    pub(crate) resume_type: Option<Type>,
    /// Context for resume return typing: when inside a handler arm, the answer type of the with-expression
    pub(crate) resume_return_type: Option<Type>,
    /// Effect tracking state (current effects, caches, annotations).
    pub(crate) effect_state: EffectState,
    /// Trait system state (definitions, impls, constraints, where bounds).
    pub(crate) trait_state: TraitState,
    /// Per-variable record candidate narrowing for field access: var_id -> (candidate record names, span).
    /// Tracks which records are still candidates for an unresolved type variable based on
    /// the intersection of all fields accessed on it. Checked at end of each function body.
    pub(crate) field_candidates: FieldCandidates,
    /// Module system state: caches, project root, import tracking.
    pub(crate) modules: ModuleContext,
    /// Reverse map: type name -> list of (constructor_name, arity) pairs (for exhaustiveness checking)
    pub(crate) adt_variants: HashMap<std::string::String, Vec<(std::string::String, usize)>>,
    /// Type name -> number of declared type parameters (for arity checking).
    /// Absent entries (e.g. Tuple) are unchecked.
    pub(crate) type_arity: HashMap<String, usize>,
    /// Evidence collected during constraint solving for the elaboration pass.
    pub(crate) evidence: Vec<TraitEvidence>,
    /// Dict params for let bindings with trait constraints: name -> (params, value_arity).
    pub(crate) let_dict_params: HashMap<String, (Vec<(String, String)>, usize)>,
    /// Diagnostics collected during block inference (for multi-error reporting).
    pub(crate) collected_diagnostics: Vec<Diagnostic>,
    /// Warnings deferred until after inference, when substitutions are complete.
    pub(crate) pending_warnings: Vec<PendingWarning>,
    /// LSP/IDE state: type info, references, definitions, go-to-def targets.
    pub(crate) lsp: LspState,
    /// When true, function annotations without matching bodies are allowed
    /// (used for builtin stdlib modules where implementations are in Rust).
    pub(crate) allow_bodyless_annotations: bool,
    /// Set to the module name when checking a module file; None for the main file.
    pub(crate) current_module: Option<String>,
}

/// Trait system state: definitions, impl registry, deferred constraints, where bounds.
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Trait definitions: trait name -> info.
    pub traits: HashMap<String, TraitInfo>,
    /// Impl registry: (trait_name, target_type) -> impl info.
    pub impls: HashMap<(String, String), ImplInfo>,
    /// Pending trait constraints to check: (trait_name, type, span_for_errors, node_id).
    pub pending_constraints: Vec<(String, Type, Span, crate::ast::NodeId)>,
    /// Where clause bounds: var_id -> set of trait names assumed satisfied.
    pub where_bounds: HashMap<u32, HashSet<String>>,
    /// Reverse map from type var ID to original type parameter name (for polymorphic evidence).
    pub where_bound_var_names: HashMap<u32, String>,
}

/// Effect tracking state accumulated during inference.
#[derive(Clone, Default)]
pub(crate) struct EffectState {
    /// Effects used in the current function body (accumulated during inference).
    pub current: HashSet<String>,
    /// Per-scope cache of instantiated effect type params: effect name -> mapping
    /// from original var IDs to fresh vars. Ensures all ops from the same effect
    /// share type params within a function scope.
    pub type_param_cache: HashMap<String, HashMap<u32, Type>>,
    /// Known effect requirements for named functions: name -> set of effect names.
    pub fun_effects: HashMap<String, HashSet<String>>,
    /// Annotation-provided effect type constraints: fn name -> [(effect_name, [concrete types])].
    pub fun_type_constraints: HashMap<String, Vec<(String, Vec<Type>)>>,
    /// Deferred effects for let bindings that partially apply effectful functions.
    /// name -> effect names. Used by the lowerer to register effectful local vars.
    pub let_bindings: HashMap<String, Vec<String>>,
}

/// State accumulated during typechecking for IDE/LSP features: hover types,
/// go-to-definition, find-all-references, unused variable detection.
#[derive(Clone, Default)]
pub(crate) struct LspState {
    /// Per-node type information for Expr nodes (LSP hover, go-to-def, etc.).
    /// Types are stored unresolved (may contain type variables); apply `sub`
    /// at lookup time to get the final resolved type.
    pub type_at_node: HashMap<crate::ast::NodeId, Type>,
    /// Per-span type information for Pat bindings.
    pub type_at_span: HashMap<Span, Type>,
    /// Resolution map: usage NodeId -> definition NodeId (for find-all-references).
    pub references: HashMap<crate::ast::NodeId, crate::ast::NodeId>,
    /// NodeId -> Span map for all recorded expression nodes (for resolving NodeIds to locations).
    pub node_spans: HashMap<crate::ast::NodeId, Span>,
    /// Constructor definition NodeIds: constructor name -> NodeId of the TypeConstructor/RecordDef.
    pub constructor_def_ids: HashMap<String, crate::ast::NodeId>,
    /// All variable/param definitions: (NodeId, name, span) for unused variable detection.
    pub definitions: Vec<(crate::ast::NodeId, String, Span)>,
    /// Stack of (op_name -> (arm_span, source_module)) maps for nested `with` expressions.
    /// Innermost handler is last. Used to record which arm handles each effect call.
    pub with_arm_stacks: Vec<HashMap<String, (Span, Option<String>)>>,
    /// Maps effect call span -> (handler arm span, source module) (for LSP go-to-def, level 1).
    pub effect_call_targets: HashMap<Span, (Span, Option<String>)>,
    /// Maps handler arm span -> (effect op definition span, source module) (for LSP go-to-def, level 2).
    pub handler_arm_targets: HashMap<Span, (Span, Option<String>)>,
    /// Import origins: binding name -> source module name (for cross-module find-references).
    /// Populated by inject_scoped_bindings when importing modules.
    pub import_origins: HashMap<String, String>,
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
    /// Cache of per-module CheckResults for elaboration (avoids re-typechecking).
    pub check_results: HashMap<String, CheckResult>,
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

/// Snapshot of effect-related inference state, saved when entering an isolated
/// scope (function body, lambda, with-expression, handler arm) and restored on
/// exit. Prevents effect tracking from leaking between scopes.
pub(crate) struct EffectScope {
    pub(crate) effects: HashSet<String>,
    pub(crate) effect_cache: HashMap<String, HashMap<u32, Type>>,
    pub(crate) field_candidates: FieldCandidates,
    resume_type: Option<Type>,
    resume_return_type: Option<Type>,
}

/// What accumulated inside an EffectScope while it was active.
pub(crate) struct EffectScopeResult {
    pub effects: HashSet<String>,
    pub effect_cache: HashMap<String, HashMap<u32, Type>>,
    pub field_candidates: FieldCandidates,
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
            resume_return_type: None,
            effect_state: EffectState::default(),
            trait_state: TraitState::default(),
            field_candidates: HashMap::new(),
            modules: ModuleContext::default(),
            adt_variants: HashMap::new(),
            type_arity: HashMap::new(),
            evidence: Vec::new(),
            let_dict_params: HashMap::new(),
            collected_diagnostics: Vec::new(),
            pending_warnings: Vec::new(),
            lsp: LspState::default(),
            allow_bodyless_annotations: false,
            current_module: None,
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
        self.modules.base_trait_impls = self.trait_state.impls.clone();
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
        self.lsp
            .type_at_node
            .entry(node_id)
            .or_insert_with(|| ty.clone());
    }

    /// Record the type of a pattern binding (by Span).
    pub(crate) fn record_type_at_span(&mut self, span: Span, ty: &Type) {
        self.lsp
            .type_at_span
            .entry(span)
            .or_insert_with(|| ty.clone());
    }

    /// Record a name resolution: usage_id references def_id.
    pub(crate) fn record_reference(
        &mut self,
        usage_id: crate::ast::NodeId,
        usage_span: Span,
        def_id: crate::ast::NodeId,
    ) {
        self.lsp.references.insert(usage_id, def_id);
        self.lsp.node_spans.insert(usage_id, usage_span);
    }

    /// Emit warnings for local variable bindings that are never referenced.
    pub(crate) fn check_unused_variables(&mut self) {
        let used: std::collections::HashSet<crate::ast::NodeId> =
            self.lsp.references.values().copied().collect();
        for (def_id, name, span) in &self.lsp.definitions {
            if name.starts_with('_') {
                continue;
            }
            if !used.contains(def_id) {
                self.pending_warnings.push(PendingWarning::UnusedVariable {
                    span: *span,
                    name: name.clone(),
                });
            }
        }
    }

    /// "Zonk" pass: apply final substitutions to deferred warnings and emit
    /// only those that are still relevant. Named after GHC's zonking pass.
    pub(crate) fn zonk_warnings(&mut self) {
        for warning in std::mem::take(&mut self.pending_warnings) {
            match warning {
                PendingWarning::DiscardedValue { span, ty } => {
                    let resolved = self.sub.apply(&ty);
                    let is_unit = matches!(&resolved, Type::Con(n, args) if n == "Unit" && args.is_empty());
                    if !is_unit && !matches!(resolved, Type::Var(_) | Type::Error | Type::Never) {
                        let display_ty = self.prettify_type(&ty);
                        self.collected_diagnostics.push(Diagnostic::warning_at(
                            span,
                            format!(
                                "value of type `{}` is discarded; use `let _ = ...` to suppress",
                                display_ty
                            ),
                        ));
                    }
                }
                PendingWarning::UnusedVariable { span, name } => {
                    self.collected_diagnostics.push(Diagnostic::warning_at(
                        span,
                        format!("unused variable: `{}`", name),
                    ));
                }
                PendingWarning::UnusedEffects {
                    span,
                    fun_name,
                    effects,
                } => {
                    self.collected_diagnostics.push(Diagnostic::warning_at(
                        span,
                        format!(
                            "function '{}' declares needs {{{}}} but never uses {}",
                            fun_name,
                            effects.join(", "),
                            if effects.len() == 1 { "it" } else { "them" },
                        ),
                    ));
                }
            }
        }
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

    /// Instantiate a record's type parameters to fresh variables.
    /// Returns (instantiated field types, result Type::Con with fresh args).
    pub(crate) fn instantiate_record(
        &mut self,
        name: &str,
        info: &RecordInfo,
    ) -> (Vec<(String, Type)>, Type) {
        let mapping: HashMap<u32, Type> = info
            .type_params
            .iter()
            .map(|&id| (id, self.fresh_var()))
            .collect();
        let fields = info
            .fields
            .iter()
            .map(|(fname, ty)| (fname.clone(), self.replace_vars(ty, &mapping)))
            .collect();
        let result_ty = Type::Con(
            name.into(),
            info.type_params
                .iter()
                .map(|id| mapping[id].clone())
                .collect(),
        );
        (fields, result_ty)
    }

    /// Enter an isolated effect scope. Saves and clears current_effects,
    /// effect_type_param_cache, field_candidates, resume_type, and
    /// resume_return_type. Call `exit_effect_scope` to restore and collect
    /// what the scope accumulated.
    pub(crate) fn enter_effect_scope(&mut self) -> EffectScope {
        EffectScope {
            effects: std::mem::take(&mut self.effect_state.current),
            effect_cache: std::mem::take(&mut self.effect_state.type_param_cache),
            field_candidates: std::mem::take(&mut self.field_candidates),
            resume_type: self.resume_type.take(),
            resume_return_type: self.resume_return_type.take(),
        }
    }

    /// Exit an effect scope, restoring saved state and returning what
    /// accumulated during the scope's lifetime.
    pub(crate) fn exit_effect_scope(&mut self, scope: EffectScope) -> EffectScopeResult {
        let result = EffectScopeResult {
            effects: std::mem::replace(&mut self.effect_state.current, scope.effects),
            effect_cache: std::mem::replace(
                &mut self.effect_state.type_param_cache,
                scope.effect_cache,
            ),
            field_candidates: std::mem::replace(
                &mut self.field_candidates,
                scope.field_candidates,
            ),
        };
        self.resume_type = scope.resume_type;
        self.resume_return_type = scope.resume_return_type;
        result
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

}

// Re-export from unify module so other files can use `super::collect_free_vars`
pub(crate) use unify::collect_free_vars;
use unify::rename_vars;
