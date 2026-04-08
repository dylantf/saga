mod builtins;
mod check_decl;
mod check_module;
pub use check_module::{BUILTIN_MODULES, ModuleMap, builtin_module_source, scan_project_modules};
mod check_traits;
mod effects;
pub(crate) mod exhaustiveness;
mod handlers;
mod infer;
mod patterns;
mod records;
mod resolve;
mod result;
mod unify;
pub use result::{CheckResult, LetDictInfo};

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, ExprKind, NodeId};
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

/// A single entry in an effect row.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectEntry {
    /// Canonical effect name: `State`, `Std.Log.Log`, etc.
    pub name: String,
    /// Type arguments: `[Int]` in `State Int`
    pub args: Vec<Type>,
}

impl EffectEntry {
    pub fn unnamed(name: String, args: Vec<Type>) -> Self {
        EffectEntry { name, args }
    }

    /// Two entries are in the same effect family if they share a canonical name.
    pub fn matches(&self, other: &EffectEntry) -> bool {
        self.name == other.name
    }

    pub fn same_instantiation(&self, other: &EffectEntry) -> bool {
        self.name == other.name && self.args == other.args
    }
}

/// An effect row: a list of known effects plus an optional row variable (tail).
/// When `tail` is `None`, the row is closed (no additional effects allowed).
/// When `tail` is `Some(id)`, the row is open (additional effects unify with the variable).
#[derive(Debug, Clone, PartialEq)]
pub struct EffectRow {
    pub effects: Vec<EffectEntry>,
    pub tail: Option<Box<Type>>,
}

impl EffectRow {
    pub fn closed(effects: Vec<EffectEntry>) -> Self {
        EffectRow {
            effects,
            tail: None,
        }
    }

    /// Empty closed row (pure -- no effects).
    pub fn empty() -> Self {
        EffectRow {
            effects: vec![],
            tail: None,
        }
    }

    /// True if this is a closed row with no effects.
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty() && self.tail.is_none()
    }

    pub fn tail_var_id(&self) -> Option<u32> {
        match &self.tail {
            Some(ty) => match ty.as_ref() {
                Type::Var(id) => Some(*id),
                _ => None,
            },
            None => None,
        }
    }

    /// Merge two closed effect rows, preserving distinct instantiations of the
    /// same effect family.
    pub fn merge(&self, other: &EffectRow) -> EffectRow {
        let mut effects = self.effects.clone();
        for entry in &other.effects {
            if !effects.iter().any(|e| e.same_instantiation(entry)) {
                effects.push(entry.clone());
            }
        }
        EffectRow {
            effects,
            tail: None,
        }
    }

    /// Remove handled effects by family name.
    pub fn subtract(&self, handled: &std::collections::HashSet<String>) -> EffectRow {
        let effects = self
            .effects
            .iter()
            .filter(|e| !handled.contains(&e.name))
            .cloned()
            .collect();
        EffectRow {
            effects,
            tail: self.tail.clone(),
        }
    }

    /// Remove handled effects by exact instantiation.
    pub fn subtract_entries(&self, handled: &[EffectEntry]) -> EffectRow {
        let effects = self
            .effects
            .iter()
            .filter(|entry| !handled.iter().any(|h| h.same_instantiation(entry)))
            .cloned()
            .collect();
        EffectRow {
            effects,
            tail: self.tail.clone(),
        }
    }
}

/// Internal type representation used during inference.
/// Separate from ast::TypeExpr, which is surface syntax.
/// All types (including primitives like Int, Bool) are represented as `Con`.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// Unification variable, solved during inference
    Var(u32),
    /// Function type: a -> b with effect row.
    /// Every function carries an effect row. Pure functions have an empty closed row.
    /// Effectful functions have their effects listed, optionally with an open tail.
    Fun(Box<Type>, Box<Type>, EffectRow),
    /// Named type constructor with args: Int = Con("Int", []), List a = Con("List", [a])
    Con(std::string::String, Vec<Type>),
    /// Anonymous record type: `{ street: String, city: String }`
    /// Fields are sorted by name for canonical comparison.
    Record(Vec<(std::string::String, Type)>),
    /// Error recovery type: unifies with everything, suppresses cascading errors.
    Error,
}

/// Convenience constructors for built-in types
impl Type {
    /// Pure function type: a -> b with empty closed effect row.
    pub fn arrow(a: Type, b: Type) -> Type {
        Type::Fun(Box::new(a), Box::new(b), EffectRow::closed(vec![]))
    }
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
            Type::Fun(a, b, row) => {
                match a.as_ref() {
                    Type::Fun(_, _, _) => write!(f, "({}) -> {}", a, b)?,
                    _ => write!(f, "{} -> {}", a, b)?,
                }
                if !row.effects.is_empty() || row.tail.is_some() {
                    write!(f, " needs {{")?;
                    for (i, entry) in row.effects.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", entry.name)?;
                        for arg in &entry.args {
                            write!(f, " {}", arg)?;
                        }
                    }
                    if let Some(tail) = &row.tail {
                        if !row.effects.is_empty() {
                            write!(f, ", ")?;
                        }
                        write!(f, "..{}", tail)?;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
            }
            Type::Con(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else if name == "Tuple" && args.len() >= 2 {
                    // Display as (A, B, ...) instead of Tuple A B
                    write!(f, "(")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")
                } else {
                    write!(f, "{}", name)?;
                    for arg in args {
                        // Wrap multi-arg type applications in parens for readability,
                        // but not tuples (they already render as (A, B))
                        match arg {
                            Type::Con(n, inner_args) if !inner_args.is_empty() && n != "Tuple" => {
                                write!(f, " ({})", arg)?;
                            }
                            _ => write!(f, " {}", arg)?,
                        }
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
        }
    }
}

// --- Substitution ---

/// Maps type variable IDs to their solved types.
#[derive(Debug, Default, Clone)]
pub struct Substitution {
    map: HashMap<u32, Type>,
    /// Row variable bindings for effect row polymorphism.
    pub(crate) row_map: HashMap<u32, EffectRow>,
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
            Type::Fun(a, b, row) => Type::Fun(
                Box::new(self.apply(a)),
                Box::new(self.apply(b)),
                self.apply_effect_row(row),
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
        }
    }

    /// Apply the substitution to an effect row, resolving type args and chasing
    /// row variable bindings.
    pub fn apply_effect_row(&self, row: &EffectRow) -> EffectRow {
        let mut effects: Vec<EffectEntry> = row
            .effects
            .iter()
            .map(|entry| EffectEntry {
                name: entry.name.clone(),
                args: entry.args.iter().map(|t| self.apply(t)).collect(),
            })
            .collect();
        let mut tail = row.tail.as_ref().map(|t| Box::new(self.apply(t)));
        // Chase row variable bindings
        while let Some(tail_ty) = &tail {
            if let Type::Var(tail_id) = tail_ty.as_ref()
                && let Some(bound) = self.row_map.get(tail_id)
            {
                for entry in &bound.effects {
                    effects.push(EffectEntry {
                        name: entry.name.clone(),
                        args: entry.args.iter().map(|t| self.apply(t)).collect(),
                    });
                }
                tail = bound.tail.clone();
                continue;
            }
            break;
        }
        EffectRow { effects, tail }
    }

    /// Resolve a type variable to its binding, without recursively applying
    /// to the whole type structure. Just chases Var -> Var chains.
    pub fn resolve_var<'a>(&'a self, ty: &'a Type) -> &'a Type {
        let mut current = ty;
        while let Type::Var(id) = current {
            if let Some(resolved) = self.map.get(id) {
                current = resolved;
            } else {
                break;
            }
        }
        current
    }

    /// Bind a row variable to an effect row, with occurs check.
    pub(crate) fn bind_row(&mut self, id: u32, row: EffectRow) -> Result<(), Diagnostic> {
        if let Some(tail_id) = row.tail_var_id()
            && tail_id == id
        {
            // Binding to itself (e.g., ..e = ..e) is a no-op
            if row.effects.is_empty() {
                return Ok(());
            }
            return Err(Diagnostic::error(format!(
                "infinite effect row: ?{} occurs in its own binding",
                id
            )));
        }
        self.row_map.insert(id, row);
        Ok(())
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
            Type::Fun(a, b, row) => {
                self.occurs(id, a)
                    || self.occurs(id, b)
                    || row
                        .effects
                        .iter()
                        .any(|entry| entry.args.iter().any(|t| self.occurs(id, t)))
            }
            Type::Con(_, args) => args.iter().any(|a| self.occurs(id, a)),
            Type::Record(fields) => fields.iter().any(|(_, ty)| self.occurs(id, ty)),
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
    /// Trait constraints: (trait_name, self_type_var_id, extra_type_arg_types).
    /// Extra types are empty for single-param traits like Show.
    /// For multi-param traits like `ConvertTo a b`, the extras track `b` as Type::Var.
    /// Concrete type args like `ConvertTo Int` are stored as Type::Con.
    pub constraints: Vec<(String, u32, Vec<Type>)>,
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
        for (trait_name, var_id, extra_types) in &self.constraints {
            let var_name = names
                .get(var_id)
                .cloned()
                .unwrap_or_else(|| format!("?{}", var_id));
            let trait_display = if extra_types.is_empty() {
                trait_name.clone()
            } else {
                let extra_names: Vec<String> = extra_types
                    .iter()
                    .map(|ty| match ty {
                        Type::Var(id) => {
                            names.get(id).cloned().unwrap_or_else(|| format!("?{}", id))
                        }
                        other => format!("{}", rename_vars(other, &names)),
                    })
                    .collect();
                format!("{} {}", trait_name, extra_names.join(" "))
            };
            bounds.entry(var_name).or_default().push(trait_display);
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
pub use check_module::{EffectDef, EffectOpDef, ModuleCodegenInfo, ModuleExports, TraitImplDict};

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
        Type::Fun(a, b, row) => {
            free_vars_in_type(a, bound, out);
            free_vars_in_type(b, bound, out);
            for entry in &row.effects {
                for t in &entry.args {
                    free_vars_in_type(t, bound, out);
                }
            }
            if let Some(tail) = &row.tail {
                free_vars_in_type(tail, bound, out);
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
    /// Canonical name of the effect this op belongs to.
    pub effect_name: std::string::String,
    pub params: Vec<(String, Type)>,
    pub return_type: Type,
    /// Effect requirements declared on this op (e.g. `spawn` needs `{Actor msg, ..e}`).
    pub needs: EffectRow,
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

/// Handler where constraint key: (effect_name, param_index).
/// Value: list of (trait_name, extra_type_arg_var_ids).
pub type HandlerWhereConstraints = HashMap<(String, usize), Vec<(String, Vec<u32>)>>;

#[derive(Debug, Clone)]
pub struct HandlerInfo {
    /// Which effects this handler handles
    pub effects: Vec<std::string::String>,
    /// Frozen return clause: (param_type, body_type). Sub-applied at register time so
    /// internal handler vars are resolved but forall vars remain free.
    pub return_type: Option<(Type, Type)>,
    /// Effects the handler's arm bodies perform (from `needs` clause).
    /// Frozen at registration; free vars are in `forall` and instantiated fresh at each usage.
    pub needs_effects: EffectRow,
    /// Type vars to instantiate fresh at each usage site (polymorphic handler params).
    pub forall: Vec<u32>,
    /// op_name -> span of the handler arm (for LSP go-to-def and with-stack)
    pub arm_spans: HashMap<String, Span>,
    /// Trait constraints from `where` clause, keyed by (effect_name, param_index).
    /// Each constraint is (trait_name, extra_type_arg_var_ids).
    /// E.g. `handler h for Store a where {a: Show}` -> {("Store", 0) -> [("Show", [])]}
    /// E.g. `handler h for State a where {a: ConvertTo b}` -> {("State", 0) -> [("ConvertTo", [b_var_id])]}
    pub where_constraints: HandlerWhereConstraints,
    /// Which module this handler is defined in (None = main file).
    pub source_module: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TraitInfo {
    /// Type parameters: first is self, rest are extras.
    /// e.g. `trait ConvertTo a b` -> ["a", "b"]
    pub type_params: Vec<String>,
    pub supertraits: Vec<String>,
    /// Method signatures: name -> (param_types, return_type, trait_self_param_var_id)
    pub methods: Vec<(String, Vec<Type>, Type, Option<u32>)>,
}

#[derive(Debug, Clone)]
pub struct ImplInfo {
    /// Constraints on type parameters: (trait_name, param_index)
    /// e.g. Show for List requires Show on param 0 (the element type)
    pub param_constraints: Vec<(String, usize)>,
    /// Extra type arguments applied to the trait (e.g. ["NOK"] in `impl ConvertTo NOK for USD`).
    /// Empty for single-param traits.
    pub trait_type_args: Vec<String>,
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
    /// Resolved extra type arguments for multi-param traits.
    /// e.g. for `ConvertTo NOK`, this holds [Type::Con("NOK", [])].
    /// Empty for single-param traits.
    pub trait_type_args: Vec<Type>,
}

/// Warnings deferred until after inference, when substitutions are complete.
#[derive(Clone)]
pub enum PendingWarning {
    /// A non-unit value was discarded in a block (not the last statement).
    DiscardedValue { span: Span, ty: Type },
    /// A local variable binding was never referenced.
    UnusedVariable { span: Span, name: String },
    /// A module-level function was never referenced.
    UnusedFunction { span: Span, name: String },
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
    /// Functions whose bodies produce handlers, so applications like
    /// `make_state 0` can preserve handler metadata such as return clauses.
    pub(crate) handler_funs: HashMap<std::string::String, HandlerInfo>,
    /// Context for resume typing: when inside a handler arm, the return type of the op being handled
    pub(crate) resume_type: Option<Type>,
    /// Context for resume return typing: when inside a handler arm, the answer type of the with-expression
    pub(crate) resume_return_type: Option<Type>,
    /// Metadata for effect inference (instantiation caches, declared rows, name registries).
    pub(crate) effect_meta: EffectMeta,
    /// Effect accumulator: effects from the current scope are pushed here automatically
    /// during inference. Isolation scopes (handlers, lambdas) save/restore this field.
    pub(crate) effect_row: EffectRow,
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
    /// Name resolution map: user-visible names -> canonical names.
    pub(crate) scope_map: ScopeMap,
    /// Evidence collected during constraint solving for the elaboration pass.
    pub(crate) evidence: Vec<TraitEvidence>,
    /// Dict params for let bindings with trait constraints.
    /// Keyed by (name, pat_node_id) to avoid collisions between same-named
    /// bindings in different scopes (e.g. multiple test bodies).
    pub(crate) let_dict_params: HashMap<(String, NodeId), result::LetDictInfo>,
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
    /// Import declarations from the prelude (passed through to lowerer).
    pub prelude_imports: Vec<crate::ast::Decl>,
    /// Set to true when a `with ets_ref` handler is encountered, signalling
    /// that the `dylang_ref_store` ETS table must be created at startup.
    pub(crate) needs_ets_ref_table: bool,
    /// Set to true when a `with beam_vec` handler is encountered, signalling
    /// that the `dylang_vec_store` ETS table must be created at startup.
    pub(crate) needs_vec_table: bool,
}

/// Maps user-visible name forms to canonical (module-qualified) names.
///
/// When `import Std.List as List exposing (map)` is processed, the ScopeMap gets:
///   values["Std.List.map"] = "Std.List.map"   (canonical)
///   values["List.map"]     = "Std.List.map"   (aliased)
///   values["map"]          = "Std.List.map"   (bare, because exposed)
///
/// This allows each binding to be stored once in the env under its canonical name,
/// with the ScopeMap handling all user-facing name form resolution.
#[derive(Debug, Clone, Default)]
pub struct ScopeMap {
    /// User-visible name -> canonical name for value bindings (functions, let bindings).
    pub values: HashMap<String, String>,
    /// User-visible name -> canonical name for handlers.
    pub handlers: HashMap<String, String>,
    /// User-visible name -> canonical (bare) name for type names.
    pub types: HashMap<String, String>,
    /// User-visible name -> canonical name for constructors.
    pub constructors: HashMap<String, String>,
    /// User-visible name -> canonical name for effects.
    pub effects: HashMap<String, String>,
    /// User-visible name -> canonical name for traits.
    pub traits: HashMap<String, String>,
    /// Canonical name -> source module name (e.g. "Std.List.map" -> "Std.List").
    /// Used by LSP to determine import origins without a separate parallel map.
    pub origins: HashMap<String, String>,
}

impl ScopeMap {
    pub fn resolve_value(&self, name: &str) -> Option<&str> {
        self.values.get(name).map(|s| s.as_str())
    }

    pub fn resolve_handler(&self, name: &str) -> Option<&str> {
        self.handlers.get(name).map(|s| s.as_str())
    }

    pub fn resolve_type(&self, name: &str) -> Option<&str> {
        self.types.get(name).map(|s| s.as_str())
    }

    pub fn resolve_constructor(&self, name: &str) -> Option<&str> {
        self.constructors.get(name).map(|s| s.as_str())
    }

    /// Find the shortest user-visible alias that maps to `canonical` in the given namespace.
    pub fn shortest_alias<'a>(
        &'a self,
        canonical: &str,
        namespace: &'a HashMap<String, String>,
    ) -> Option<&'a str> {
        namespace
            .iter()
            .filter(|(_, c)| c.as_str() == canonical)
            .map(|(alias, _)| alias.as_str())
            .min_by_key(|a| a.len())
    }

    pub fn resolve_effect(&self, name: &str) -> Option<&str> {
        self.effects.get(name).map(|s| s.as_str())
    }

    pub fn resolve_trait(&self, name: &str) -> Option<&str> {
        self.traits.get(name).map(|s| s.as_str())
    }

    /// Get the source module for a user-visible name, checking all name kinds.
    pub fn origin_of(&self, name: &str) -> Option<&str> {
        // Resolve the user-visible name to canonical, then look up origin
        let canonical = self
            .values
            .get(name)
            .or_else(|| self.handlers.get(name))
            .or_else(|| self.constructors.get(name))
            .or_else(|| self.effects.get(name))
            .or_else(|| self.traits.get(name))
            .or_else(|| self.types.get(name));
        if let Some(canon) = canonical {
            self.origins.get(canon).map(|s| s.as_str())
        } else {
            // Name might already be canonical
            self.origins.get(name).map(|s| s.as_str())
        }
    }

    /// Check if a user-visible name is an import (has an origin in scope_map).
    pub fn is_import(&self, name: &str) -> bool {
        self.origin_of(name).is_some()
    }

    /// Register a name under its canonical and (optionally) aliased qualified forms.
    ///
    /// Inserts `"Module.Name" -> "Module.Name"` (canonical) and, when the alias
    /// prefix differs from the module name, `"Alias.Name" -> "Module.Name"`.
    pub fn register_qualified(
        map: &mut HashMap<String, String>,
        module_name: &str,
        prefix: &str,
        bare_name: &str,
    ) {
        let canonical = format!("{}.{}", module_name, bare_name);
        map.entry(canonical.clone())
            .or_insert_with(|| canonical.clone());
        if prefix != module_name {
            let aliased = format!("{}.{}", prefix, bare_name);
            map.entry(aliased).or_insert_with(|| canonical);
        }
    }

    /// Merge another scope_map into this one (first-insert-wins).
    pub fn merge(&mut self, other: &ScopeMap) {
        for (k, v) in &other.values {
            self.values.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.handlers {
            self.handlers.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.types {
            self.types.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.constructors {
            self.constructors
                .entry(k.clone())
                .or_insert_with(|| v.clone());
        }
        for (k, v) in &other.effects {
            self.effects.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.traits {
            self.traits.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.origins {
            self.origins.entry(k.clone()).or_insert_with(|| v.clone());
        }
    }
}

/// Trait system state: definitions, impl registry, deferred constraints, where bounds.
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Trait definitions: trait name -> info.
    pub traits: HashMap<String, TraitInfo>,
    /// Impl registry: (trait_name, trait_type_args, target_type) -> impl info.
    pub impls: HashMap<(String, Vec<String>, String), ImplInfo>,
    /// Pending trait constraints to check: (trait_name, trait_type_arg_types, self_type, span, node_id).
    /// trait_type_arg_types is empty for single-param traits.
    pub pending_constraints: Vec<(String, Vec<Type>, Type, Span, crate::ast::NodeId)>,
    /// Where clause bounds: var_id -> set of trait names assumed satisfied.
    pub where_bounds: HashMap<u32, HashSet<String>>,
    /// Reverse map from type var ID to original type parameter name (for polymorphic evidence).
    pub where_bound_var_names: HashMap<u32, String>,
}

/// Metadata for effect inference: instantiation caches and name registries.
/// Effect accumulation lives on Checker.effect_row.
#[derive(Clone, Default)]
pub(crate) struct EffectMeta {
    /// Per-scope cache of instantiated effect type params: effect name -> mapping
    /// from original var IDs to fresh vars. Ensures all ops from the same effect
    /// share type params within a function scope.
    pub type_param_cache: HashMap<String, HashMap<u32, Type>>,
    /// Registry of locally defined function names. Not used for effect tracking
    /// (the accumulator + absorption handle that). Only read at the CheckResult
    /// boundary to build fun_effects for codegen. See docs/remove-known-funs-registry.md.
    pub known_funs: HashSet<String>,
    /// Annotation-provided effect type constraints: fn name -> [(effect_name, [concrete types])].
    pub fun_type_constraints: HashMap<String, Vec<(String, Vec<Type>)>>,
    /// Registry of let bindings with deferred effects. Same story as known_funs:
    /// only read at the CheckResult boundary for codegen, not for effect tracking.
    pub known_let_bindings: HashSet<String>,
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
    /// Top-level function definitions: (NodeId, name, span, is_public) for unused function detection.
    pub fun_definitions: Vec<(crate::ast::NodeId, String, Span, bool)>,
    /// Stack of (op_name -> (arm_span, source_module)) maps for nested `with` expressions.
    /// Innermost handler is last. Used to record which arm handles each effect call.
    pub with_arm_stacks: Vec<HashMap<String, (Span, Option<String>)>>,
    /// Maps effect call span -> (handler arm span, source module) (for LSP go-to-def, level 1).
    pub effect_call_targets: HashMap<Span, (Span, Option<String>)>,
    /// Maps handler arm span -> (effect op definition span, source module) (for LSP go-to-def, level 2).
    pub handler_arm_targets: HashMap<Span, (Span, Option<String>)>,
    /// Type/effect name references: (span, name) pairs for all type names in annotations,
    /// type expressions, effect refs, etc. Used for find-references on type/effect names.
    pub type_references: Vec<(Span, String)>,
    /// Doc comments from imported declarations: name -> doc lines.
    pub imported_docs: HashMap<String, Vec<String>>,
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
    pub(crate) base_trait_impls: HashMap<(String, Vec<String>, String), ImplInfo>,
    /// Modules currently being typechecked (cycle detection).
    pub(crate) loading: HashSet<String>,
}

/// Per-variable record candidate narrowing: var_id -> (candidate record names, span).
pub(crate) type FieldCandidates = HashMap<u32, (Vec<String>, Span)>;

/// Snapshot of inference state saved when entering an isolated scope (function
/// body, lambda, with-expression, handler arm) and restored on exit.
pub(crate) struct InferScope {
    pub(crate) effect_cache: HashMap<String, HashMap<u32, Type>>,
    pub(crate) field_candidates: FieldCandidates,
    resume_type: Option<Type>,
    resume_return_type: Option<Type>,
}

/// What accumulated inside an InferScope while it was active.
pub(crate) struct InferScopeResult {
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
            handler_funs: HashMap::new(),
            resume_type: None,
            resume_return_type: None,
            effect_meta: EffectMeta::default(),
            effect_row: EffectRow::empty(),
            trait_state: TraitState::default(),
            field_candidates: HashMap::new(),
            modules: ModuleContext::default(),
            adt_variants: HashMap::new(),
            type_arity: HashMap::new(),
            scope_map: ScopeMap::default(),
            evidence: Vec::new(),
            let_dict_params: HashMap::new(),
            collected_diagnostics: Vec::new(),
            pending_warnings: Vec::new(),
            lsp: LspState::default(),
            allow_bodyless_annotations: false,
            current_module: None,
            prelude_imports: Vec::new(),
            needs_ets_ref_table: false,
            needs_vec_table: false,
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
        crate::desugar::desugar_program(&mut prelude_program);
        checker
            .check_program_inner(&mut prelude_program)
            .map_err(|errs| errs.into_iter().next().unwrap())?;

        // Save the prelude's import declarations so the lowerer can register
        // only the names the prelude actually exposes.
        checker.prelude_imports = prelude_program
            .into_iter()
            .filter(|d| matches!(d, crate::ast::Decl::Import { .. }))
            .collect();

        checker.modules.prelude_snapshot = Some(Box::new(checker.clone()));
        Ok(checker)
    }

    /// Remove a module's cached exports and trait impls from this checker.
    /// Used by the LSP to avoid false "duplicate impl" errors when re-checking
    /// a stdlib file that was already loaded via the prelude.
    pub fn evict_module(&mut self, module_name: &str) {
        if let Some(exports) = self.modules.exports.remove(module_name) {
            for key in exports.trait_impls.keys() {
                self.trait_state.impls.remove(key);
            }
        }
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

    /// Record a type/effect name reference from an EffectRef AST node.
    pub(crate) fn record_effect_ref(&mut self, effect_ref: &crate::ast::EffectRef) {
        let name_end = effect_ref.span.start + effect_ref.name.len();
        self.lsp.type_references.push((
            Span {
                start: effect_ref.span.start,
                end: name_end,
            },
            effect_ref.name.clone(),
        ));
    }

    /// Emit warnings for module-level functions that are never referenced.
    pub(crate) fn check_unused_functions(&mut self) {
        let used: std::collections::HashSet<crate::ast::NodeId> =
            self.lsp.references.values().copied().collect();
        for (def_id, name, span, public) in &self.lsp.fun_definitions {
            if *public || name == "main" || name.starts_with('_') {
                continue;
            }
            if !used.contains(def_id) {
                self.pending_warnings.push(PendingWarning::UnusedFunction {
                    span: *span,
                    name: name.clone(),
                });
            }
        }
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
                    let is_unit =
                        matches!(&resolved, Type::Con(n, args) if n == "Unit" && args.is_empty());
                    if !is_unit && !matches!(resolved, Type::Var(_) | Type::Error) {
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
                PendingWarning::UnusedFunction { span, name } => {
                    self.collected_diagnostics.push(Diagnostic::warning_at(
                        span,
                        format!("unused function: `{}`", name),
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

    pub fn module_map(&self) -> Option<&check_module::ModuleMap> {
        self.modules.map.as_ref()
    }

    /// Typecheck a module by name, triggering the full dependency walk.
    /// Used for library builds where there is no Main.dy entry point.
    pub fn typecheck_import_by_name(&mut self, module_name: &str) {
        let parts: Vec<String> = module_name.split('.').map(|s| s.to_string()).collect();
        let span = crate::token::Span { start: 0, end: 0 };
        if let Err(e) = self.typecheck_import(&parts, None, None, span) {
            eprintln!("Error typechecking module '{}': {}", module_name, e);
            std::process::exit(1);
        }
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

    /// Push effects onto the accumulator, deduplicating by name.
    pub(crate) fn emit_effects(&mut self, effs: &EffectRow) {
        for entry in &effs.effects {
            if !self
                .effect_row
                .effects
                .iter()
                .any(|e| e.same_instantiation(entry))
            {
                self.effect_row.effects.push(entry.clone());
            }
        }
    }

    /// Push a single named effect onto the accumulator, deduplicating by exact instantiation.
    pub(crate) fn emit_effect(&mut self, name: String, args: Vec<Type>) {
        if !self
            .effect_row
            .effects
            .iter()
            .any(|e| e.name == name && e.args == args)
        {
            self.effect_row
                .effects
                .push(EffectEntry::unnamed(name, args));
        }
    }

    pub(crate) fn current_effect_args(&self, effect_name: &str) -> Vec<Type> {
        let Some(info) = self.effects.get(effect_name) else {
            return vec![];
        };
        let Some(cache) = self.effect_meta.type_param_cache.get(effect_name) else {
            return vec![];
        };
        info.type_params
            .iter()
            .filter_map(|param_id| cache.get(param_id))
            .map(|ty| self.sub.apply(ty))
            .collect()
    }

    pub(crate) fn prettify_effect_entry(&self, entry: &EffectEntry) -> String {
        let short = entry
            .name
            .rsplit('.')
            .next()
            .unwrap_or(entry.name.as_str())
            .to_string();
        format!(
            "{}",
            self.prettify_type(&Type::Con(short, entry.args.clone()))
        )
    }

    /// Save the current effect accumulator and start a fresh one.
    /// Returns the saved EffectRow so the caller can restore it later.
    pub(crate) fn save_effects(&mut self) -> EffectRow {
        std::mem::replace(&mut self.effect_row, EffectRow::empty())
    }

    /// Restore a previously saved effect accumulator, returning what
    /// accumulated since the save.
    pub(crate) fn restore_effects(&mut self, saved: EffectRow) -> EffectRow {
        std::mem::replace(&mut self.effect_row, saved)
    }

    /// Enter an isolated inference scope. Saves and clears
    /// effect_type_param_cache, field_candidates, resume_type, and
    /// resume_return_type. Call `exit_scope` to restore and collect
    /// what the scope accumulated.
    pub(crate) fn enter_scope(&mut self) -> InferScope {
        InferScope {
            effect_cache: std::mem::take(&mut self.effect_meta.type_param_cache),
            field_candidates: std::mem::take(&mut self.field_candidates),
            resume_type: self.resume_type.take(),
            resume_return_type: self.resume_return_type.take(),
        }
    }

    /// Exit an inference scope, restoring saved state and returning what
    /// accumulated during the scope's lifetime.
    pub(crate) fn exit_scope(&mut self, scope: InferScope) -> InferScopeResult {
        let result = InferScopeResult {
            effect_cache: std::mem::replace(
                &mut self.effect_meta.type_param_cache,
                scope.effect_cache,
            ),
            field_candidates: std::mem::replace(&mut self.field_candidates, scope.field_candidates),
        };
        self.resume_type = scope.resume_type;
        self.resume_return_type = scope.resume_return_type;
        result
    }
}

/// Extract all effect names from a type by walking Fun nodes' effect rows.
pub fn effects_from_type(ty: &Type) -> HashSet<String> {
    let mut effects = HashSet::new();
    fn walk(ty: &Type, out: &mut HashSet<String>) {
        if let Type::Fun(_, ret, row) = ty {
            for entry in &row.effects {
                out.insert(entry.name.clone());
            }
            walk(ret, out);
        }
    }
    walk(ty, &mut effects);
    effects
}

/// Collect exact effect entries from a callback parameter type's effect rows.
/// For `() -> a needs {Fail String, Log}`, collects those concrete entries.
/// Only collects statically declared row entries (not row variables).
pub fn collect_callback_effect_entries(ty: &Type, out: &mut Vec<EffectEntry>) {
    if let Type::Fun(_, ret, row) = ty {
        for entry in &row.effects {
            if !out.iter().any(|seen| seen.same_instantiation(entry)) {
                out.push(entry.clone());
            }
        }
        collect_callback_effect_entries(ret, out);
    }
}

/// Collect effect names from a callback parameter type's effect rows.
/// For `() -> a needs {Fail, Log}`, collects `{"Fail", "Log"}`.
/// Only collects from closed-row effects (not row variables).
pub fn collect_callback_effects(ty: &Type, out: &mut HashSet<String>) {
    if let Type::Fun(_, ret, row) = ty {
        for entry in &row.effects {
            out.insert(entry.name.clone());
        }
        collect_callback_effects(ret, out);
    }
}

// Re-export from unify module so other files can use `super::collect_free_vars`
pub(crate) use unify::collect_free_vars;
use unify::rename_vars;
