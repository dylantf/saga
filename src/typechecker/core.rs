use std::collections::HashMap;

use super::rename_vars;
use crate::ast::Kind;
use crate::token::Span;

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

/// An effect row: a list of known effects plus zero or more row variables
/// (tails). The row denotes the *union* of its named effects and all of its
/// tail variables.
///
/// When `tails` is empty, the row is closed (no additional effects allowed).
/// When `tails` is non-empty, the row is open: each tail variable independently
/// stands for a set of additional effects. A row with several tails
/// (`needs {..a, ..b}`) forwards the union of multiple independent open rows;
/// each binds independently during unification.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectRow {
    pub effects: Vec<EffectEntry>,
    pub tails: Vec<Type>,
}

impl EffectRow {
    pub fn closed(effects: Vec<EffectEntry>) -> Self {
        EffectRow {
            effects,
            tails: vec![],
        }
    }

    /// Empty closed row (pure -- no effects).
    pub fn empty() -> Self {
        EffectRow {
            effects: vec![],
            tails: vec![],
        }
    }

    /// True if this is a closed row with no effects.
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty() && self.tails.is_empty()
    }

    /// True if the row has at least one open tail.
    pub fn is_open(&self) -> bool {
        !self.tails.is_empty()
    }

    /// The variable IDs of all tails that are bare type variables, in order.
    pub fn tail_var_ids(&self) -> Vec<u32> {
        self.tails
            .iter()
            .filter_map(|t| match t {
                Type::Var(id) => Some(*id),
                _ => None,
            })
            .collect()
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
            tails: vec![],
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
            tails: self.tails.clone(),
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
            tails: self.tails.clone(),
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
    /// Type-level symbol literal: `'Foo` at the source level. Inhabits kind `Symbol`.
    /// Two `Symbol(a)` and `Symbol(b)` are equal iff `a == b`.
    Symbol(std::string::String),
    /// Error recovery type: unifies with everything, suppresses cascading errors.
    Error,
}

/// Information stored about a registered `type alias`. The body is the
/// fully-converted `Type` produced from the alias's RHS using the alias's
/// parameter variables as positional placeholders. At each use site,
/// `convert_type_expr` substitutes the parameter variables with the
/// provided argument types and yields a fresh `Type` with the alias erased.
#[derive(Debug, Clone)]
pub struct TypeAliasInfo {
    /// Positional parameter variable IDs (matching the order of `type_params`).
    pub param_vars: Vec<u32>,
    /// Positional parameter kinds (mirrors `type_param_kinds` for this alias).
    pub param_kinds: Vec<Kind>,
    /// Pre-converted RHS, expressed in terms of `param_vars`.
    pub body: Type,
    /// Source span of the alias declaration.
    pub span: crate::token::Span,
}

/// Maps bare builtin type names to their canonical (module-qualified) forms.
/// This is the single source of truth for which module each builtin type belongs to.
pub const BUILTIN_TYPE_CANONICAL: &[(&str, &str)] = &[
    ("Int", "Std.Int.Int"),
    ("Float", "Std.Float.Float"),
    ("String", "Std.String.String"),
    ("Bool", "Std.Bool.Bool"),
    ("Unit", "Std.Base.Unit"),
    ("List", "Std.List.List"),
    ("Dict", "Std.Dict.Dict"),
    ("Set", "Std.Set.Set"),
    ("BitString", "Std.BitString.BitString"),
    ("Tuple", "Std.Base.Tuple"),
    ("Handler", "Std.Base.Handler"),
    // Types defined in stdlib .saga files but referenced in the typechecker
    ("Maybe", "Std.Maybe.Maybe"),
    ("Result", "Std.Result.Result"),
    ("Ordering", "Std.Base.Ordering"),
    ("Pid", "Std.Actor.Pid"),
    ("ExitReason", "Std.Actor.ExitReason"),
];

/// Resolve a bare builtin type name to its canonical form.
/// Returns the input unchanged if it's not a known builtin.
pub fn canonicalize_type_name(name: &str) -> &str {
    BUILTIN_TYPE_CANONICAL
        .iter()
        .find(|(bare, _)| *bare == name)
        .map(|(_, canonical)| *canonical)
        .unwrap_or(name)
}

/// Check if a name is the canonical form of a known builtin type.
/// Catches names like `"Std.Base.Tuple"` that were canonicalized by the
/// resolve pass but aren't registered in type_arity (variadic types).
pub fn is_builtin_canonical(name: &str) -> bool {
    BUILTIN_TYPE_CANONICAL
        .iter()
        .any(|(_, canonical)| *canonical == name)
}

/// Get the bare (user-facing) name from a canonical type name.
/// `"Std.Int.Int"` → `"Int"`, `"MyMod.Foo"` → `"Foo"`, `"Handler"` → `"Handler"`.
pub fn bare_type_name(canonical: &str) -> &str {
    canonical.rsplit('.').next().unwrap_or(canonical)
}

/// Mangle a canonical type name for use in Erlang identifiers (e.g. dict names).
/// Replaces dots with underscores: `"Std.Int.Int"` → `"Std_Int_Int"`.
pub fn mangle_type_name(canonical: &str) -> String {
    canonical.replace('.', "_")
}

/// Tuples are variable-arity: `(a, b)` and `(a, b, c)` are distinct concrete
/// types but share the canonical name `"Std.Base.Tuple"`. For impl keying and
/// dict naming we need to distinguish them, so suffix the canonical name with
/// the arity for tuple targets. Non-tuple names pass through unchanged.
pub fn arity_keyed_target_name(canonical: &str, arity: usize) -> String {
    if canonical == canonicalize_type_name("Tuple") {
        format!("{}.{}", canonical, arity)
    } else {
        canonical.to_string()
    }
}

/// Build a dict constructor name from canonical trait name, type args, erlang module, and target type.
/// Both `elaborate.rs` and `check_module.rs` must produce identical names for the same impl.
pub fn make_dict_name(
    canonical_trait: &str,
    trait_type_args: &[String],
    erlang_module: &str,
    target_type: &str,
) -> String {
    let mangled_trait = mangle_type_name(canonical_trait);
    let type_args_suffix = if trait_type_args.is_empty() {
        String::new()
    } else {
        format!("_{}", trait_type_args.join("_"))
    };
    let mangled_type = mangle_type_name(target_type);
    if erlang_module.is_empty() {
        format!(
            "__dict_{}{}_{}",
            mangled_trait, type_args_suffix, mangled_type
        )
    } else {
        format!(
            "__dict_{}{}_{}_{}",
            mangled_trait, type_args_suffix, erlang_module, mangled_type
        )
    }
}

/// Convenience constructors for built-in types
impl Type {
    /// Pure function type: a -> b with empty closed effect row.
    pub fn arrow(a: Type, b: Type) -> Type {
        Type::Fun(Box::new(a), Box::new(b), EffectRow::closed(vec![]))
    }
    pub fn con(name: &str) -> Type {
        Type::Con(canonicalize_type_name(name).into(), vec![])
    }
    pub fn int() -> Type {
        Type::con(canonicalize_type_name("Int"))
    }
    pub fn float() -> Type {
        Type::con(canonicalize_type_name("Float"))
    }
    pub fn string() -> Type {
        Type::con(canonicalize_type_name("String"))
    }
    pub fn bool() -> Type {
        Type::con(canonicalize_type_name("Bool"))
    }
    pub fn unit() -> Type {
        Type::con(canonicalize_type_name("Unit"))
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
                if !row.effects.is_empty() || !row.tails.is_empty() {
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
                    for (i, tail) in row.tails.iter().enumerate() {
                        if !row.effects.is_empty() || i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "..{}", tail)?;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
            }
            Type::Con(name, args) => {
                let display_name = bare_type_name(name);
                let is_tuple = display_name == "Tuple";
                if args.is_empty() {
                    write!(f, "{}", display_name)
                } else if is_tuple && args.len() >= 2 {
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
                    write!(f, "{}", display_name)?;
                    for arg in args {
                        // Wrap multi-arg type applications in parens for readability,
                        // but not tuples (they already render as (A, B))
                        match arg {
                            Type::Con(n, inner_args)
                                if !inner_args.is_empty() && bare_type_name(n) != "Tuple" =>
                            {
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
            Type::Symbol(name) => write!(f, "'{}", name),
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

    /// Number of solved type-variable bindings. Grows monotonically as
    /// inference progresses, so it doubles as a cheap "did the solver make
    /// progress?" signal for the pending-constraint worklist.
    pub fn solved_count(&self) -> usize {
        self.map.len()
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
            Type::Symbol(_) => ty.clone(),
            Type::Error => Type::Error,
        }
    }

    /// Apply the substitution to an effect row, resolving type args and chasing
    /// row variable bindings.
    pub fn apply_effect_row(&self, row: &EffectRow) -> EffectRow {
        let mut effects: Vec<EffectEntry> = vec![];
        let push_effect = |effects: &mut Vec<EffectEntry>, entry: &EffectEntry| {
            let resolved = EffectEntry {
                name: entry.name.clone(),
                args: entry.args.iter().map(|t| self.apply(t)).collect(),
            };
            if !effects.iter().any(|e| e.same_instantiation(&resolved)) {
                effects.push(resolved);
            }
        };
        for entry in &row.effects {
            push_effect(&mut effects, entry);
        }

        // Chase each tail's row-variable binding independently, accumulating
        // effects and collecting the leftover (still-unbound) tails. Each tail
        // binds independently, so two tails can resolve to disjoint effect sets.
        let mut out_tails: Vec<Type> = vec![];
        let mut seen_tail_ids: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut worklist: std::collections::VecDeque<Type> =
            row.tails.iter().map(|t| self.apply(t)).collect();
        while let Some(tail_ty) = worklist.pop_front() {
            match &tail_ty {
                Type::Var(tail_id) => {
                    if let Some(bound) = self.row_map.get(tail_id) {
                        for entry in &bound.effects {
                            push_effect(&mut effects, entry);
                        }
                        for t in &bound.tails {
                            worklist.push_back(self.apply(t));
                        }
                    } else if seen_tail_ids.insert(*tail_id) {
                        out_tails.push(tail_ty);
                    }
                }
                // A non-variable tail can't be chased further; keep it.
                _ => out_tails.push(tail_ty),
            }
        }
        EffectRow {
            effects,
            tails: out_tails,
        }
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
        let mentions_self = row
            .tails
            .iter()
            .any(|t| matches!(t, Type::Var(v) if *v == id));
        if mentions_self {
            // Binding a row variable to a row that only mentions itself
            // (e.g. `..e = ..e`) is a no-op.
            let only_self = row.effects.is_empty()
                && row
                    .tails
                    .iter()
                    .all(|t| matches!(t, Type::Var(v) if *v == id));
            if only_self {
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
    pub(crate) fn bind(&mut self, id: u32, ty: &Type) -> Result<(), Diagnostic> {
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
            Type::Symbol(_) => false,
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
    pub(crate) fn free_vars(&self, sub: &Substitution) -> Vec<u32> {
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
            for tail in &row.tails {
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
        Type::Symbol(_) => {}
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
