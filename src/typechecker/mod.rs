mod check_decl;
mod check_module;
mod check_traits;
pub(crate) mod exhaustiveness;
mod infer;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use crate::ast::Expr;
use crate::token::Span;

/// Returns the span of the first effect call found in `expr`, if any.
/// Used to reject effect calls inside guard expressions.
pub(crate) fn find_effect_call(expr: &Expr) -> Option<Span> {
    match expr {
        Expr::EffectCall { span, .. } => Some(*span),
        Expr::App { func, arg, .. } => find_effect_call(func).or_else(|| find_effect_call(arg)),
        Expr::BinOp { left, right, .. } => {
            find_effect_call(left).or_else(|| find_effect_call(right))
        }
        Expr::UnaryMinus { expr, .. } => find_effect_call(expr),
        Expr::If {
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
    /// Function type with effect annotation: a -> b needs {Eff}
    /// Used for HOF parameter types that declare which effects they absorb.
    /// Unification treats EffArrow the same as Arrow (effects are not unified).
    EffArrow(Box<Type>, Box<Type>, Vec<String>),
    /// Named type constructor with args: Int = Con("Int", []), List a = Con("List", [a])
    Con(std::string::String, Vec<Type>),
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
        }
    }
}

// --- Substitution ---

/// Maps type variable IDs to their solved types.
#[derive(Debug, Default)]
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
                effs.clone(),
            ),
            Type::Con(name, args) => {
                Type::Con(name.clone(), args.iter().map(|a| self.apply(a)).collect())
            }
        }
    }

    /// Bind a type variable to a type, with occurs check.
    fn bind(&mut self, id: u32, ty: &Type) -> Result<(), TypeError> {
        if let Type::Var(other) = ty
            && *other == id
        {
            return Ok(());
        }

        if self.occurs(id, ty) {
            return Err(TypeError::new(format!(
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
            Type::Arrow(a, b) | Type::EffArrow(a, b, _) => self.occurs(id, a) || self.occurs(id, b),
            Type::Con(_, args) => args.iter().any(|a| self.occurs(id, a)),
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

// --- Module codegen info ---

/// Information about a module's exports needed by the lowerer/codegen.
/// Populated during typechecking alongside `tc_loaded`.
#[derive(Debug, Clone, Default)]
pub struct ModuleCodegenInfo {
    /// Public type bindings: name -> scheme (same data as tc_loaded).
    pub exports: Vec<(String, Scheme)>,
    /// Public effect definitions: effect name -> (ops as (op_name, param_count), type_param_count).
    pub effect_defs: Vec<(String, Vec<(String, usize)>, usize)>,
    /// Public record definitions: record name -> ordered field names.
    pub record_fields: Vec<(String, Vec<String>)>,
    /// Public handler names.
    pub handler_defs: Vec<String>,
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
        Type::Arrow(a, b) | Type::EffArrow(a, b, _) => {
            free_vars_in_type(a, bound, out);
            free_vars_in_type(b, bound, out);
        }
        Type::Con(_, args) => {
            for arg in args {
                free_vars_in_type(arg, bound, out);
            }
        }
    }
}

// --- Errors ---

#[derive(Debug, Clone)]
pub struct TypeError {
    pub message: std::string::String,
    pub span: Option<Span>,
}

impl TypeError {
    pub(crate) fn new(message: impl Into<std::string::String>) -> Self {
        TypeError {
            message: message.into(),
            span: None,
        }
    }

    pub(crate) fn at(span: Span, message: impl Into<std::string::String>) -> Self {
        TypeError {
            message: message.into(),
            span: Some(span),
        }
    }

    pub(crate) fn with_span(mut self, span: Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

// --- Internal types used by inference ---

#[derive(Debug, Clone)]
pub(crate) struct EffectOpSig {
    pub name: std::string::String,
    pub params: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub(crate) struct EffectDefInfo {
    /// Fresh var IDs for the effect's type parameters (empty for non-parameterized effects)
    pub type_params: Vec<u32>,
    pub ops: Vec<EffectOpSig>,
}

#[derive(Debug, Clone)]
pub(crate) struct HandlerInfo {
    /// Which effects this handler handles
    pub effects: Vec<std::string::String>,
    /// Return clause: (param_var_id, body_type). Used to compute the `with` expression type.
    pub return_type: Option<(u32, Type)>,
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
    pub span: Span,
    pub trait_name: String,
    /// The concrete type that satisfied the constraint.
    /// None if resolved via a where-bound type variable (polymorphic passthrough).
    pub resolved_type: Option<(String, Vec<Type>)>,
}

// --- Inference engine ---

pub struct Checker {
    pub(crate) next_var: u32,
    pub sub: Substitution,
    pub env: TypeEnv,
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
    /// Trait definitions: trait name -> info
    pub(crate) traits: HashMap<String, TraitInfo>,
    /// Impl registry: (trait_name, target_type) -> impl info
    pub(crate) trait_impls: HashMap<(String, String), ImplInfo>,
    /// Pending trait constraints to check: (trait_name, type, span)
    pub(crate) pending_constraints: Vec<(String, Type, Span)>,
    /// Per-variable record candidate narrowing for field access: var_id -> (candidate record names, span).
    /// Tracks which records are still candidates for an unresolved type variable based on
    /// the intersection of all fields accessed on it. Checked at end of each function body.
    pub(crate) field_candidates: HashMap<u32, (Vec<String>, Span)>,
    /// Where clause bounds: var_id -> set of trait names assumed satisfied
    pub(crate) where_bounds: HashMap<u32, HashSet<String>>,
    /// Project root for resolving imports. None = script mode.
    pub(crate) project_root: Option<std::path::PathBuf>,
    /// Cache of already-typechecked modules: module name -> public type bindings.
    pub(crate) tc_loaded: HashMap<String, Vec<(String, Scheme)>>,
    /// Cache of type->constructors maps for already-typechecked modules.
    pub(crate) tc_type_ctors: HashMap<String, HashMap<String, Vec<String>>>,
    /// Cache of codegen-relevant info for each typechecked module.
    pub tc_codegen_info: HashMap<String, ModuleCodegenInfo>,
    /// Cache of record definitions from typechecked modules: module name -> record name -> field types.
    pub(crate) tc_record_defs: HashMap<String, HashMap<String, Vec<(String, Type)>>>,
    /// Modules currently being typechecked (cycle detection).
    pub(crate) tc_loading: HashSet<String>,
    /// Reverse map: type name -> list of (constructor_name, arity) pairs (for exhaustiveness checking)
    pub(crate) adt_variants: HashMap<std::string::String, Vec<(std::string::String, usize)>>,
    /// Evidence collected during constraint solving for the elaboration pass.
    pub evidence: Vec<TraitEvidence>,
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
            traits: HashMap::new(),
            trait_impls: HashMap::new(),
            pending_constraints: Vec::new(),
            field_candidates: HashMap::new(),
            where_bounds: HashMap::new(),
            project_root: None,
            tc_loaded: HashMap::new(),
            tc_type_ctors: HashMap::new(),
            tc_codegen_info: HashMap::new(),
            tc_record_defs: HashMap::new(),
            tc_loading: HashSet::new(),
            adt_variants: HashMap::new(),
            evidence: Vec::new(),
        };
        checker.register_builtins();
        checker
    }

    pub fn with_project_root(root: std::path::PathBuf) -> Self {
        let mut checker = Self::new();
        checker.project_root = Some(root);
        checker
    }

    pub(crate) fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    fn register_builtins(&mut self) {
        // Built-in Show trait and impls for primitives
        self.traits.insert(
            "Show".into(),
            TraitInfo {
                type_param: "a".into(),
                supertraits: vec![],
                methods: vec![("show".into(), vec![Type::Var(u32::MAX)], Type::string())],
            },
        );
        for prim in &["Int", "Float", "String", "Bool", "Unit"] {
            self.trait_impls.insert(
                ("Show".into(), prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    span: None,
                },
            );
        }
        // Show for compound types requires Show on type params
        // List a: Show on param 0
        self.trait_impls.insert(
            ("Show".into(), "List".into()),
            ImplInfo {
                param_constraints: vec![("Show".into(), 0)],
                span: None,
            },
        );
        // Maybe a: Show on param 0
        self.trait_impls.insert(
            ("Show".into(), "Maybe".into()),
            ImplInfo {
                param_constraints: vec![("Show".into(), 0)],
                span: None,
            },
        );
        // Result a b: Show on params 0 and 1
        self.trait_impls.insert(
            ("Show".into(), "Result".into()),
            ImplInfo {
                param_constraints: vec![("Show".into(), 0), ("Show".into(), 1)],
                span: None,
            },
        );

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

        // Built-in Ord trait (<, >, <=, >=)
        self.traits.insert(
            "Ord".into(),
            TraitInfo {
                type_param: "a".into(),
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float", "String"] {
            self.trait_impls.insert(
                ("Ord".into(), prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    span: None,
                },
            );
        }

        // print : Show a => a -> Unit
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.env.insert(
            "print".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![("Show".into(), a_id)],
                ty: Type::Arrow(Box::new(a), Box::new(Type::unit())),
            },
        );

        // show : Show a => a -> String
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.env.insert(
            "show".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![("Show".into(), a_id)],
                ty: Type::Arrow(Box::new(a), Box::new(Type::string())),
            },
        );

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

        // Show for Dict k v: requires Show on both k and v
        self.trait_impls.insert(
            ("Show".into(), "Dict".into()),
            ImplInfo {
                param_constraints: vec![("Show".into(), 0), ("Show".into(), 1)],
                span: None,
            },
        );
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

        // Dict.put : forall k v. Eq k => k -> v -> Dict k v -> Dict k v
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
            self.env.insert(
                "Dict.put".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![("Eq".into(), k_id)],
                    ty: Type::Arrow(
                        Box::new(k),
                        Box::new(Type::Arrow(
                            Box::new(v),
                            Box::new(Type::Arrow(Box::new(dict_kv.clone()), Box::new(dict_kv))),
                        )),
                    ),
                },
            );
        }

        // Dict.remove : forall k v. Eq k => k -> Dict k v -> Dict k v
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
            self.env.insert(
                "Dict.remove".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![("Eq".into(), k_id)],
                    ty: Type::Arrow(
                        Box::new(k),
                        Box::new(Type::Arrow(Box::new(dict_kv.clone()), Box::new(dict_kv))),
                    ),
                },
            );
        }

        // Dict.keys : forall k v. Dict k v -> List k
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
            let dict_kv = Type::Con("Dict".into(), vec![k.clone(), v]);
            let list_k = Type::Con("List".into(), vec![k]);
            self.env.insert(
                "Dict.keys".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![],
                    ty: Type::Arrow(Box::new(dict_kv), Box::new(list_k)),
                },
            );
        }

        // Dict.values : forall k v. Dict k v -> List v
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
            let dict_kv = Type::Con("Dict".into(), vec![k, v.clone()]);
            let list_v = Type::Con("List".into(), vec![v]);
            self.env.insert(
                "Dict.values".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![],
                    ty: Type::Arrow(Box::new(dict_kv), Box::new(list_v)),
                },
            );
        }

        // Dict.size : forall k v. Dict k v -> Int
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
            let dict_kv = Type::Con("Dict".into(), vec![k, v]);
            self.env.insert(
                "Dict.size".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![],
                    ty: Type::Arrow(Box::new(dict_kv), Box::new(Type::int())),
                },
            );
        }

        // Dict.from_list : forall k v. Eq k => List (k, v) -> Dict k v
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
            let tuple_kv = Type::Con("Tuple".into(), vec![k.clone(), v.clone()]);
            let list_kv = Type::Con("List".into(), vec![tuple_kv]);
            let dict_kv = Type::Con("Dict".into(), vec![k, v]);
            self.env.insert(
                "Dict.from_list".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![("Eq".into(), k_id)],
                    ty: Type::Arrow(Box::new(list_kv), Box::new(dict_kv)),
                },
            );
        }

        // Dict.to_list : forall k v. Dict k v -> List (k, v)
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
            let tuple_kv = Type::Con("Tuple".into(), vec![k, v]);
            let list_kv = Type::Con("List".into(), vec![tuple_kv]);
            self.env.insert(
                "Dict.to_list".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![],
                    ty: Type::Arrow(Box::new(dict_kv), Box::new(list_kv)),
                },
            );
        }

        // Dict.member : forall k v. Eq k => k -> Dict k v -> Bool
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
            let dict_kv = Type::Con("Dict".into(), vec![k.clone(), v]);
            self.env.insert(
                "Dict.member".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![("Eq".into(), k_id)],
                    ty: Type::Arrow(
                        Box::new(k),
                        Box::new(Type::Arrow(Box::new(dict_kv), Box::new(Type::bool()))),
                    ),
                },
            );
        }
    }

    // --- Unification ---

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), TypeError> {
        let a = self.sub.apply(a);
        let b = self.sub.apply(b);

        match (&a, &b) {
            _ if a == b => Ok(()),

            (Type::Var(id), _) => self.sub.bind(*id, &b),
            (_, Type::Var(id)) => self.sub.bind(*id, &a),

            (Type::Arrow(a1, a2), Type::Arrow(b1, b2))
            | (Type::Arrow(a1, a2), Type::EffArrow(b1, b2, _))
            | (Type::EffArrow(a1, a2, _), Type::Arrow(b1, b2))
            | (Type::EffArrow(a1, a2, _), Type::EffArrow(b1, b2, _)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)
            }

            (Type::Con(n1, args1), Type::Con(n2, args2))
                if n1 == n2 && args1.len() == args2.len() =>
            {
                for (a, b) in args1.iter().zip(args2.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }

            _ => Err(TypeError::new(format!(
                "type mismatch: expected {}, got {}",
                a, b
            ))),
        }
    }

    /// Unify with span context: if unification fails, attach the span to the error.
    pub(crate) fn unify_at(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), TypeError> {
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
                effs.clone(),
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter().map(|a| self.replace_vars(a, mapping)).collect(),
            ),
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
                    let effect_names: Vec<String> = needs.iter().map(|e| e.name.clone()).collect();
                    Type::EffArrow(Box::new(a_ty), Box::new(b_ty), effect_names)
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
        Type::Arrow(a, b) | Type::EffArrow(a, b, _) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
        }
        Type::Con(_, args) => {
            for arg in args {
                collect_free_vars(arg, out);
            }
        }
    }
}
