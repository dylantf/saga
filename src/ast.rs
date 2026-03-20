use std::sync::atomic::{AtomicU32, Ordering};

use crate::token::Span;

pub type Program = Vec<Decl>;

static NEXT_NODE_ID: AtomicU32 = AtomicU32::new(1);

/// Unique identifier for an expression node. Every node (parsed or synthetic)
/// gets a globally unique ID via `NodeId::fresh()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);

impl NodeId {
    pub fn fresh() -> Self {
        NodeId(NEXT_NODE_ID.fetch_add(1, Ordering::Relaxed))
    }
}

/// A reference to an effect, optionally with type arguments.
/// e.g. `Log` (no args), `State Int`, `State (MVector a)`
#[derive(Debug, Clone, PartialEq)]
pub struct EffectRef {
    pub name: String,
    pub type_args: Vec<TypeExpr>,
    pub span: Span,
}

// --- Top-level ---

#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub declarations: Vec<Decl>,
}

// --- Declarations ---

/// An item in an import exposing list: `import Foo (bar, Baz)`.
/// Capital names are treated as types and hoist their constructors automatically.
pub type ExposedItem = String;

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// `pub fun add (a: Int) (b: Int) -> Int needs {Log} where {a: Show + Eq}`
    FunAnnotation {
        id: NodeId,
        public: bool,
        name: String,
        name_span: Span,
        params: Vec<(String, TypeExpr)>,
        return_type: TypeExpr,
        effects: Vec<EffectRef>,
        /// `where {a: Show + Eq, b: Ord}` - trait bounds on type variables
        where_clause: Vec<TraitBound>,
        span: Span,
    },

    /// `add x y = x + y` or `main () = { ... }`
    FunBinding {
        id: NodeId,
        name: String,
        name_span: Span,
        params: Vec<Pat>,
        guard: Option<Box<Expr>>,
        body: Expr,
        span: Span,
    },

    Let {
        id: NodeId,
        name: String,
        annotation: Option<TypeExpr>,
        value: Expr,
        span: Span,
    },

    /// `type Option a { Some(a), None }`
    TypeDef {
        id: NodeId,
        public: bool,
        opaque: bool,
        name: String,
        name_span: Span,
        type_params: Vec<String>,
        variants: Vec<TypeConstructor>,
        deriving: Vec<String>,
        span: Span,
    },

    /// `record User { name: String, age: Int }`
    /// `record Box a { value: a }`
    RecordDef {
        id: NodeId,
        public: bool,
        name: String,
        name_span: Span,
        type_params: Vec<String>,
        fields: Vec<(String, TypeExpr)>,
        deriving: Vec<String>,
        span: Span,
    },

    /// `effect Console { fun print (msg: String) -> Unit }`
    /// `effect State s { fun get () -> s; fun put (val: s) -> Unit }`
    EffectDef {
        id: NodeId,
        public: bool,
        name: String,
        name_span: Span,
        type_params: Vec<String>,
        operations: Vec<EffectOp>,
        span: Span,
    },

    /// `handler console_log for Log needs {Http} { ... }`
    /// `handler counter for State Int { ... }`
    HandlerDef {
        id: NodeId,
        public: bool,
        name: String,
        name_span: Span,
        effects: Vec<EffectRef>,
        needs: Vec<EffectRef>,
        arms: Vec<HandlerArm>,
        /// Partially parsed arms from error recovery (for LSP hover, not typechecked).
        recovered_arms: Vec<HandlerArm>,
        /// `return value = Ok(value)` clause
        return_clause: Option<Box<HandlerArm>>,
        span: Span,
    },

    /// `trait Show a { fun show (x: a) -> String }`
    TraitDef {
        id: NodeId,
        public: bool,
        name: String,
        name_span: Span,
        type_param: String,
        supertraits: Vec<String>,
        methods: Vec<TraitMethod>,
        span: Span,
    },

    /// `impl Show for User { show user = ... }`
    /// `impl Store for Redis needs {Http, Fail} { ... }`
    ImplDef {
        id: NodeId,
        trait_name: String,
        target_type: String,
        type_params: Vec<String>,
        where_clause: Vec<TraitBound>,
        needs: Vec<EffectRef>,
        methods: Vec<(String, Vec<Pat>, Expr)>,
        span: Span,
    },

    /// `@external("erlang", "lists", "reverse") pub fun reverse (list: List a) -> List a`
    ExternalFun {
        id: NodeId,
        public: bool,
        name: String,
        /// Target runtime, e.g. "erlang"
        runtime: String,
        /// Erlang module name, e.g. "lists"
        module: String,
        /// Erlang function name, e.g. "reverse"
        func: String,
        params: Vec<(String, TypeExpr)>,
        return_type: TypeExpr,
        effects: Vec<EffectRef>,
        where_clause: Vec<TraitBound>,
        span: Span,
    },

    /// `import Math exposing { abs, max }`
    Import {
        id: NodeId,
        module_path: Vec<String>,
        alias: Option<String>,
        exposing: Option<Vec<ExposedItem>>,
        span: Span,
    },

    /// `module Foo.Bar`
    ModuleDecl {
        id: NodeId,
        path: Vec<String>,
        span: Span,
    },

    // --- Elaboration-only (never produced by the parser) ---
    /// Synthesized dictionary constructor function for a trait impl.
    /// e.g. `__dict_Describe_User` returns a tuple of method functions.
    DictConstructor {
        id: NodeId,
        name: String,
        /// Parameters for sub-dictionaries (conditional impls like `Show for List a where {a: Show}`)
        dict_params: Vec<String>,
        /// Method implementations as lambda expressions, ordered by trait method declaration order
        methods: Vec<Expr>,
        span: Span,
    },
}

// --- Expressions ---

/// An expression node with a unique identity and source location.
#[derive(Debug, Clone)]
pub struct Expr {
    pub id: NodeId,
    pub span: Span,
    pub kind: ExprKind,
}

impl Expr {
    /// Create a synthetic Expr with a fresh unique NodeId.
    /// Used by elaboration, derive, normalize, and codegen passes.
    pub fn synth(span: Span, kind: ExprKind) -> Self {
        Expr {
            id: NodeId::fresh(),
            span,
            kind,
        }
    }
}

/// PartialEq compares kind only. Span is source metadata, NodeId is
/// internal bookkeeping; neither contributes to semantic equality.
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// `42`, `3.14`, `"hello"`, `True`
    Lit { value: Lit },

    /// `foo`, `x'`
    Var { name: String },

    /// `Option`, `Some` -- uppercase identifiers
    Constructor { name: String },

    /// `f x y` -- function application (curried)
    App { func: Box<Expr>, arg: Box<Expr> },

    /// `x + y`, `a == b`, `s <> t`
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    /// `-x` (negation)
    UnaryMinus { expr: Box<Expr> },

    /// `if cond then a else b`
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },

    /// `case expr { Pat -> Expr, ... }`
    Case {
        scrutinee: Box<Expr>,
        arms: Vec<CaseArm>,
    },

    /// `{ stmt1; stmt2; expr }`
    Block { stmts: Vec<Stmt> },

    /// `fun x -> x + 1`
    Lambda { params: Vec<Pat>, body: Box<Expr> },

    /// `user.name`
    FieldAccess { expr: Box<Expr>, field: String },

    /// `User { name: "Dylan", age: 30 }`
    RecordCreate {
        name: String,
        fields: Vec<(String, Expr)>,
    },

    /// `{ street: "Main St", city: "Portland" }` (anonymous record)
    AnonRecordCreate {
        fields: Vec<(String, Expr)>,
    },

    /// `{ user | age: user.age + 1 }`
    RecordUpdate {
        record: Box<Expr>,
        fields: Vec<(String, Expr)>,
    },

    /// `log! "hello"`, `Cache.get! key`
    EffectCall {
        name: String,
        /// Optional namespace qualifier: `Cache` in `Cache.get!`
        qualifier: Option<String>,
        args: Vec<Expr>,
    },

    /// `expr with handler_name` or `expr with { ... }`
    With {
        expr: Box<Expr>,
        handler: Box<Handler>,
    },

    /// `resume value`
    Resume { value: Box<Expr> },

    /// `(a, b)`, `(1, "hello", True)`
    Tuple { elements: Vec<Expr> },

    /// `Math.abs` - module-qualified name lookup
    QualifiedName { module: String, name: String },

    /// `do { Pat <- expr ... SuccessExpr } else { Pat -> expr ... }`
    Do {
        bindings: Vec<(Pat, Expr)>,
        success: Box<Expr>,
        else_arms: Vec<CaseArm>,
    },

    /// `receive { Pat -> body, after N -> timeout_body }`
    Receive {
        arms: Vec<CaseArm>,
        /// Optional (timeout_expr, timeout_body)
        after_clause: Option<(Box<Expr>, Box<Expr>)>,
    },

    /// `(expr : Type)` -- inline type annotation / ascription
    Ascription {
        expr: Box<Expr>,
        type_expr: TypeExpr,
    },

    // --- Elaboration-only (never produced by the parser) ---
    /// Extract a method from a dictionary tuple (does not apply it).
    /// Lowered to `erlang:element(method_index+1, dict)`.
    DictMethodAccess {
        dict: Box<Expr>,
        method_index: usize,
    },
    /// Reference to a dictionary value (a variable holding a dict, or a dict constructor name).
    DictRef { name: String },
    /// Call an Erlang BIF. Only produced by elaboration, never by the parser.
    ForeignCall {
        module: String,
        func: String,
        args: Vec<Expr>,
    },
}

impl Expr {
    /// Returns true if this expression contains a `resume` call anywhere in it.
    pub fn contains_resume(&self) -> bool {
        match &self.kind {
            ExprKind::Resume { .. } => true,
            ExprKind::Block { stmts, .. } => stmts.iter().any(|s| s.contains_resume()),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                cond.contains_resume()
                    || then_branch.contains_resume()
                    || else_branch.contains_resume()
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => scrutinee.contains_resume() || arms.iter().any(|a| a.body.contains_resume()),
            ExprKind::Lambda { body, .. } => body.contains_resume(),
            ExprKind::App { func, arg, .. } => func.contains_resume() || arg.contains_resume(),
            ExprKind::BinOp { left, right, .. } => {
                left.contains_resume() || right.contains_resume()
            }
            ExprKind::UnaryMinus { expr, .. } => expr.contains_resume(),
            ExprKind::Tuple { elements, .. } => elements.iter().any(|e| e.contains_resume()),
            ExprKind::FieldAccess { expr, .. } => expr.contains_resume(),
            ExprKind::RecordCreate { fields, .. }
            | ExprKind::AnonRecordCreate { fields, .. } => {
                fields.iter().any(|(_, e)| e.contains_resume())
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                record.contains_resume() || fields.iter().any(|(_, e)| e.contains_resume())
            }
            // Only check the `with` body, not the handler arm bodies: `resume` inside
            // an arm body refers to *that arm's* continuation, not the outer context's.
            ExprKind::With { expr, .. } => expr.contains_resume(),
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                bindings.iter().any(|(_, e)| e.contains_resume())
                    || success.contains_resume()
                    || else_arms.iter().any(|a| a.body.contains_resume())
            }
            ExprKind::EffectCall { args, .. } => args.iter().any(|e| e.contains_resume()),
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                arms.iter().any(|a| a.body.contains_resume())
                    || after_clause
                        .as_ref()
                        .is_some_and(|(t, b)| t.contains_resume() || b.contains_resume())
            }
            ExprKind::Ascription { expr, .. } => expr.contains_resume(),
            ExprKind::ForeignCall { args, .. } => args.iter().any(|e| e.contains_resume()),
            ExprKind::DictMethodAccess { dict, .. } => dict.contains_resume(),
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => false,
        }
    }
}

// --- Statements (inside blocks) ---

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// `let x = expr`, `let x: Type = expr`, or `let (a, b) = expr`
    Let {
        pattern: Pat,
        annotation: Option<TypeExpr>,
        value: Expr,
        assert: bool,
        span: Span,
    },

    /// `let f x y = body` -- local function definition (may be multi-clause)
    LetFun {
        id: NodeId,
        name: String,
        name_span: Span,
        params: Vec<Pat>,
        guard: Option<Box<Expr>>,
        body: Expr,
        span: Span,
    },

    /// Expression used as a statement (last one is the block's value)
    Expr(Expr),
}

impl Stmt {
    pub fn contains_resume(&self) -> bool {
        match self {
            Stmt::Let { value, .. } => value.contains_resume(),
            Stmt::LetFun { body, guard, .. } => {
                body.contains_resume() || guard.as_ref().is_some_and(|g| g.contains_resume())
            }
            Stmt::Expr(e) => e.contains_resume(),
        }
    }
}

// --- Patterns ---

#[derive(Debug, Clone, PartialEq)]
pub enum Pat {
    /// `_`
    Wildcard { id: NodeId, span: Span },

    /// `x`, `name`
    Var {
        id: NodeId,
        name: String,
        span: Span,
    },

    /// `42`, `"hello"`, `True`
    Lit { id: NodeId, value: Lit, span: Span },

    /// `Some(x)`, `Cons(a, b)`
    Constructor {
        id: NodeId,
        name: String,
        args: Vec<Pat>,
        span: Span,
    },

    /// `Success { status, body }` or `ApiError { code: c }`
    /// Optional `as` binding: `Student { name } as s` or `Student as s`
    Record {
        id: NodeId,
        name: String,
        fields: Vec<(String, Option<Pat>)>, // (field_name, optional alias pattern)
        as_name: Option<String>,
        span: Span,
    },

    /// `{ street, city }` (anonymous record destructure)
    AnonRecord {
        id: NodeId,
        fields: Vec<(String, Option<Pat>)>,
        span: Span,
    },

    /// `(a, b)`, `(x, y, z)`
    Tuple {
        id: NodeId,
        elements: Vec<Pat>,
        span: Span,
    },

    /// `"prefix" <> rest` -- string prefix pattern
    StringPrefix {
        id: NodeId,
        prefix: String,
        rest: Box<Pat>,
        span: Span,
    },
}

impl Pat {
    pub fn id(&self) -> NodeId {
        match self {
            Pat::Wildcard { id, .. }
            | Pat::Var { id, .. }
            | Pat::Lit { id, .. }
            | Pat::Constructor { id, .. }
            | Pat::Record { id, .. }
            | Pat::AnonRecord { id, .. }
            | Pat::Tuple { id, .. }
            | Pat::StringPrefix { id, .. } => *id,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Pat::Wildcard { span, .. }
            | Pat::Var { span, .. }
            | Pat::Lit { span, .. }
            | Pat::Constructor { span, .. }
            | Pat::Record { span, .. }
            | Pat::AnonRecord { span, .. }
            | Pat::Tuple { span, .. }
            | Pat::StringPrefix { span, .. } => *span,
        }
    }
}

// --- Types ---

#[derive(Debug, Clone)]
pub enum TypeExpr {
    /// Concrete type: `Int`, `String`, `Option`
    Named { name: String, span: Span },

    /// Type variable: `a`, `b`, `e`
    Var { name: String, span: Span },

    /// `Option a`, `Result a e`
    App { func: Box<TypeExpr>, arg: Box<TypeExpr>, span: Span },

    /// `a -> b` or `a -> b needs {Eff}` or `a -> b needs {State Int}`
    Arrow { from: Box<TypeExpr>, to: Box<TypeExpr>, effects: Vec<EffectRef>, span: Span },

    /// Anonymous record type: `{ street: String, city: String }`
    Record { fields: Vec<(String, TypeExpr)>, span: Span },
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named { span, .. }
            | TypeExpr::Var { span, .. }
            | TypeExpr::App { span, .. }
            | TypeExpr::Arrow { span, .. }
            | TypeExpr::Record { span, .. } => *span,
        }
    }
}

/// PartialEq compares structure only, ignoring spans (same as Expr).
impl PartialEq for TypeExpr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeExpr::Named { name: a, .. }, TypeExpr::Named { name: b, .. }) => a == b,
            (TypeExpr::Var { name: a, .. }, TypeExpr::Var { name: b, .. }) => a == b,
            (
                TypeExpr::App { func: f1, arg: a1, .. },
                TypeExpr::App { func: f2, arg: a2, .. },
            ) => f1 == f2 && a1 == a2,
            (
                TypeExpr::Arrow { from: f1, to: t1, effects: e1, .. },
                TypeExpr::Arrow { from: f2, to: t2, effects: e2, .. },
            ) => f1 == f2 && t1 == t2 && e1 == e2,
            (
                TypeExpr::Record { fields: f1, .. },
                TypeExpr::Record { fields: f2, .. },
            ) => f1 == f2,
            _ => false,
        }
    }
}

// --- Supporting types ---

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinOp {
    Add,      // +
    Sub,      // -
    Mul,      // *
    FloatDiv, // / (float division)
    IntDiv,   // / on Int (truncating integer division, emitted by elaboration)
    Mod,      // %
    Eq,       // ==
    NotEq,    // !=
    Lt,       // <
    Gt,       // >
    LtEq,     // <=
    GtEq,     // >=
    And,      // &&
    Or,       // ||
    Concat,   // <>
}

/// A constructor in a type definition, e.g. Some(a) or None
#[derive(Debug, Clone, PartialEq)]
pub struct TypeConstructor {
    pub id: NodeId,
    pub name: String,
    pub fields: Vec<(Option<String>, TypeExpr)>, // (optional label, type)
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseArm {
    pub pattern: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EffectOp {
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HandlerArm {
    pub op_name: String,
    pub params: Vec<(String, Span)>,
    pub body: Box<Expr>,
    pub span: Span,
}

/// `a: Show + Eq` in a `where` clause
#[derive(Debug, Clone, PartialEq)]
pub struct TraitBound {
    /// The type variable being constrained (e.g. `a`)
    pub type_var: String,
    /// The required traits (e.g. `["Show", "Eq"]`)
    pub traits: Vec<String>,
}

/// The handler in a `with` expression
#[derive(Debug, Clone, PartialEq)]
pub enum Handler {
    /// `expr with handler_name`
    Named(String, Span),
    /// `expr with { h1, h2, op args = body }`
    Inline {
        /// Named handler references (e.g. `h1, h2`)
        named: Vec<String>,
        /// Inline handler arms (e.g. `op args = body`)
        arms: Vec<HandlerArm>,
        /// `return value = Ok(value)` clause
        return_clause: Option<Box<HandlerArm>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub span: Span,
}
