use crate::token::Span;

pub type Program = Vec<Decl>;

/// A reference to an effect, optionally with type arguments.
/// e.g. `Log` (no args), `State Int`, `State (MVector a)`
#[derive(Debug, Clone, PartialEq)]
pub struct EffectRef {
    pub name: String,
    pub type_args: Vec<TypeExpr>,
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
        public: bool,
        name: String,
        params: Vec<(String, TypeExpr)>,
        return_type: TypeExpr,
        effects: Vec<EffectRef>,
        /// `where {a: Show + Eq, b: Ord}` - trait bounds on type variables
        where_clause: Vec<TraitBound>,
        span: Span,
    },

    /// `add x y = x + y` or `main () = { ... }`
    FunBinding {
        name: String,
        params: Vec<Pat>,
        guard: Option<Box<Expr>>,
        body: Expr,
        span: Span,
    },

    Let {
        name: String,
        annotation: Option<TypeExpr>,
        value: Expr,
        span: Span,
    },

    /// `type Option a { Some(a), None }`
    TypeDef {
        public: bool,
        name: String,
        type_params: Vec<String>,
        variants: Vec<TypeConstructor>,
        span: Span,
    },

    /// `record User { name: String, age: Int }`
    RecordDef {
        public: bool,
        name: String,
        fields: Vec<(String, TypeExpr)>,
        span: Span,
    },

    /// `effect Console { fun print (msg: String) -> Unit }`
    /// `effect State s { fun get () -> s; fun put (val: s) -> Unit }`
    EffectDef {
        public: bool,
        name: String,
        type_params: Vec<String>,
        operations: Vec<EffectOp>,
        span: Span,
    },

    /// `handler console_log for Log needs {Http} { ... }`
    /// `handler counter for State Int { ... }`
    HandlerDef {
        public: bool,
        name: String,
        effects: Vec<EffectRef>,
        needs: Vec<EffectRef>,
        arms: Vec<HandlerArm>,
        /// `return value -> Ok(value)` clause
        return_clause: Option<Box<HandlerArm>>,
        span: Span,
    },

    /// `trait Show a { fun show (x: a) -> String }`
    TraitDef {
        public: bool,
        name: String,
        type_param: String,
        supertraits: Vec<String>,
        methods: Vec<TraitMethod>,
        span: Span,
    },

    /// `impl Show for User { show user = ... }`
    /// `impl Store for Redis needs {Http, Fail} { ... }`
    ImplDef {
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
        module_path: Vec<String>,
        alias: Option<String>,
        exposing: Option<Vec<ExposedItem>>,
        span: Span,
    },

    /// `module Foo.Bar`
    ModuleDecl { path: Vec<String>, span: Span },

    // --- Elaboration-only (never produced by the parser) ---
    /// Synthesized dictionary constructor function for a trait impl.
    /// e.g. `__dict_Describe_User` returns a tuple of method functions.
    DictConstructor {
        name: String,
        /// Parameters for sub-dictionaries (conditional impls like `Show for List a where {a: Show}`)
        dict_params: Vec<String>,
        /// Method implementations as lambda expressions, ordered by trait method declaration order
        methods: Vec<Expr>,
        span: Span,
    },
}

// --- Expressions ---

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// `42`, `3.14`, `"hello"`, `True`
    Lit { value: Lit, span: Span },

    /// `foo`, `x'`
    Var { name: String, span: Span },

    /// `Option`, `Some` — uppercase identifiers
    Constructor { name: String, span: Span },

    /// `f x y` — function application (curried)
    App {
        func: Box<Expr>,
        arg: Box<Expr>,
        span: Span,
    },

    /// `x + y`, `a == b`, `s <> t`
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
        span: Span,
    },

    /// `-x` (negation)
    UnaryMinus { expr: Box<Expr>, span: Span },

    /// `if cond then a else b`
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
        span: Span,
    },

    /// `case expr { Pat -> Expr, ... }`
    Case {
        scrutinee: Box<Expr>,
        arms: Vec<CaseArm>,
        span: Span,
    },

    /// `{ stmt1; stmt2; expr }`
    Block { stmts: Vec<Stmt>, span: Span },

    /// `fun x -> x + 1`
    Lambda {
        params: Vec<Pat>,
        body: Box<Expr>,
        span: Span,
    },

    /// `user.name`
    FieldAccess {
        expr: Box<Expr>,
        field: String,
        span: Span,
    },

    /// `User { name: "Dylan", age: 30 }`
    RecordCreate {
        name: String,
        fields: Vec<(String, Expr)>,
        span: Span,
    },

    /// `{ user | age: user.age + 1 }`
    RecordUpdate {
        record: Box<Expr>,
        fields: Vec<(String, Expr)>,
        span: Span,
    },

    /// `log! "hello"`, `Cache.get! key`
    EffectCall {
        name: String,
        /// Optional namespace qualifier: `Cache` in `Cache.get!`
        qualifier: Option<String>,
        args: Vec<Expr>,
        span: Span,
    },

    /// `expr with handler_name` or `expr with { ... }`
    With {
        expr: Box<Expr>,
        handler: Box<Handler>,
        span: Span,
    },

    /// `resume value`
    Resume { value: Box<Expr>, span: Span },

    /// `(a, b)`, `(1, "hello", True)`
    Tuple { elements: Vec<Expr>, span: Span },

    /// `Math.abs` - module-qualified name lookup
    QualifiedName {
        module: String,
        name: String,
        span: Span,
    },

    /// `do { Pat <- expr ... SuccessExpr } else { Pat -> expr ... }`
    Do {
        bindings: Vec<(Pat, Expr)>,
        success: Box<Expr>,
        else_arms: Vec<CaseArm>,
        span: Span,
    },

    // --- Elaboration-only (never produced by the parser) ---
    /// Extract a method from a dictionary tuple (does not apply it).
    /// Lowered to `erlang:element(method_index+1, dict)`.
    DictMethodAccess {
        dict: Box<Expr>,
        method_index: usize,
        span: Span,
    },
    /// Reference to a dictionary value (a variable holding a dict, or a dict constructor name).
    DictRef { name: String, span: Span },
    /// Call an Erlang BIF. Only produced by elaboration, never by the parser.
    ForeignCall {
        module: String,
        func: String,
        args: Vec<Expr>,
        span: Span,
    },
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Lit { span, .. }
            | Expr::Var { span, .. }
            | Expr::Constructor { span, .. }
            | Expr::App { span, .. }
            | Expr::BinOp { span, .. }
            | Expr::UnaryMinus { span, .. }
            | Expr::If { span, .. }
            | Expr::Case { span, .. }
            | Expr::Block { span, .. }
            | Expr::Lambda { span, .. }
            | Expr::FieldAccess { span, .. }
            | Expr::RecordCreate { span, .. }
            | Expr::RecordUpdate { span, .. }
            | Expr::EffectCall { span, .. }
            | Expr::With { span, .. }
            | Expr::Resume { span, .. }
            | Expr::Tuple { span, .. }
            | Expr::QualifiedName { span, .. }
            | Expr::Do { span, .. }
            | Expr::DictMethodAccess { span, .. }
            | Expr::DictRef { span, .. }
            | Expr::ForeignCall { span, .. } => *span,
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
        span: Span,
    },

    /// Expression used as a statement (last one is the block's value)
    Expr(Expr),
}

// --- Patterns ---

#[derive(Debug, Clone, PartialEq)]
pub enum Pat {
    /// `_`
    Wildcard { span: Span },

    /// `x`, `name`
    Var { name: String, span: Span },

    /// `42`, `"hello"`, `True`
    Lit { value: Lit, span: Span },

    /// `Some(x)`, `Cons(a, b)`
    Constructor {
        name: String,
        args: Vec<Pat>,
        span: Span,
    },

    /// `Success { status, body }` or `ApiError { code: c }`
    Record {
        name: String,
        fields: Vec<(String, Option<Pat>)>, // (field_name, optional alias pattern)
        span: Span,
    },

    /// `(a, b)`, `(x, y, z)`
    Tuple { elements: Vec<Pat>, span: Span },

    /// `"prefix" <> rest` -- string prefix pattern
    StringPrefix {
        prefix: String,
        rest: Box<Pat>,
        span: Span,
    },
}

impl Pat {
    pub fn span(&self) -> Span {
        match self {
            Pat::Wildcard { span }
            | Pat::Var { span, .. }
            | Pat::Lit { span, .. }
            | Pat::Constructor { span, .. }
            | Pat::Record { span, .. }
            | Pat::Tuple { span, .. }
            | Pat::StringPrefix { span, .. } => *span,
        }
    }
}

// --- Types ---

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// Concrete type: `Int`, `String`, `Option`
    Named(String),

    /// Type variable: `a`, `b`, `e`
    Var(String),

    /// `Option a`, `Result a e`
    App(Box<TypeExpr>, Box<TypeExpr>),

    /// `a -> b` or `a -> b needs {Eff}` or `a -> b needs {State Int}`
    Arrow(Box<TypeExpr>, Box<TypeExpr>, Vec<EffectRef>),
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
    pub name: String,
    pub fields: Vec<TypeExpr>, // empty = bare variant like None
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
    pub params: Vec<String>,
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
    Named(String),
    /// `expr with { h1, h2, op args -> body }`
    Inline {
        /// Named handler references (e.g. `h1, h2`)
        named: Vec<String>,
        /// Inline handler arms (e.g. `op args -> body`)
        arms: Vec<HandlerArm>,
        /// `return value -> Ok(value)` clause
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
