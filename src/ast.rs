use crate::token::Span;

pub type Program = Vec<Decl>;

// --- Top-level ---

#[derive(Debug, Clone)]
pub struct Module {
    pub declarations: Vec<Decl>,
}

// --- Declarations ---

#[derive(Debug, Clone)]
pub enum Decl {
    /// `pub fun add (a: Int) (b: Int) -> Int`
    FunAnnotation {
        public: bool,
        name: String,
        params: Vec<(String, TypeExpr)>,
        return_type: TypeExpr,
        effects: Vec<String>,
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

    /// `let x = 42`
    Let {
        name: String,
        value: Expr,
        span: Span,
    },

    /// `type Option a { Some(a), None }`
    TypeDef {
        name: String,
        type_params: Vec<String>,
        variants: Vec<TypeConstructor>,
        span: Span,
    },

    /// `record User { name: String, age: Int }`
    RecordDef {
        name: String,
        fields: Vec<(String, TypeExpr)>,
        span: Span,
    },

    /// `effect Console { fun print (msg: String) -> Unit }`
    EffectDef {
        name: String,
        operations: Vec<EffectOp>,
        span: Span,
    },

    /// `handler std_io : Console { ... }`
    HandlerDef {
        name: String,
        effect: String,
        arms: Vec<HandlerArm>,
        span: Span,
    },

    /// `trait Show a { fun show (x: a) -> String }`
    TraitDef {
        name: String,
        type_param: String,
        supertraits: Vec<String>,
        methods: Vec<TraitMethod>,
        span: Span,
    },

    /// `impl Show for User { show user = ... }`
    ImplDef {
        trait_name: String,
        target_type: String,
        methods: Vec<(String, Vec<Pat>, Expr)>,
        span: Span,
    },

    /// `import Math exposing { abs, max }`
    Import {
        module_path: Vec<String>,
        alias: Option<String>,
        exposing: Option<Vec<String>>,
        span: Span,
    },

    /// `module Foo.Bar`
    ModuleDecl { path: Vec<String>, span: Span },
}

// --- Expressions ---

#[derive(Debug, Clone)]
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

    /// `User { name = "Dylan", age = 30 }`
    RecordCreate {
        name: String,
        fields: Vec<(String, Expr)>,
        span: Span,
    },

    /// `{ user | age = user.age + 1 }`
    RecordUpdate {
        record: Box<Expr>,
        fields: Vec<(String, Expr)>,
        span: Span,
    },

    /// `x |> f` / `f <| x`
    Pipe {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
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
            | Expr::Pipe { span, .. } => *span,
        }
    }
}

// --- Statements (inside blocks) ---

#[derive(Debug, Clone)]
pub enum Stmt {
    /// `let x = expr`
    Let {
        name: String,
        value: Expr,
        span: Span,
    },

    /// Expression used as a statement (last one is the block's value)
    Expr(Expr),
}

// --- Patterns ---

#[derive(Debug, Clone)]
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
}

// --- Types ---

#[derive(Debug, Clone)]
pub enum TypeExpr {
    /// Concrete type: `Int`, `String`, `Option`
    Named(String),

    /// Type variable: `a`, `b`, `e`
    Var(String),

    /// `Option a`, `Result a e`
    App(Box<TypeExpr>, Box<TypeExpr>),

    /// `a -> b`
    Arrow(Box<TypeExpr>, Box<TypeExpr>),
}

// --- Supporting types ---

#[derive(Debug, Clone)]
pub enum Lit {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Mod,    // %
    Eq,     // ==
    NotEq,  // !=
    Lt,     // <
    Gt,     // >
    LtEq,   // <=
    GtEq,   // >=
    And,    // &&
    Or,     // ||
    Concat, // <>
}

/// A constructor in a type definition, e.g. Some(a) or None
#[derive(Debug, Clone)]
pub struct TypeConstructor {
    pub name: String,
    pub fields: Vec<TypeExpr>, // empty = bare variant like None
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CaseArm {
    pub pattern: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EffectOp {
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct HandlerArm {
    pub op_name: String,
    pub params: Vec<String>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TraitMethod {
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub span: Span,
}
