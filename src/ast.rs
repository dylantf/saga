use std::sync::atomic::{AtomicU32, Ordering};

pub use crate::token::Trivia;
use crate::token::{Span, StringKind};

pub type Program = Vec<Decl>;

/// An AST node wrapped with leading trivia and an optional trailing comment.
/// PartialEq compares the inner node only (trivia is formatting metadata).
#[derive(Debug, Clone)]
pub struct Annotated<T> {
    pub node: T,
    pub leading_trivia: Vec<Trivia>,
    pub trailing_comment: Option<String>,
    /// Own-line comments that follow this node (before a blank line boundary).
    /// Only populated at the program declaration level.
    pub trailing_trivia: Vec<Trivia>,
}

impl<T: PartialEq> PartialEq for Annotated<T> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl<T> Annotated<T> {
    /// Wrap a node with no trivia.
    pub fn bare(node: T) -> Self {
        Annotated {
            node,
            leading_trivia: Vec::new(),
            trailing_comment: None,
            trailing_trivia: Vec::new(),
        }
    }
}

/// Strip `Annotated` wrappers from a vec, returning just the inner nodes.
pub fn strip_vec<T>(items: Vec<Annotated<T>>) -> Vec<T> {
    items.into_iter().map(|a| a.node).collect()
}

/// A program with trivia annotations preserved for formatting.
#[derive(Debug, Clone)]
pub struct AnnotatedProgram {
    pub declarations: Vec<Annotated<Decl>>,
    /// Comments/blank lines after the last declaration (end of file)
    pub trailing_trivia: Vec<Trivia>,
}

/// A method implementation inside an `impl` block.
#[derive(Debug, Clone, PartialEq)]
pub struct ImplMethod {
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Pat>,
    pub body: Expr,
}

/// Strip trivia annotations, returning plain declarations.
/// Transfers `Trivia::DocComment` items into each decl's `doc` field.
pub fn strip_annotations(annotated: AnnotatedProgram) -> Program {
    annotated
        .declarations
        .into_iter()
        .map(|ann| {
            let mut decl = ann.node;
            let docs: Vec<String> = ann
                .leading_trivia
                .into_iter()
                .filter_map(|t| match t {
                    Trivia::DocComment(text) => Some(text),
                    _ => None,
                })
                .collect();
            if !docs.is_empty() {
                set_decl_doc(&mut decl, docs);
            }
            decl
        })
        .collect()
}

/// Attach doc comments to a declaration node (if it supports them).
pub fn set_decl_doc(decl: &mut Decl, doc: Vec<String>) {
    match decl {
        Decl::FunSignature { doc: d, .. }
        | Decl::Val { doc: d, .. }
        | Decl::TypeDef { doc: d, .. }
        | Decl::RecordDef { doc: d, .. }
        | Decl::EffectDef { doc: d, .. }
        | Decl::HandlerDef { doc: d, .. }
        | Decl::TraitDef { doc: d, .. }
        | Decl::ImplDef { doc: d, .. } => *d = doc,
        _ => {}
    }
}

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

// --- Annotations ---

/// A compile-time annotation attached to a declaration, e.g. `@external("erlang", "lists", "reverse")`.
#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub name: String,
    pub name_span: Span,
    pub args: Vec<Lit>,
    pub span: Span,
}

// --- Declarations ---

/// An item in an import exposing list: `import Foo (bar, Baz)`.
/// Capital names are treated as types and hoist their constructors automatically.
pub type ExposedItem = String;

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// `pub fun add : (a: Int) -> (b: Int) -> Int needs {Log} where {a: Show, Eq}`
    FunSignature {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        name: String,
        name_span: Span,
        params: Vec<(String, TypeExpr)>,
        return_type: TypeExpr,
        effects: Vec<EffectRef>,
        /// Row variable for open effect rows, e.g. `..e` in `needs {Assert, ..e}`
        effect_row_var: Option<(String, Span)>,
        /// `where {a: Show + Eq, b: Ord}` - trait bounds on type variables
        where_clause: Vec<TraitBound>,
        /// Compile-time annotations, e.g. `@external("erlang", "lists", "reverse")`
        annotations: Vec<Annotation>,
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
        name_span: Span,
        annotation: Option<TypeExpr>,
        value: Expr,
        span: Span,
    },

    /// `val pi = 3.14159` or `pub val version = "1.0.0"`
    Val {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        name: String,
        name_span: Span,
        annotations: Vec<Annotation>,
        value: Expr,
        span: Span,
    },

    /// `type Option a { Some(a), None }`
    TypeDef {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        opaque: bool,
        name: String,
        name_span: Span,
        type_params: Vec<String>,
        variants: Vec<Annotated<TypeConstructor>>,
        deriving: Vec<String>,
        /// True if any `|` was on a new line - preserve multi-line layout.
        multiline: bool,
        span: Span,
    },

    /// `record User { name: String, age: Int }`
    /// `record Box a { value: a }`
    RecordDef {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        name: String,
        name_span: Span,
        type_params: Vec<String>,
        fields: Vec<Annotated<(String, TypeExpr)>>,
        deriving: Vec<String>,
        /// True if any field was on a new line — preserve multi-line layout.
        multiline: bool,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
        span: Span,
    },

    /// `effect Console { fun print : (msg: String) -> Unit }`
    /// `effect State s { fun get : Unit -> s; fun put (val: s) -> Unit }`
    EffectDef {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        name: String,
        name_span: Span,
        type_params: Vec<String>,
        operations: Vec<Annotated<EffectOp>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
        span: Span,
    },

    /// `handler console_log for Log needs {Http} { ... }`
    /// `handler counter for State Int { ... }`
    /// `handler show_store for Store a where {a: Show} { ... }`
    HandlerDef {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        name: String,
        name_span: Span,
        body: HandlerBody,
        /// Partially parsed arms from error recovery (for LSP hover, not typechecked).
        recovered_arms: Vec<Annotated<HandlerArm>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
        span: Span,
    },

    /// `trait Show a { fun show (x: a) -> String }`
    /// `trait ConvertTo a b { ... }` -- a is self, b is an extra type param
    TraitDef {
        id: NodeId,
        doc: Vec<String>,
        public: bool,
        name: String,
        name_span: Span,
        /// Type parameters: first is the self type, rest are extras.
        /// e.g. `trait ConvertTo a b` -> ["a", "b"]
        type_params: Vec<String>,
        supertraits: Vec<(String, Span)>,
        methods: Vec<Annotated<TraitMethod>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
        span: Span,
    },

    /// `impl Show for User { show user = ... }`
    /// `impl ConvertTo NOK for USD { ... }` -- NOK is a trait type arg
    /// `impl Store for Redis needs {Http, Fail} { ... }`
    ImplDef {
        id: NodeId,
        doc: Vec<String>,
        trait_name: String,
        trait_name_span: Span,
        /// Type arguments applied to the trait, e.g. ["NOK"] in `impl ConvertTo NOK for USD`
        trait_type_args: Vec<String>,
        target_type: String,
        target_type_span: Span,
        type_params: Vec<String>,
        where_clause: Vec<TraitBound>,
        needs: Vec<EffectRef>,
        methods: Vec<Annotated<ImplMethod>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
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

    /// A bare expression at the top level (test/describe sugar in test files).
    /// Converted to `Let { name: "_", .. }` by the desugar pass.
    TopExpr {
        id: NodeId,
        value: Expr,
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
        /// True if `else` was on a new line - preserve multi-line layout.
        multiline: bool,
    },

    /// `case expr { Pat -> Expr, ... }`
    Case {
        scrutinee: Box<Expr>,
        arms: Vec<Annotated<CaseArm>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
    },

    /// `{ stmt1; stmt2; expr }`
    Block {
        stmts: Vec<Annotated<Stmt>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
    },

    /// `fun x -> x + 1`
    Lambda { params: Vec<Pat>, body: Box<Expr> },

    /// `user.name`
    FieldAccess { expr: Box<Expr>, field: String },

    /// `User { name: "Dylan", age: 30 }`
    RecordCreate {
        name: String,
        fields: Vec<(String, Span, Expr)>,
    },

    /// `{ street: "Main St", city: "Portland" }` (anonymous record)
    AnonRecordCreate { fields: Vec<(String, Span, Expr)> },

    /// `{ user | age: user.age + 1 }`
    RecordUpdate {
        record: Box<Expr>,
        fields: Vec<(String, Span, Expr)>,
    },

    /// `log! "hello"`, `Cache.get! key`, `counter.put! 5`
    EffectCall {
        name: String,
        /// Optional namespace qualifier: `Cache` in `Cache.get!`
        qualifier: Option<String>,
        /// Optional handle-binding instance: `counter` in `counter.put!`
        instance: Option<String>,
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

    /// `Math.abs` - module-qualified name lookup.
    /// `module` is the user-written alias (e.g. "List"), used by codegen.
    /// `canonical_module` is filled by the resolve pass (e.g. "Std.List"), used by typechecker.
    QualifiedName {
        module: String,
        name: String,
        /// Set by the resolve pass. None = not yet resolved (e.g. auto-imports).
        canonical_module: Option<String>,
    },

    /// `do { Pat <- expr ... SuccessExpr } else { Pat -> expr ... }`
    Do {
        bindings: Vec<(Pat, Expr)>,
        success: Box<Expr>,
        else_arms: Vec<Annotated<CaseArm>>,
        /// Comments before the closing `}` of the else block
        dangling_trivia: Vec<Trivia>,
    },

    /// `receive { Pat -> body, after N -> timeout_body }`
    Receive {
        arms: Vec<Annotated<CaseArm>>,
        /// Optional (timeout_expr, timeout_body)
        after_clause: Option<(Box<Expr>, Box<Expr>)>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
    },

    /// `(expr : Type)` -- inline type annotation / ascription
    Ascription {
        expr: Box<Expr>,
        type_expr: TypeExpr,
    },

    /// `handler for Effect { op param = body ... }` -- anonymous handler expression
    HandlerExpr { body: HandlerBody },

    // --- Surface syntax (desugared before typechecking) ---
    /// `x |> f |> g` -- forward pipe chain.
    /// Stored as a flat list of annotated segments: [x, f, g].
    /// Each segment carries leading trivia (comments before `|>`) and
    /// a trailing comment (comment at end of that segment, before the next `|>`).
    /// The first segment's leading trivia comes from the head expression.
    Pipe {
        segments: Vec<Annotated<Expr>>,
        /// True if any `|>` was on a new line in the source - the user
        /// intended multi-line layout, so the formatter should preserve it.
        multiline: bool,
    },

    /// `a + b + c` or `a + b - c` -- binary operator chain at one precedence level.
    /// Stored as a flat list of annotated operands plus per-pair operators.
    /// `segments` has N elements, `ops` has N-1 elements.
    /// Desugars to left-nested `BinOp` before typechecking.
    BinOpChain {
        segments: Vec<Annotated<Expr>>,
        ops: Vec<BinOp>,
        /// True if any operator was on a new line in the source.
        multiline: bool,
    },

    /// `f <| x` -- backward pipe chain (desugars to App(f, x))
    PipeBack { segments: Vec<Annotated<Expr>> },

    /// `f >> g` -- forward compose chain (desugars to fun x -> g (f x))
    ComposeForward { segments: Vec<Annotated<Expr>> },

    /// `f << g` -- backward compose chain (desugars to fun x -> f (g x))
    ComposeBack { segments: Vec<Annotated<Expr>> },

    /// `x :: xs` -- cons (desugars to App(App(Constructor("Cons"), x), xs))
    Cons { head: Box<Expr>, tail: Box<Expr> },

    /// `[1, 2, 3]` or `[]` -- list literal (desugars to nested Cons/Nil)
    ListLit { elements: Vec<Expr> },

    /// `$"hello {name}"` -- interpolated string (desugars to show/concat chain)
    StringInterp {
        parts: Vec<StringPart>,
        kind: StringKind,
    },

    /// `[expr | qualifiers]` -- list comprehension (desugars to flat_map/if/let)
    ListComprehension {
        body: Box<Expr>,
        qualifiers: Vec<ComprehensionQualifier>,
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
            ExprKind::Block { stmts, .. } => stmts.iter().any(|s| s.node.contains_resume()),
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
            } => scrutinee.contains_resume() || arms.iter().any(|a| a.node.body.contains_resume()),
            ExprKind::Lambda { body, .. } => body.contains_resume(),
            ExprKind::App { func, arg, .. } => func.contains_resume() || arg.contains_resume(),
            ExprKind::BinOp { left, right, .. } => {
                left.contains_resume() || right.contains_resume()
            }
            ExprKind::UnaryMinus { expr, .. } => expr.contains_resume(),
            ExprKind::Tuple { elements, .. } => elements.iter().any(|e| e.contains_resume()),
            ExprKind::FieldAccess { expr, .. } => expr.contains_resume(),
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
                fields.iter().any(|(_, _, e)| e.contains_resume())
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                record.contains_resume() || fields.iter().any(|(_, _, e)| e.contains_resume())
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
                    || else_arms.iter().any(|a| a.node.body.contains_resume())
            }
            ExprKind::EffectCall { args, .. } => args.iter().any(|e| e.contains_resume()),
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                arms.iter().any(|a| a.node.body.contains_resume())
                    || after_clause
                        .as_ref()
                        .is_some_and(|(t, b)| t.contains_resume() || b.contains_resume())
            }
            ExprKind::Ascription { expr, .. } => expr.contains_resume(),
            // Handler expression arm bodies have their own resume context,
            // similar to With -- don't look through them.
            ExprKind::HandlerExpr { .. } => false,
            ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
                segments.iter().any(|s| s.node.contains_resume())
            }
            ExprKind::PipeBack { segments }
            | ExprKind::ComposeForward { segments }
            | ExprKind::ComposeBack { segments } => {
                segments.iter().any(|s| s.node.contains_resume())
            }
            ExprKind::Cons { head, tail } => head.contains_resume() || tail.contains_resume(),
            ExprKind::ListLit { elements } => elements.iter().any(|e| e.contains_resume()),
            ExprKind::StringInterp { parts, .. } => parts
                .iter()
                .any(|p| matches!(p, StringPart::Expr(e) if e.contains_resume())),
            ExprKind::ListComprehension { body, qualifiers } => {
                body.contains_resume()
                    || qualifiers.iter().any(|q| match q {
                        ComprehensionQualifier::Generator(_, e)
                        | ComprehensionQualifier::Let(_, e) => e.contains_resume(),
                        ComprehensionQualifier::Guard(e) => e.contains_resume(),
                    })
            }
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

    /// `handle logger = expr` -- bind a handler to a name
    Handle {
        name: String,
        name_span: Span,
        value: Expr,
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
            Stmt::Handle { value, .. } => value.contains_resume(),
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
    /// `rest` is true when `..` is present: `User { name, .. }`
    Record {
        id: NodeId,
        name: String,
        fields: Vec<(String, Option<Pat>)>, // (field_name, optional alias pattern)
        rest: bool,
        as_name: Option<String>,
        span: Span,
    },

    /// `{ street, city }` (anonymous record destructure)
    /// `rest` is true when `..` is present: `{ street, .. }`
    AnonRecord {
        id: NodeId,
        fields: Vec<(String, Option<Pat>)>,
        rest: bool,
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

    // --- Surface syntax (desugared before typechecking) ---
    /// `[a, b, c]` -- list pattern (desugars to nested Cons/Nil constructors)
    ListPat {
        id: NodeId,
        elements: Vec<Pat>,
        span: Span,
    },

    /// `x :: xs` -- cons pattern (desugars to Constructor("Cons", [x, xs]))
    ConsPat {
        id: NodeId,
        head: Box<Pat>,
        tail: Box<Pat>,
        span: Span,
    },

    /// `A | B | C` -- or-pattern (desugars to duplicate arms)
    Or {
        id: NodeId,
        patterns: Vec<Pat>,
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
            | Pat::StringPrefix { id, .. }
            | Pat::ListPat { id, .. }
            | Pat::ConsPat { id, .. }
            | Pat::Or { id, .. } => *id,
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
            | Pat::StringPrefix { span, .. }
            | Pat::ListPat { span, .. }
            | Pat::ConsPat { span, .. }
            | Pat::Or { span, .. } => *span,
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
    App {
        func: Box<TypeExpr>,
        arg: Box<TypeExpr>,
        span: Span,
    },

    /// `a -> b` or `a -> b needs {Eff}` or `a -> b needs {State Int, ..e}`
    Arrow {
        from: Box<TypeExpr>,
        to: Box<TypeExpr>,
        effects: Vec<EffectRef>,
        /// Row variable for open effect rows, e.g. `..e` in `needs {Assert, ..e}`
        effect_row_var: Option<(String, Span)>,
        span: Span,
    },

    /// Anonymous record type: `{ street: String, city: String }`
    Record {
        fields: Vec<(String, TypeExpr)>,
        /// True if any field separator was on a new line - preserve multi-line layout.
        multiline: bool,
        span: Span,
    },

    /// Labeled parameter in a type expression: `(label: Type)`.
    /// Documentation-only — the label does not affect type semantics.
    Labeled {
        label: String,
        inner: Box<TypeExpr>,
        span: Span,
    },
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named { span, .. }
            | TypeExpr::Var { span, .. }
            | TypeExpr::App { span, .. }
            | TypeExpr::Arrow { span, .. }
            | TypeExpr::Record { span, .. }
            | TypeExpr::Labeled { span, .. } => *span,
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
                TypeExpr::App {
                    func: f1, arg: a1, ..
                },
                TypeExpr::App {
                    func: f2, arg: a2, ..
                },
            ) => f1 == f2 && a1 == a2,
            (
                TypeExpr::Arrow {
                    from: f1,
                    to: t1,
                    effects: e1,
                    ..
                },
                TypeExpr::Arrow {
                    from: f2,
                    to: t2,
                    effects: e2,
                    ..
                },
            ) => f1 == f2 && t1 == t2 && e1 == e2,
            (TypeExpr::Record { fields: f1, .. }, TypeExpr::Record { fields: f2, .. }) => f1 == f2,
            (TypeExpr::Labeled { label: l1, inner: i1, .. }, TypeExpr::Labeled { label: l2, inner: i2, .. }) => l1 == l2 && i1 == i2,
            _ => false,
        }
    }
}

// --- Supporting types ---

/// Literal values. Int and Float carry the original source text alongside the
/// parsed numeric value so the formatter can round-trip exactly what the user wrote.
#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(String, i64),
    Float(String, f64),
    String(String, StringKind),
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
    Mod,      // % (integer remainder, emitted by elaboration for Int)
    FloatMod, // % on Float (math:fmod, emitted by elaboration)
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

/// A part of an interpolated string (`$"hello {name}"`).
#[derive(Debug, Clone, PartialEq)]
pub enum StringPart {
    /// Literal text between holes.
    Lit(String),
    /// `{expr}` -- the raw expression inside the hole (before show wrapping).
    Expr(Expr),
}

/// A qualifier in a list comprehension (`[expr | qualifiers]`).
#[derive(Debug, Clone, PartialEq)]
pub enum ComprehensionQualifier {
    /// `pat <- expr` -- generator
    Generator(Pat, Expr),
    /// `expr` -- guard (boolean filter)
    Guard(Expr),
    /// `let pat = expr` -- let binding
    Let(Pat, Expr),
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
    pub doc: Vec<String>,
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HandlerArm {
    pub op_name: String,
    /// Optional effect qualifier for disambiguation (e.g. `Logger` in `Logger.log`)
    pub qualifier: Option<String>,
    pub params: Vec<(String, Span)>,
    pub body: Box<Expr>,
    pub span: Span,
}

/// Shared handler body used by both declarations (`Decl::HandlerDef`) and
/// expressions (`ExprKind::HandlerExpr`). Contains only semantic fields;
/// formatting/recovery concerns live on the wrapper.
#[derive(Debug, Clone, PartialEq)]
pub struct HandlerBody {
    pub effects: Vec<EffectRef>,
    pub needs: Vec<EffectRef>,
    pub where_clause: Vec<TraitBound>,
    pub arms: Vec<Annotated<HandlerArm>>,
    pub return_clause: Option<Box<HandlerArm>>,
}

/// `a: Show + Eq` or `a: ConvertTo b` in a `where` clause
#[derive(Debug, Clone, PartialEq)]
pub struct TraitBound {
    /// The type variable being constrained (e.g. `a`)
    pub type_var: String,
    /// The required traits with optional type args and spans.
    /// e.g. `Show` -> ("Show", [], span), `ConvertTo b` -> ("ConvertTo", ["b"], span)
    pub traits: Vec<(String, Vec<String>, Span)>,
}

/// A named handler reference inside an inline `with` block (e.g. `console_log`).
#[derive(Debug, Clone, PartialEq)]
pub struct NamedHandlerRef {
    pub name: String,
    pub span: Span,
}

/// The handler in a `with` expression
#[derive(Debug, Clone, PartialEq)]
pub enum Handler {
    /// `expr with handler_name`
    Named(String, Span),
    /// `expr with { h1, h2, op args = body }`
    Inline {
        /// Named handler references (e.g. `h1, h2`)
        named: Vec<Annotated<NamedHandlerRef>>,
        /// Inline handler arms (e.g. `op args = body`)
        arms: Vec<Annotated<HandlerArm>>,
        /// `return value = Ok(value)` clause
        return_clause: Option<Box<HandlerArm>>,
        /// Comments before the closing `}` with no following sibling
        dangling_trivia: Vec<Trivia>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    pub doc: Vec<String>,
    pub name: String,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub span: Span,
}
