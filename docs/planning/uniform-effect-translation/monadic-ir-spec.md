# Monadic IR Specification

Companion to [uniform-effect-translation.md](../uniform-effect-translation.md).
This is the concrete IR design for the new path — paste-able Rust type
definitions for `src/codegen/monadic/ir.rs`.

Status: **draft / design**. Subject to revision during implementation.

## Required context

Read these first:

1. [uniform-effect-translation.md](../uniform-effect-translation.md) — the
   architecture. Especially stages 9, 10, 11.
2. [src/ast.rs](../../../src/ast.rs) — existing `Expr`, `Decl`, `Handler`,
   `HandlerArm`, `Pat`. The IR mirrors a subset.

---

## Core types

### `MVar`

Fresh-binder identity. Variables introduced by ANF or translation get an
`MVar`; the original source name is kept for debug.

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MVar {
    pub name: String,    // original (or synthesized) identifier
    pub id: u32,         // disambiguates shadowed/synthetic vars
}
```

### `EffectOpRef`

Pre-resolved effect operation reference. Built at translation time so the
lowerer doesn't need to recompute effect/op indices.

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EffectOpRef {
    pub effect: String,  // canonical effect name (e.g. "Log", "State")
    pub op: String,      // op name as declared (e.g. "log", "get")
    pub op_index: u32,   // 1-based op index inside op tuple (alphabetical)
}
```

### `Atom`

ANF atomic positions. Every position the ANF invariant declares atomic is
typed as `Atom` — a non-atomic subterm in those positions is a compile
error, not a runtime concern.

Constructors are **recursively atomic** (all args must be atoms). A
constructor of a non-atomic value gets ANF'd into `let a = e in Ctor(a)`
upstream.

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
    Var { name: MVar, source: NodeId },
    Lit { value: Lit, source: NodeId },

    /// Nullary or all-atomic constructor: `None`, `Some(x)`, `Cons(h, t)`.
    /// Post-elaboration, list literals and `::` are rewritten to Cons/Nil.
    Ctor {
        name: String,
        args: Vec<Atom>,
        source: NodeId,
    },

    Tuple { elements: Vec<Atom>, source: NodeId },
    AnonRecord {
        fields: Vec<(String, Atom)>,
        source: NodeId,
    },
    Record {
        name: String,
        fields: Vec<(String, Atom)>,
        source: NodeId,
    },

    /// Closure value at construction. Body is MExpr (own computation
    /// context per ANF rules — lambda is atomic at construction, body is
    /// ANF'd recursively).
    Lambda {
        params: Vec<Pat>,
        body: Box<MExpr>,
        source: NodeId,
    },

    DictRef { name: String, source: NodeId },
    QualifiedRef {
        module: String,
        name: String,
        source: NodeId,
    },
    Symbol { symbol: String, source: NodeId },
}
```

### `MExpr`

The monadic IR. Every sequencing point is `Bind` or `Let`; every leaf value
is `Pure(Atom)`; every `perform` is `Yield`. Other variants are *structural*
control flow / binders.

**NodeId carrying rule** (resolved):
- `Atom` variants each carry their own `source: NodeId`.
- Structural `MExpr` variants (`App`, `Case`, `If`, `With`, `FieldAccess`,
  `RecordUpdate`, `DictMethodAccess`, `ForeignCall`, `BinOp`, `UnaryMinus`,
  `BitString`, `Receive`, `Resume`) carry `source: NodeId`.
- `Yield` carries `source: NodeId` (the original `EffectCall` ID).
- **`Pure` and `Bind` do NOT carry `source`.** `Pure` wraps an atom that
  already has one; `Bind` is pure scaffolding from the translator.
- `Let` does not carry `source` either — it's introduced by effect
  optimization, not a source construct.

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum MExpr {
    // --- monadic constructors ---

    /// Lift a value into the monad. No NodeId — the atom carries source.
    Pure(Atom),

    /// `perform` site.
    Yield {
        op: EffectOpRef,
        args: Vec<Atom>,
        source: NodeId,
    },

    /// Monadic sequencing: run `value` (may yield), bind result to `var`,
    /// continue with `body`. Emitted uniformly by the translator. No
    /// NodeId — `Bind` is pure scaffolding.
    Bind {
        var: MVar,
        value: Box<MExpr>,
        body: Box<MExpr>,
    },

    // --- structural: pure binder & control flow ---

    /// Pure `let`. `value` is provably effect-free (recursively no `Yield`).
    /// Produced by effect optimization's Bind→Let promotion rewrite. The
    /// translator never emits this directly.
    Let {
        var: MVar,
        value: Box<MExpr>,
        body: Box<MExpr>,
    },

    Case {
        scrutinee: Atom,
        arms: Vec<MArm>,
        source: NodeId,
    },

    If {
        cond: Atom,
        then_branch: Box<MExpr>,
        else_branch: Box<MExpr>,
        source: NodeId,
    },

    /// Saturated call. Head and every arg atomic post-ANF.
    App {
        head: Atom,
        args: Vec<Atom>,
        source: NodeId,
    },

    /// `with body handler`. Handler arm bodies are themselves MExpr.
    With {
        handler: MHandler,
        body: Box<MExpr>,
        source: NodeId,
    },

    /// `resume v`. Argument is atomic by ANF.
    Resume { value: Atom, source: NodeId },

    FieldAccess {
        record: Atom,
        field: String,
        record_name: Option<String>,
        source: NodeId,
    },

    RecordUpdate {
        record: Atom,
        fields: Vec<(String, Atom)>,
        record_name: Option<String>,
        source: NodeId,
    },

    DictMethodAccess {
        dict: Atom,
        trait_name: String,
        method_index: usize,
        source: NodeId,
    },

    /// Erlang BIF / `@external` call.
    ForeignCall {
        module: String,
        func: String,
        args: Vec<Atom>,
        source: NodeId,
    },

    /// Builtin operator over atoms. Kept distinct from `ForeignCall` so the
    /// lowerer can emit native Core Erlang shapes without recovering
    /// operator identity from a string pair.
    BinOp {
        op: BinOp,
        left: Atom,
        right: Atom,
        source: NodeId,
    },
    UnaryMinus { value: Atom, source: NodeId },

    BitString {
        segments: Vec<MBitSegment>,
        source: NodeId,
    },

    Receive {
        arms: Vec<MArm>,
        after: Option<(Atom, Box<MExpr>)>,
        source: NodeId,
    },
}
```

### `MArm`, `MBitSegment`

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct MArm {
    pub pattern: Pat,             // patterns are not computations — verbatim from AST
    pub guard: Option<MExpr>,
    pub body: MExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MBitSegment {
    pub value: Atom,
    pub size: Option<Atom>,
    pub specs: Vec<ast::BitSegSpec>,
    pub span: Span,
}
```

### `MHandler` / `MHandlerArm`

Parallel structs to AST `Handler` / `HandlerArm`. Not a generic
`Handler<E>` parameterization — local, single-file, no AST diff required.

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct MHandler {
    pub effects: Vec<String>,     // effects this handler discharges
    pub arms: Vec<MHandlerArm>,
    pub return_clause: Option<MHandlerArm>,
    pub source: NodeId,           // original handler NodeId
}

#[derive(Debug, Clone, PartialEq)]
pub struct MHandlerArm {
    pub id: NodeId,               // original arm NodeId — HandlerAnalysis key
    pub op: EffectOpRef,          // pre-resolved
    pub params: Vec<Pat>,
    pub body: MExpr,
    pub finally_block: Option<MExpr>,
    pub span: Span,
}
```

The AST's `Handler::Named(NamedHandlerRef)` form is resolved to its arms at
translation time — `MHandler` doesn't need that variant. Inline-vs-named
distinction is irrelevant post-translation; we always have a flat list of
arms.

### `MDecl` / `MProgram`

Selectively-parallel: typed where bodies live; everything else passes
through unchanged.

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct MFunBinding {
    pub id: NodeId,
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Pat>,
    pub body: MExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MVal {
    pub id: NodeId,
    pub public: bool,
    pub name: String,
    pub value: MExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MDictConstructor {
    pub id: NodeId,
    pub name: String,
    pub dict_params: Vec<String>,
    pub methods: Vec<MExpr>,        // each is `MExpr::Pure(Atom::Lambda { .. })`
    pub method_effects: Vec<Vec<String>>,
    pub method_open_rows: Vec<bool>,
    pub impl_effects: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MDecl {
    FunBinding(MFunBinding),
    Val(MVal),
    DictConstructor(MDictConstructor),
    /// All decls without an expression body pass through unchanged:
    /// FunSignature, TypeDef, RecordDef, EffectDef, TraitDef, ImplDef
    /// (synthesized dicts are converted to DictConstructor by
    /// elaborate; surviving ImplDefs shouldn't exist post-elaborate),
    /// Import, ModuleDecl, TypeAlias.
    Passthrough(ast::Decl),
}

pub type MProgram = Vec<MDecl>;
```

---

## Excluded `ExprKind` variants

Variants in `ast::ExprKind` deliberately absent from `MExpr`:

| Variant | Why absent |
|---|---|
| `Pipe`, `PipeBack`, `ComposeForward`, `BinOpChain`, `Cons`, `ListLit`, `StringInterp`, `ListComprehension` | Desugared in stage 4 (`desugar.rs`); never reach codegen. |
| `Block { stmts }` | ANF flattens into a chain of `Bind` / `Let`. After ANF there are no statement lists, only sequenced binders. |
| `Do { bindings, success, else_arms }` | Desugared to nested `case` / monadic chain before translation. |
| `EffectCall { name, qualifier, args }` | Translated to `MExpr::Yield`. The whole point of monadic translation. |
| `Constructor { name }` (nullary) | Becomes `Atom::Ctor { args: vec![], … }`. |
| `Var`, `Lit`, `QualifiedName`, `DictRef`, `SymbolIntrinsic`, atomic `Tuple` / `RecordCreate` / `AnonRecordCreate`, bare `Lambda` | Reified as `Atom` variants under `MExpr::Pure(atom)`. |
| `Ascription { expr, type_expr }` | Type ascription is erased post-typecheck. Translator strips it. |
| `HandlerExpr { body }` | Either folded into enclosing `With { handler: MHandler }`, or lifted to a named handler decl. No standalone IR variant needed. |
| Constructor used as a value (partial application) | Eta-expanded into `Atom::Lambda` carrying `Pure(Ctor(...))` body. |

---

## Stage entry-function signatures

```rust
// src/codegen/handler_analysis.rs
pub fn analyze(p: &ast::Program) -> HandlerAnalysis;

// src/codegen/anf.rs
// Output is still ast::Program — ANF doesn't change the type, just guarantees
// the atom/complex invariant at sub-positions. Monadic translation is what
// changes the type.
pub fn normalize(p: ast::Program) -> ast::Program;

// src/codegen/monadic/translate.rs
pub fn translate(
    p: &ast::Program,
    r: &codegen::resolve::ResolutionMap,
) -> MProgram;

// src/codegen/monadic/effect_opt/mod.rs
pub fn run(
    m: MProgram,
    h: &HandlerAnalysis,
) -> MProgram;

// src/codegen/lower_monadic/mod.rs
impl<'ctx> Lowerer<'ctx> {
    pub fn new(
        resolution: &'ctx ResolutionMap,
        ctors: &'ctx ConstructorAtoms,
        module_ctx: &'ctx ModuleCodegenContext,
        handler_info: &'ctx HandlerAnalysis,
    ) -> Self;

    pub fn lower_module(
        &mut self,
        module_name: &str,
        program: &MProgram,
    ) -> codegen::cerl::CModule;
}
```

---

## File-size targets (per cross-cutting principle)

- `ir.rs` — ~350 LOC (type definitions only)
- `translate.rs` — ~500–700 LOC; split if it grows (`translate/expr.rs`,
  `translate/handler.rs`, `translate/decl.rs`)
- `effect_opt/mod.rs` — orchestrator only, ~100 LOC
- `effect_opt/bind_collapse.rs`, `effect_opt/bind_to_let.rs`,
  `effect_opt/direct_call.rs` — one rewrite each
- `print.rs` — debug pretty-printer
