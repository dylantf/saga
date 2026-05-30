//! Monadic IR type definitions.
//!
//! Transcribed from `docs/planning/uniform-effect-translation/monadic-ir-spec.md`.
//! No logic lives here — only data definitions. The translator (stage 10),
//! effect optimization (stage 11), and lowerer (stage 12) populate and consume
//! these types in later steps.
//!
//! Frontend types are reused verbatim where the spec calls for them
//! (`ast::Pat`, `ast::Lit`, `ast::BinOp`, `ast::BitSegSpec`, `token::Span`,
//! `typechecker::{ResolvedEffectOp, Type}`); we deliberately do not wrap them.

#![allow(dead_code)] // Step 3: type defs only; consumers land in later steps.

use std::collections::{HashMap, HashSet};

use crate::ast::{self, BinOp, BitSegSpec, Lit, NodeId, Pat};
use crate::token::Span;
use crate::typechecker::{self, ResolvedEffectOp, ResolvedValue, Type};

// -------------------------------------------------------------------------
// Core types
// -------------------------------------------------------------------------

/// Fresh-binder identity. Original (or synthesized) name is kept for debug;
/// `id` disambiguates shadowed/synthetic vars.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MVar {
    pub name: String,
    pub id: u32,
}

/// Pre-resolved effect operation reference. Built at translation time so the
/// lowerer does not need to recompute effect / op indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EffectOpRef {
    pub effect: String,
    pub op: String,
    /// 1-based op index inside the canonical (alphabetical) op tuple.
    pub op_index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindMode {
    /// Source/block sequencing: the bound computation resumes into `body`.
    Sequence,
    /// ANF-introduced value-position evaluation: the bound computation first
    /// produces a local value; only successful completion continues into
    /// `body`, while abort tuples bubble to the enclosing delimiter.
    ValuePosition,
}

// -------------------------------------------------------------------------
// Atoms (ANF atomic positions)
// -------------------------------------------------------------------------

/// ANF atomic positions. Constructors are recursively atomic — a constructor
/// of a non-atomic value must have been ANF'd into `let a = e in Ctor(a)`
/// upstream.
#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
    Var {
        name: MVar,
        source: NodeId,
    },
    Lit {
        value: Lit,
        source: NodeId,
    },

    /// Nullary or all-atomic constructor: `None`, `Some(x)`, `Cons(h, t)`.
    /// Post-elaboration, list literals and `::` are rewritten to Cons/Nil.
    Ctor {
        name: String,
        args: Vec<Atom>,
        source: NodeId,
    },

    Tuple {
        elements: Vec<Atom>,
        source: NodeId,
    },
    AnonRecord {
        fields: Vec<(String, Atom)>,
        source: NodeId,
    },
    Record {
        name: String,
        fields: Vec<(String, Atom)>,
        source: NodeId,
    },

    /// Closure value at construction. The body is its own ANF computation
    /// context — the lambda value is atomic, the body is not.
    Lambda {
        params: Vec<Pat>,
        body: Box<MExpr>,
        source: NodeId,
    },

    DictRef {
        name: String,
        source: NodeId,
    },
    QualifiedRef {
        module: String,
        name: String,
        source: NodeId,
    },
    Symbol {
        symbol: String,
        source: NodeId,
    },
    /// Backend-only Erlang atom value. This is not produced from Saga source:
    /// `Symbol` remains a type/generic-level source construct that lowers to a
    /// binary. Optimizer-native rewrites use this when a BEAM BIF requires an
    /// actual Erlang atom argument.
    BackendAtom {
        atom: String,
        source: NodeId,
    },
    /// Backend-only `fun() -> ...` thunk used by native APIs that call Saga
    /// callbacks from Erlang. Currently produced only for `Process.spawn`
    /// direct-call specialization.
    BackendSpawnThunk {
        callback: Box<Atom>,
        source: NodeId,
    },
}

// -------------------------------------------------------------------------
// MExpr
// -------------------------------------------------------------------------

/// The monadic IR. Every sequencing point is `Bind` or `Let`; every leaf
/// value is `Pure(Atom)`; every `perform` is `Yield`. Other variants are
/// structural control flow / binders.
///
/// **NodeId carrying rule** (resolved in the spec):
/// - `Atom` variants each carry their own `source: NodeId`.
/// - Structural `MExpr` variants carry `source: NodeId`.
/// - `Yield` carries `source: NodeId` (the original `EffectCall` ID).
/// - `Pure` and `Bind` do **not** carry `source` — `Pure` wraps an atom that
///   already has one; `Bind` is pure scaffolding from the translator.
/// - `Let` does not carry `source` — it is introduced by effect optimization,
///   not by source code.
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
    /// continue with `body`. Emitted uniformly by the translator.
    Bind {
        var: MVar,
        value: Box<MExpr>,
        body: Box<MExpr>,
        mode: BindMode,
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

    /// Run `body`, then run `cleanup`, preserving `body`'s result. Produced by
    /// effect optimization when it can direct-call a tail-resumptive arm with a
    /// `finally` block. The translator never emits this directly.
    Ensure {
        body: Box<MExpr>,
        cleanup: Box<MExpr>,
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

    /// `with body handler`. Handler arm bodies are themselves `MExpr`.
    With {
        handler: MHandler,
        body: Box<MExpr>,
        source: NodeId,
    },

    /// `resume v`. Argument is atomic by ANF.
    Resume {
        value: Atom,
        source: NodeId,
    },

    FieldAccess {
        record: Atom,
        field: String,
        record_name: Option<String>,
        /// Canonical sorted field order for anonymous records (from
        /// elaboration); lets lowering read field positions structurally
        /// instead of decoding the runtime tag. `None` for named records.
        anon_fields: Option<Vec<String>>,
        source: NodeId,
    },

    RecordUpdate {
        record: Atom,
        fields: Vec<(String, Atom)>,
        record_name: Option<String>,
        /// Canonical sorted field order for anonymous records. `None` for
        /// named records.
        anon_fields: Option<Vec<String>>,
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
    /// lowerer can emit native Core Erlang shapes without recovering operator
    /// identity from a string pair.
    BinOp {
        op: BinOp,
        left: Atom,
        right: Atom,
        source: NodeId,
    },
    UnaryMinus {
        value: Atom,
        source: NodeId,
    },

    BitString {
        segments: Vec<MBitSegment>,
        source: NodeId,
    },

    Receive {
        arms: Vec<MArm>,
        after: Option<(Atom, Box<MExpr>)>,
        source: NodeId,
    },

    /// `let f x y = …` inside a block. The bound name resolves to a local
    /// recursive function (via backend `ResolutionMap` as `BeamFunction
    /// { erlang_mod: None }`), so call sites emit `apply f/arity(args, _Ev,
    /// _ReturnK)` rather than chasing a closure value. The lowerer emits a
    /// `CExpr::LetRec` so that arity-N name actually exists at the call
    /// sites that follow.
    LetFun {
        name: String,
        params: Vec<crate::ast::Pat>,
        body: Box<MExpr>,
        rest: Box<MExpr>,
        source: NodeId,
    },

    /// Handler expression used as a runtime value (returned from a function,
    /// stored in a variable, etc.). The lowerer builds the op-tuple CExpr
    /// using `build_arm_closure` / `build_return_clause_closure` so that
    /// `resume`, evidence threading, and arm_k are handled correctly.
    HandlerValue {
        effects: Vec<String>,
        arms: Vec<MHandlerArm>,
        return_clause: Option<Box<MHandlerArm>>,
        source: NodeId,
    },
}

impl MExpr {
    pub fn contains_resume(&self) -> bool {
        match self {
            MExpr::Resume { .. } => true,
            MExpr::Pure(atom) => atom.contains_resume(),
            MExpr::Yield { args, .. } => args.iter().any(Atom::contains_resume),
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                value.contains_resume() || body.contains_resume()
            }
            MExpr::Ensure { body, cleanup } => body.contains_resume() || cleanup.contains_resume(),
            MExpr::Case {
                scrutinee, arms, ..
            } => scrutinee.contains_resume() || arms.iter().any(|a| a.body.contains_resume()),
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                cond.contains_resume()
                    || then_branch.contains_resume()
                    || else_branch.contains_resume()
            }
            MExpr::App { head, args, .. } => {
                head.contains_resume() || args.iter().any(Atom::contains_resume)
            }
            MExpr::ForeignCall { args, .. } => args.iter().any(Atom::contains_resume),
            MExpr::BinOp { left, right, .. } => left.contains_resume() || right.contains_resume(),
            MExpr::UnaryMinus { value, .. } => value.contains_resume(),
            MExpr::FieldAccess { record, .. } => record.contains_resume(),
            MExpr::RecordUpdate { record, fields, .. } => {
                record.contains_resume() || fields.iter().any(|(_, atom)| atom.contains_resume())
            }
            MExpr::DictMethodAccess { dict, .. } => dict.contains_resume(),
            MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
                seg.value.contains_resume() || seg.size.as_ref().is_some_and(Atom::contains_resume)
            }),
            MExpr::With { body, .. } => body.contains_resume(),
            MExpr::Receive { arms, after, .. } => {
                arms.iter().any(|a| a.body.contains_resume())
                    || after.as_ref().is_some_and(|(timeout, b)| {
                        timeout.contains_resume() || b.contains_resume()
                    })
            }
            MExpr::LetFun { body, rest, .. } => body.contains_resume() || rest.contains_resume(),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().any(|a| a.body.contains_resume())
                    || return_clause
                        .as_ref()
                        .is_some_and(|a| a.body.contains_resume())
            }
        }
    }
}

impl Atom {
    pub fn contains_resume(&self) -> bool {
        match self {
            Atom::Lambda { body, .. } => body.contains_resume(),
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                args.iter().any(Atom::contains_resume)
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                fields.iter().any(|(_, atom)| atom.contains_resume())
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => false,
            Atom::BackendSpawnThunk { callback, .. } => callback.contains_resume(),
        }
    }
}

// -------------------------------------------------------------------------
// Arm / bit segment
// -------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct MArm {
    /// Patterns are not computations — taken verbatim from the AST.
    pub pattern: Pat,
    pub guard: Option<MExpr>,
    pub body: MExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MBitSegment {
    pub value: Atom,
    pub size: Option<Atom>,
    pub specs: Vec<BitSegSpec>,
    pub span: Span,
}

// -------------------------------------------------------------------------
// Handlers
// -------------------------------------------------------------------------

/// Two variants — **static** and **dynamic** — preserving the distinction
/// that effect optimization's direct-call rewrite depends on.
#[derive(Debug, Clone, PartialEq)]
pub enum MHandler {
    /// Arms known at compile time. Direct-call rewrite eligible if the
    /// matching arm is `TailResumptive`.
    ///
    /// Built from:
    ///   - inline `handler for E { ... }` expressions
    ///   - static name references (`with console_log`)
    ///   - static aliases (`let h = console_log; with h`) resolved via
    ///     `ResolutionMap` at translation time
    Static {
        effects: Vec<String>,
        arms: Vec<MHandlerArm>,
        return_clause: Option<MHandlerArm>,
        source: NodeId,
    },

    /// Compiler-builtin native handler whose op tuple is emitted directly by
    /// the lowerer. This preserves handler identity for empty stdlib handler
    /// declarations such as `Std.Ref.ets_ref`, where the effect alone is not
    /// enough to choose the runtime backend.
    Native {
        effects: Vec<String>,
        handler: String,
        source: NodeId,
    },

    /// Inline handler block that composes several statically-known handlers,
    /// usually native stdlib handlers (`with {ets_ref, beam_actor}`).
    Composite {
        handlers: Vec<MHandler>,
        source: NodeId,
    },

    /// Arms are a runtime closure-tuple value. Direct-call rewrite must NOT
    /// fire here — the optimizer skips this variant entirely.
    ///
    /// Built from:
    ///   - conditional bindings (`let h = if dev then a else b`)
    ///   - factory results (`let h = make_handler()`)
    ///   - any `with <expr>` where `<expr>` is not a literal handler / static
    ///     name reference / resolvable alias
    ///
    /// Invariant: today's compiler produces dynamic handler bindings per
    /// single effect, so `effects.len() == 1` in practice. The field is a
    /// `Vec<String>` to mirror `Static.effects`; a translator emitting more
    /// than one is a bug unless the invariant is explicitly relaxed first.
    Dynamic {
        effects: Vec<String>,
        op_tuple: Atom,
        return_lambda: Option<Atom>,
        source: NodeId,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct MHandlerArm {
    /// Original arm `NodeId` — the key for `HandlerAnalysis` lookups.
    pub id: NodeId,
    pub op: EffectOpRef,
    pub params: Vec<Pat>,
    pub body: Box<MExpr>,
    pub finally_block: Option<Box<MExpr>>,
    pub span: Span,
}

// -------------------------------------------------------------------------
// Decls / program
// -------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct MFunBinding {
    pub id: NodeId,
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Pat>,
    pub guard: Option<MExpr>,
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
    /// Each method is expected to be `MExpr::Pure(Atom::Lambda { .. })`.
    pub methods: Vec<MExpr>,
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
    /// Decls without an expression body pass through unchanged:
    /// `FunSignature`, `TypeDef`, `RecordDef`, `EffectDef`, `TraitDef`,
    /// `ImplDef` (synthesized dicts are converted to `DictConstructor` by
    /// elaborate; surviving `ImplDef`s shouldn't exist post-elaborate),
    /// `Import`, `ModuleDecl`, `TypeAlias`.
    Passthrough(ast::Decl),
}

pub type MProgram = Vec<MDecl>;

/// Pre-translated handler arms for handler-as-value lowering.
/// Produced by the translator for each handler definition; consumed by
/// the lowerer to build runtime op-tuples when a handler name appears
/// as a value (e.g. `let h = if cond then handler_a else handler_b`).
#[derive(Debug, Clone)]
pub struct HandlerValueInfo {
    pub effects: Vec<String>,
    pub arms: Vec<MHandlerArm>,
    pub return_clause: Option<MHandlerArm>,
}

pub type HandlerValueMap = HashMap<String, HandlerValueInfo>;

// -------------------------------------------------------------------------
// EffectInfo (narrowed read-only view)
// -------------------------------------------------------------------------

/// Borrow bundle into `CheckResult` + per-module `ResolutionResult`. Built
/// once at the entry point and threaded through translation and effect
/// optimization. Reuses frontend types verbatim — no wrappers.
pub struct EffectInfo<'a> {
    /// `EffectCall` NodeId → resolved effect/op name (the typechecker did
    /// this; backend `ResolutionMap` leaves it dynamic for the old path).
    pub effect_calls: &'a HashMap<NodeId, typechecker::ResolvedEffectOp>,

    /// Handler-arm NodeId → which effect/op the arm handles.
    pub handler_arms: &'a HashMap<NodeId, ResolvedEffectOp>,

    /// Constructor expression/pattern NodeId → canonical constructor name.
    /// Used when imported handler bodies are inlined into another module:
    /// their bare constructor spelling must still lower to the defining
    /// module's runtime tag.
    pub constructors: &'a HashMap<NodeId, String>,

    /// Function name → set of effect names the function performs. Used by
    /// Bind→Let promotion to look up callee effect rows.
    pub fun_effects: &'a HashMap<String, HashSet<String>>,

    /// Let-binding name → effects the bound value carries (partial-app
    /// effectful values held in let-bindings).
    pub let_effect_bindings: &'a HashMap<String, Vec<String>>,

    /// Per-NodeId resolved type. Used to read effect rows on expressions
    /// (row-polymorphic call effects after zonking).
    pub type_at_node: &'a HashMap<NodeId, Type>,

    /// Effect name → list of op names in canonical (alphabetical) order.
    /// Required for translation to compute `EffectOpRef.op_index` for
    /// **cross-module** effects — in-program effects can be derived
    /// locally by scanning `Decl::EffectDef`, but imported effects need
    /// this map. Built at the entry-point boundary from `CheckResult`
    /// (`build_effect_info` in `src/codegen/mod.rs`). Both bare and
    /// `Module.Name` keys are inserted so lookups by either spelling
    /// succeed.
    pub effect_ops: &'a HashMap<String, Vec<String>>,

    /// Handler name → list of effect names the handler handles. Built
    /// from `CheckResult.handlers` so the translator can populate
    /// `MHandler::Dynamic.effects` for let-bound / factory-produced
    /// handler values whose arms aren't statically visible.
    pub handler_effects: &'a HashMap<String, Vec<String>>,

    /// Handler reference NodeId → resolved binding identity. Used to turn
    /// qualified imported handler spellings such as `Http.discard_events`
    /// into their canonical handler keys before looking up effects or
    /// pre-translated handler bodies.
    pub handler_refs: &'a HashMap<NodeId, ResolvedValue>,

    /// Let-binding pattern NodeId → effect names for handler-valued
    /// let bindings. Built from `CheckResult.let_binding_handlers`.
    /// Used by the translator when `with <local_var>` references a
    /// dynamically-bound handler to recover the effect tag.
    pub let_handler_effects: &'a HashMap<NodeId, Vec<String>>,
}
