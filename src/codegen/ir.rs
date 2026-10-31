//! The typed back-end tree (`docs/planning/typed-backend-ir.md`).
//!
//! Each node carries what the lowerer needs to emit it: references are
//! absolute, record slots are indices, a function reference has its
//! convention. The builder (`lower/build.rs`) sets every field by a positive
//! rule; the lowerer reads the fields and looks nothing up.
//!
//! During the migration the builder is shallow: it builds one node and
//! leaves the children as `Ast`, which the lowerer hands back to the builder
//! when it reaches them. The `Ast` variants and the lifetime go when the
//! builder is made deep. No node is stored anywhere: one is built, lowered
//! and dropped within a single lowering call.

use crate::ast;
use crate::codegen::call_effects::CallEffectInfo;
use crate::codegen::lower::errors::ErrorKind;
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi};
use crate::intrinsics::IntrinsicId;
use crate::token::Span;

/// A function the compiler calls or references directly: a top-level,
/// imported, external or block-local function, or a dictionary constructor.
#[derive(Debug, Clone)]
pub(crate) struct FnRef {
    /// The Erlang module that defines it; `None` for the module being
    /// emitted (a local `'name'/arity`).
    pub module: Option<String>,
    pub name: String,
    pub abi: CallableAbi,
}

/// How a named function is represented when it is used as a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FnRepr {
    /// A bare fun of the function's own arity.
    Bare,
    /// `{'$saga_cps', Fun}`: the occurrence's type is effectful.
    Tagged,
    /// A bare fun over an effectful function whose row is open and empty at
    /// this occurrence: it supplies empty evidence itself.
    BareEmptyRow,
}

/// A data constructor, by its runtime shape.
#[derive(Debug, Clone)]
pub(crate) enum CtorRef {
    Nil,
    Cons,
    Bool(bool),
    /// A nullary constructor that is a bare atom at runtime.
    Atom(&'static str),
    /// A tuple tagged with this atom.
    Tagged(String),
}

/// A value: evaluating one runs no user code and cannot perform.
#[derive(Debug)]
pub(crate) enum Val<'a> {
    /// Not built yet (see the module comment). Only `Lowerer::operand`
    /// makes one.
    Ast(&'a ast::Expr),
    Lit(&'a ast::Lit),
    /// A variable, by its Core Erlang name.
    Local(String),
    Fn {
        target: FnRef,
        repr: FnRepr,
    },
    /// A block-local function used as a value.
    LocalFn {
        target: FnRef,
        repr: FnRepr,
    },
    /// A top-level binding that takes no parameters.
    Const(FnRef),
    /// An intrinsic used as a value.
    Intrinsic {
        name: String,
        arity: usize,
    },
    Ctor {
        ctor: CtorRef,
        args: Vec<Val<'a>>,
    },
    /// A constructor used as a function of `arity` fields.
    CtorFn {
        ctor: CtorRef,
        arity: usize,
    },
    Tuple(Vec<Val<'a>>),
    /// A record literal, named or anonymous. `fields` are in the order
    /// written (the order they are evaluated in), each with its slot.
    Record {
        tag: String,
        arity: usize,
        fields: Vec<(usize, Val<'a>)>,
    },
    /// Slot `slot` (0-based, after the tag) of a record.
    Field {
        base: Box<Val<'a>>,
        slot: usize,
    },
    /// A dictionary that takes no dictionaries.
    Dict(FnRef),
    /// A dictionary constructor applied to its dictionaries.
    DictApp {
        ctor: FnRef,
        args: Vec<Val<'a>>,
    },
    /// A dictionary passed to the enclosing function.
    DictParam(String),
    /// Element `slot` (1-based) of a dictionary tuple: a method.
    DictMethod {
        dict: Box<Val<'a>>,
        slot: usize,
        /// The method takes no parameters: its slot holds a thunk, forced here.
        nullary: bool,
        /// The slot holds a tagged closure but this occurrence is pure:
        /// a bare fun of this many arguments is wanted.
        pure_view: Option<usize>,
    },
    /// Element `slot` (1-based) of a dictionary tuple: a superclass dictionary.
    DictSuper {
        dict: Box<Val<'a>>,
        slot: usize,
    },
    /// A named handler used as a value. Its lowering is not migrated.
    HandlerRef(String),
}

/// A computation: only ever the value of a `let` or a tail. So far the
/// forms an application is built into.
#[derive(Debug)]
pub(crate) enum Expr<'a> {
    Val(Val<'a>),
    Call(Call<'a>),
    /// A known function applied to fewer arguments than it takes: a closure
    /// over the arguments given.
    Partial {
        target: FnRef,
        args: Vec<Val<'a>>,
        repr: FnRepr,
        span: Span,
    },
    /// An applied operation. Still the operation node and the argument
    /// expressions: operations are not migrated.
    Perform {
        op: &'a ast::Expr,
        args: Vec<&'a ast::Expr>,
    },
    Intrinsic {
        id: IntrinsicId,
        args: Vec<Val<'a>>,
    },
    /// `panic msg` or `todo ()`: raise the error `kind`, with `message` or
    /// the kind's own text.
    Raise {
        kind: ErrorKind,
        message: Option<Val<'a>>,
        span: Span,
    },
}

/// The convention of one call: direct, or with the evidence the callee's
/// row asks for and a return continuation.
#[derive(Debug, Clone)]
pub(crate) enum Conv {
    Direct,
    Cps(EvidenceAbi),
}

#[derive(Debug)]
pub(crate) struct Call<'a> {
    pub callee: Callee<'a>,
    pub args: Vec<Val<'a>>,
    conv: Conv,
    /// Where the call is written, when the emitted call is annotated with it.
    pub span: Option<Span>,
    /// For the fast paths that still match on the AST: the name the
    /// lowerer's tables know the callee by, and the head expression.
    pub site: Option<(String, &'a ast::Expr)>,
}

impl<'a> Call<'a> {
    /// The only way to make a call, so the convention is always the one the
    /// callee was classified with. (It is read from the plan's entry for
    /// now; it will be computed from the callee here.)
    pub(crate) fn new(callee: Callee<'a>, args: Vec<Val<'a>>, classified: &CallEffectInfo) -> Self {
        let conv = match classified.cps_call_abi() {
            Some(abi) => Conv::Cps(abi.evidence.clone().expect("a CPS call has evidence")),
            None => Conv::Direct,
        };
        Call {
            callee,
            args,
            conv,
            span: None,
            site: None,
        }
    }

    pub(crate) fn conv(&self) -> &Conv {
        &self.conv
    }
}

#[derive(Debug)]
pub(crate) enum Callee<'a> {
    /// A known function, saturated.
    Fn(FnRef),
    /// Method `slot` (1-based) of a dictionary. `known_impl` is the method's
    /// own function when the dictionary is statically known and the method
    /// is hoisted. A direct call always has one: without it the method is
    /// called as the value `Val::DictMethod`.
    DictMethod {
        dict: Val<'a>,
        slot: usize,
        known_impl: Option<FnRef>,
    },
    /// A function value.
    Value(Val<'a>),
    /// The function another computation returns: the second half of a named
    /// function applied to more arguments than it takes.
    Result(Box<Expr<'a>>),
}
