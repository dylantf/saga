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
use crate::codegen::runtime_shape::CallableAbi;

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
