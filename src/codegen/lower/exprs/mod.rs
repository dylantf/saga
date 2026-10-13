//! Expression lowering: `impl Lowerer` methods that turn typed AST expressions
//! into Core Erlang. Effect-system lowering lives in the sibling `effects` module.
//!
//! Split across submodules by concern:
//! - `return_k`  — continuation / installed-return-k machinery and tail lowering
//! - `cases`     — `case` expression and pattern-arm lowering
//! - `values`    — constructors, tuples, binops, field/record access, destructuring
//! - `blocks`    — block lowering, with and without a continuation
//! - `handlers`  — `do`-notation and handler-expression lowering
//! - `dispatch`  — bitstrings and the top-level `lower_expr` dispatch
//!
//! `is_guard_safe` (defined in `codegen::effect_position`) reaches the submodules via `use super::*`.

pub(crate) use crate::codegen::effect_position::is_guard_safe;

mod blocks;
mod cases;
mod dispatch;
mod handlers;
mod return_k;
mod values;
