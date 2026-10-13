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
//! `is_guard_safe` is shared here and reaches the submodules via `use super::*`.

use crate::ast::{Expr, ExprKind};

mod blocks;
mod cases;
mod dispatch;
mod handlers;
mod return_k;
mod values;

/// Returns true if `expr` is a valid Core Erlang guard expression:
/// comparisons, arithmetic, boolean ops, unary minus, and literals/variables.
/// Any function application (user-defined or unknown BIF) returns false.
pub(crate) fn is_guard_safe(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit { .. } | ExprKind::Var { .. } => true,
        ExprKind::BinOp { left, right, .. } => is_guard_safe(left) && is_guard_safe(right),
        ExprKind::UnaryMinus { expr, .. } => is_guard_safe(expr),
        // No App, Constructor, Block, If, Case, etc. -- too complex for a guard
        _ => false,
    }
}
