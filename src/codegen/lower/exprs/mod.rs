//! Expression lowering: `impl Lowerer` methods that turn typed AST expressions
//! into Core Erlang. Effect-system lowering lives in the sibling `effects` module.
//!
//! Split across submodules by concern:
//! - `return_k`  — continuation / installed-return-k machinery and tail lowering
//! - `cases`     — `case` expression and pattern-arm lowering
//! - `values`    — constructors, tuples, binops, field/record access, destructuring
//! - `blocks`    — block and `*_with_k` CPS lowering
//! - `handlers`  — `do`-notation and handler-expression lowering
//! - `dispatch`  — bitstrings and the top-level `lower_expr` dispatch
//!
//! `CpsSlot` and `is_guard_safe` are shared here and reach the submodules via
//! `use super::*`.

use crate::ast::{Expr, ExprKind};
use crate::codegen::cerl::CExpr;
use crate::typechecker::Type;

mod blocks;
mod cases;
mod dispatch;
mod handlers;
mod return_k;
mod values;

/// One "hole" in a composite expression being assembled by
/// [`Lowerer::lower_with_cps_slots`]. The slot kind controls whether the
/// value comes from a pre-lowered CExpr or from CPS-chained lowering of a
/// source expression that may be effectful.
pub(crate) enum CpsSlot<'e> {
    /// Already-lowered value. Bound to a plain `let`. Use for values
    /// computed by the caller (e.g. `element(idx, rec_var)`).
    Pure(CExpr),
    /// Source expression to lower. CPS-chained if effectful; otherwise
    /// lowered as a value with the optional expected type.
    Expr {
        expr: &'e Expr,
        expected: Option<Type>,
    },
}

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
