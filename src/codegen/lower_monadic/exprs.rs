//! Monadic-IR → Core Erlang expression lowering.
//!
//! Sub-step 7a: STUB. The full MExpr lowering arrives in 7b–7g.

use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::monadic::ir::MExpr;

use super::Lowerer;

// Name of the function-entry return-continuation variable. Every emitted
// CFunDef binds this as its trailing parameter (after `_Evidence`); the body
// applies it to the function's final value. Kept in sync with `decls.rs`.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";

impl<'ctx> Lowerer<'ctx> {
    /// Lower an MExpr in function-body (tail) position.
    ///
    /// STUB (7a): every body lowers to `apply _ReturnK('unit')`.
    /// Sub-step 7c replaces this with real MExpr lowering.
    pub(super) fn lower_body_stub(&mut self, _body: &MExpr) -> CExpr {
        CExpr::Apply(
            Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
            vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
        )
    }

    /// Lower the body of an `MDecl::Val` in 7a.
    ///
    /// Vals are arity-0 — there is no `_ReturnK` in scope — so the stub
    /// returns the constant value directly. STUB (7a): every val body is
    /// `'unit'`. Sub-step 7c replaces this with real MExpr-to-value
    /// lowering (literal atoms / tuples / etc. emitted in place).
    pub(super) fn lower_val_body_stub(&mut self, _value: &MExpr) -> CExpr {
        CExpr::Lit(CLit::Atom("unit".to_string()))
    }
}
