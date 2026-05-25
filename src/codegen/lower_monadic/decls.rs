//! Lower `MDecl` values to Core Erlang `CFunDef`s.
//!
//! Sub-step 7a scope:
//!   - `FunBinding`, `Val`, `DictConstructor` → CFunDef with uniform
//!     `(user_args..., _Evidence, _ReturnK)` signature. Bodies are stubbed.
//!   - `Passthrough` decls emit nothing (most of these — TypeDef, EffectDef,
//!     ModuleDecl, etc. — are pure metadata with no runtime presence).
//!     `FunSignature` with `@external` annotations and other code-emitting
//!     passthroughs are handled by a later sub-step.
//!
//! The "uniform shape" is load-bearing: every CFunDef takes evidence + a
//! return continuation, regardless of whether the source function performs
//! any effects. See the planning doc's "slow uniform path" section.

use crate::ast::Pat;
use crate::codegen::cerl::{CExpr, CFunDef};
use crate::codegen::monadic::ir::{MDictConstructor, MFunBinding, MVal};

use super::Lowerer;
use super::pats::lower_param_names;

/// Variable name for the evidence-vector parameter on every emitted CFunDef.
pub(super) const EVIDENCE_VAR: &str = "_Evidence";
/// Variable name for the return-continuation parameter on every emitted CFunDef.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";

impl<'ctx> Lowerer<'ctx> {
    /// Lower an `MDecl::FunBinding` to a `CFunDef`.
    ///
    /// Signature: `(param_0, ..., param_{n-1}, _Evidence, _ReturnK)`.
    pub(super) fn lower_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let mut params = lower_param_names(&fb.params);
        params.push(EVIDENCE_VAR.to_string());
        params.push(RETURN_K_VAR.to_string());
        let arity = params.len();
        let body = self.lower_body_stub(&fb.body);
        CFunDef {
            name: fb.name.clone(),
            arity,
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    /// Lower an `MDecl::Val` to a `CFunDef`.
    ///
    /// Vals are pure constants — Saga's language design routes effectful
    /// computations through ordinary functions. The codegen convention
    /// matches the old lowerer: an arity-0 Erlang function whose body is
    /// the constant value. No `_Evidence` / `_ReturnK` threading.
    ///
    /// The uniform "every fn takes evidence + return-K" rule applies to
    /// **functions**; a val isn't a function in the calling-convention
    /// sense, just a top-level constant exposed as `mod:name/0`.
    pub(super) fn lower_val(&mut self, v: &MVal) -> CFunDef {
        let body = self.lower_val_body_stub(&v.value);
        CFunDef {
            name: v.name.clone(),
            arity: 0,
            body: CExpr::Fun(vec![], Box::new(body)),
        }
    }

    /// Lower an `MDecl::DictConstructor` to a `CFunDef`.
    ///
    /// Signature: `(dict_params..., _Evidence, _ReturnK)`. The body is
    /// stubbed in 7a; sub-step 7c will replace it with the actual tuple
    /// synthesis (`{method_0, method_1, ...}`) matching the old lowerer's
    /// shape.
    pub(super) fn lower_dict_constructor(&mut self, dc: &MDictConstructor) -> CFunDef {
        let mut params: Vec<String> = dc
            .dict_params
            .iter()
            .map(|p| super::util::core_var(p))
            .collect();
        params.push(EVIDENCE_VAR.to_string());
        params.push(RETURN_K_VAR.to_string());
        let arity = params.len();
        // STUB body: see exprs.rs. Real tuple synthesis lands in 7c.
        let body = if let Some(first) = dc.methods.first() {
            self.lower_body_stub(first)
        } else {
            self.lower_stub_unit()
        };
        CFunDef {
            name: dc.name.clone(),
            arity,
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_stub_unit(&mut self) -> CExpr {
        use crate::codegen::cerl::CLit;
        CExpr::Apply(
            Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
            vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
        )
    }
}

/// Compute the exported arity of an MFunBinding under the uniform convention.
/// Public to callers (mod.rs) that build the export list before the body
/// has been lowered.
pub(super) fn fun_binding_arity(params: &[Pat]) -> usize {
    lower_param_names(params).len() + 2 // + _Evidence + _ReturnK
}

pub(super) fn val_arity() -> usize {
    0 // val is a top-level constant — no params, no evidence threading
}

pub(super) fn dict_constructor_arity(dc: &MDictConstructor) -> usize {
    dc.dict_params.len() + 2
}
