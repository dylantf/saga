//! New lowerer (uniform-effect-translation, stage 12).
//!
//! Consumes `MProgram` (post-ANF, monadic-translated, optionally-optimized)
//! and produces a Core Erlang `CModule`. Designed to be invoked alongside the
//! old lowerer via the toggle in `src/codegen/mod.rs` (wired in step 8, not
//! this sub-step).
//!
//! ## Sub-step 7a scope
//!
//! Function/decl scaffolding only. The MExpr body lowering is **stubbed**
//! (see [`exprs::lower_body_stub`]) — every emitted CFunDef body is
//! `apply _ReturnK('unit')`. Sub-steps 7b–7g fill in the real translation
//! incrementally.
//!
//! ## Calling convention (uniform)
//!
//! Every emitted CFunDef takes `(user_args..., _Evidence, _ReturnK)` —
//! evidence vector and return continuation are appended even when the source
//! function performs no effects. The slow uniform shape is the load-bearing
//! invariant; selective omission belongs to the optimization stage.
//!
//! ## Module layout
//!
//! - `mod.rs`   — `Lowerer` struct + `lower_module` entry + decl dispatch
//! - `decls.rs` — per-`MDecl` CFunDef construction
//! - `exprs.rs` — MExpr → CExpr (STUB in 7a)
//! - `pats.rs`  — pattern lowering (param-only in 7a; full in 7g)
//! - `util.rs`  — local helpers copied from old lowerer (no imports per
//!   agent-guide allowlist)

#![allow(dead_code)] // 7a scaffolding; consumers land in 7b–7g.

mod decls;
mod effects;
mod exprs;
mod pats;
mod util;

use crate::codegen::CodegenContext;
use crate::codegen::cerl::CModule;
use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{EffectInfo, MDecl, MProgram};
use crate::codegen::resolve::{ConstructorAtoms, ResolutionMap};

use decls::{dict_constructor_arity, fun_binding_arity, val_arity};

/// New-path lowerer.
///
/// Holds read-only borrows of every input the lowering needs: the source-
/// `NodeId`-keyed resolution map, the constructor → atom table, the cross-
/// module codegen context, the handler-arm classification, and the narrowed
/// effect-info view. None of these are mutated; ownership stays with the
/// caller for the duration of `lower_module`.
///
/// **Type note (open):** the planning spec names this field's type
/// `ModuleCodegenContext`. No such type exists in the codebase today; the
/// existing `CodegenContext` (in `src/codegen/mod.rs`) is the only candidate
/// that fits the role. We use that here and flag the divergence — a follow-up
/// rename to `ModuleCodegenContext` is straightforward if the spec is the
/// canonical name.
pub struct Lowerer<'ctx> {
    resolution: &'ctx ResolutionMap,
    ctors: &'ctx ConstructorAtoms,
    module_ctx: &'ctx CodegenContext,
    handler_info: &'ctx HandlerAnalysis,
    effect_info: &'ctx EffectInfo<'ctx>,
    /// Name of the in-scope return continuation. Defaults to `_ReturnK` at
    /// every function/lambda entry; `Bind` lowering rebinds it temporarily
    /// to a freshly-generated `_K{n}` name for the duration of lowering the
    /// bound value.
    current_return_k: String,
    /// Monotonic counter for fresh K names. Reset at each function entry to
    /// keep emitted Core Erlang stable across decls.
    k_counter: u32,
    /// Name of the in-scope evidence vector variable. Defaults to `_Evidence`
    /// at every function/lambda entry; `With` lowering rebinds it temporarily
    /// to a freshly-generated `_Ev{n}` name for the duration of the handler's
    /// body, mirroring the [`current_return_k`] pattern.
    current_evidence: String,
    /// Monotonic counter for fresh evidence-var names. Reset at each function
    /// entry to keep emitted Core Erlang stable across decls.
    ev_counter: u32,
    /// Monotonic counter for fresh handler-arm continuation names (`_K_arm{n}`).
    /// Distinct from `k_counter` so Bind-K names stay stable as tests already
    /// pin them (`_K0`, `_K1`, ...) independently of any handler arms in scope.
    arm_k_counter: u32,
    /// Monotonic counter for fresh return-clause continuation names (`_K_ret{n}`).
    ret_k_counter: u32,
    /// Monotonic counter for fresh helper var names (`_HArg{n}` style is
    /// positional per arm; this counter is used for transient internals like
    /// return-clause param fallbacks).
    helper_counter: u32,
}

impl<'ctx> Lowerer<'ctx> {
    pub fn new(
        resolution: &'ctx ResolutionMap,
        ctors: &'ctx ConstructorAtoms,
        module_ctx: &'ctx CodegenContext,
        handler_info: &'ctx HandlerAnalysis,
        effect_info: &'ctx EffectInfo<'ctx>,
    ) -> Self {
        Self {
            resolution,
            ctors,
            module_ctx,
            handler_info,
            effect_info,
            current_return_k: exprs::RETURN_K_VAR.to_string(),
            k_counter: 0,
            current_evidence: exprs::EVIDENCE_VAR.to_string(),
            ev_counter: 0,
            arm_k_counter: 0,
            ret_k_counter: 0,
            helper_counter: 0,
        }
    }

    /// Mint a fresh handler-arm K name (`_K_arm{n}`). Distinct from Bind-K
    /// to keep emitted Core Erlang stable across changes to handler arms.
    pub(super) fn fresh_k_arm_name(&mut self) -> String {
        let n = self.arm_k_counter;
        self.arm_k_counter += 1;
        format!("_K_arm{}", n)
    }

    /// Mint a fresh return-clause K name (`_K_ret{n}`). Bound to the
    /// synthesized return-lambda; the handled body's tail-K is this var,
    /// so values flow `body → return-clause → outer K` automatically.
    pub(super) fn fresh_k_ret_name(&mut self) -> String {
        let n = self.ret_k_counter;
        self.ret_k_counter += 1;
        format!("_K_ret{}", n)
    }

    /// Mint a fresh helper name (`_H{n}`). Used for transient internals
    /// (e.g. return-clause param fallbacks).
    pub(super) fn fresh_helper_name(&mut self) -> String {
        let n = self.helper_counter;
        self.helper_counter += 1;
        format!("_H{}", n)
    }

    /// Mint a fresh Core Erlang variable name for a `With`-extended evidence
    /// vector. Form `_Ev{n}` — parallel to `_K{n}` from [`fresh_k_name`].
    pub(super) fn fresh_evidence_name(&mut self) -> String {
        let n = self.ev_counter;
        self.ev_counter += 1;
        format!("_Ev{}", n)
    }

    /// Mint a fresh Core Erlang variable name for a `Bind` continuation.
    /// Form `_K{n}` — starts with `_` so it is a valid Core Erlang var and
    /// is visually distinguishable from source-derived `_X` mangling.
    pub(super) fn fresh_k_name(&mut self) -> String {
        let n = self.k_counter;
        self.k_counter += 1;
        format!("_K{}", n)
    }

    /// Run `body` with `current_return_k` set to `k`, restoring the previous
    /// value afterward. Used by `Bind` to redirect the inner computation's
    /// tail to a freshly-bound continuation.
    pub(super) fn with_return_k<R>(&mut self, k: String, body: impl FnOnce(&mut Self) -> R) -> R {
        let prev = std::mem::replace(&mut self.current_return_k, k);
        let r = body(self);
        self.current_return_k = prev;
        r
    }

    /// Reset the K-naming counter and ambient return continuation at the
    /// start of a fresh function/lambda body.
    pub(super) fn reset_k_state(&mut self) {
        self.current_return_k = exprs::RETURN_K_VAR.to_string();
        self.k_counter = 0;
        self.current_evidence = exprs::EVIDENCE_VAR.to_string();
        self.ev_counter = 0;
        self.arm_k_counter = 0;
        self.ret_k_counter = 0;
        self.helper_counter = 0;
    }

    /// Lower an entire `MProgram` to a Core Erlang `CModule`.
    ///
    /// Iterates declarations in source order:
    ///   - `MFunBinding`, `MVal`, `MDictConstructor` → one `CFunDef` each
    ///   - `Passthrough(ast::Decl)` — most decl kinds emit no runtime code
    ///     (type/effect/trait/import/module headers). The few exceptions
    ///     (`@external` wrappers on `FunSignature`, etc.) are handled by a
    ///     later sub-step; in 7a they're silently skipped, which keeps the
    ///     scaffolding honest about what's stubbed.
    ///
    /// Export list:
    ///   - `MVal` carries its own `public` flag → exported when true.
    ///   - `MFunBinding` and `MDictConstructor` have no pub field on the IR.
    ///     For 7a, both are exported unconditionally so the emitted module
    ///     compiles standalone. Sub-step 7g (or earlier, if a real test
    ///     exposes the gap) wires this back to the source-decl visibility.
    pub fn lower_module(&mut self, module_name: &str, program: &MProgram) -> CModule {
        let mut exports = Vec::new();
        let mut funs = Vec::new();

        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    exports.push((fb.name.clone(), fun_binding_arity(&fb.params)));
                    funs.push(self.lower_fun_binding(fb));
                }
                MDecl::Val(v) => {
                    if v.public {
                        exports.push((v.name.clone(), val_arity()));
                    }
                    funs.push(self.lower_val(v));
                }
                MDecl::DictConstructor(dc) => {
                    exports.push((dc.name.clone(), dict_constructor_arity(dc)));
                    funs.push(self.lower_dict_constructor(dc));
                }
                MDecl::Passthrough(_) => {
                    // No runtime emission for type/effect/trait/import/module
                    // headers. `@external` wrappers and other code-emitting
                    // passthroughs are deferred to a later sub-step.
                }
            }
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }
}

#[cfg(test)]
mod tests;
