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

use crate::ast::{self, Annotation, Decl, Lit, Pat, TypeExpr};
use crate::codegen::cerl::{CExpr, CFunDef};
use crate::codegen::monadic::ir::{Atom, MDictConstructor, MExpr, MFunBinding, MVal};

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
        self.reset_k_state();
        let body = self.lower_expr(&fb.body);
        CFunDef {
            name: fb.name.clone(),
            arity,
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    /// Lower an `MDecl::Val` to a `CFunDef`.
    ///
    /// Vals are pure, arity-0 constants — Saga's language design routes
    /// effectful computations through ordinary functions, so a val's body
    /// never performs effects. The export shape matches the old lowerer:
    /// `mod:name/0`, with no `_Evidence` / `_ReturnK` threading at the
    /// calling convention.
    ///
    /// However, after ANF + monadic translation, the body's `MExpr` shape
    /// is not restricted to `Pure(atom)` — it may contain `Bind` / `Let` /
    /// `If` / `Case` / `BinOp` etc. (a `val x = 1 + 2`, for instance).
    /// `lower_expr` ends every tail with `apply <current_return_k>(value)`,
    /// so we bind `_ReturnK` locally to the identity function inside the
    /// arity-0 wrapper — the final `apply` then beta-reduces (in spirit;
    /// the Erlang compiler does the actual inlining) to just the value.
    ///
    /// `_Evidence` is similarly bound to a dummy atom so any stray
    /// reference (defensive — pure bodies should not produce one) doesn't
    /// surface as an unbound-var error in `erlc`.
    pub(super) fn lower_val(&mut self, v: &MVal) -> CFunDef {
        self.reset_k_state();
        let body_inner = self.lower_expr(&v.value);
        // let <_Evidence> = 'unit', <_ReturnK> = fun (_X) -> _X in <body_inner>
        let id_param = "_X".to_string();
        let id_k = CExpr::Fun(vec![id_param.clone()], Box::new(CExpr::Var(id_param)));
        let evidence_dummy = CExpr::Lit(crate::codegen::cerl::CLit::Atom("unit".to_string()));
        let body_with_k = CExpr::Let(
            RETURN_K_VAR.to_string(),
            Box::new(id_k),
            Box::new(body_inner),
        );
        let body = CExpr::Let(
            EVIDENCE_VAR.to_string(),
            Box::new(evidence_dummy),
            Box::new(body_with_k),
        );
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
    /// Lower an `MDecl::DictConstructor` to a `CFunDef`.
    ///
    /// Signature: `(dict_params..., _Evidence, _ReturnK)`. The body is a
    /// tuple of the dict's methods — each method is statically known to be
    /// `Pure(Atom::Lambda { .. })` per [`MDictConstructor`]'s IR spec, so
    /// we extract the lambda atom from each and lower it via `lower_atom`
    /// (yielding a `CExpr::Fun` with the uniform calling convention). The
    /// resulting tuple is returned through `_ReturnK`, matching every
    /// other uniform-shape callable.
    ///
    /// **Open question.** The dict ctor is called like a normal fn at the
    /// callsite (`apply __dict_Show_Int(_Evidence, _K)`); returning through
    /// `_ReturnK` is the same convention as any other fn. If a future use
    /// site invokes the ctor specially (module-init context with no K in
    /// scope), the uniform shape will need to drop — flagging now so the
    /// integration step (7d/8) can catch it.
    pub(super) fn lower_dict_constructor(&mut self, dc: &MDictConstructor) -> CFunDef {
        let mut params: Vec<String> = dc
            .dict_params
            .iter()
            .map(|p| super::util::core_var(p))
            .collect();
        params.push(EVIDENCE_VAR.to_string());
        params.push(RETURN_K_VAR.to_string());
        let arity = params.len();
        self.reset_k_state();

        let method_ces: Vec<CExpr> = dc
            .methods
            .iter()
            .map(|m| match m {
                MExpr::Pure(atom @ Atom::Lambda { .. }) => self.lower_atom(atom),
                other => panic!(
                    "lower_dict_constructor: expected Pure(Atom::Lambda) per IR spec, got {:?}",
                    std::mem::discriminant(other)
                ),
            })
            .collect();

        let tuple = CExpr::Tuple(method_ces);
        let body = CExpr::Apply(Box::new(CExpr::Var(RETURN_K_VAR.to_string())), vec![tuple]);

        CFunDef {
            name: dc.name.clone(),
            arity,
            body: CExpr::Fun(params, Box::new(body)),
        }
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

/// Extract the `(erl_module, erl_func)` pair from an
/// `@external("runtime", "<mod>", "<func>")` annotation list. Returns
/// `None` when no such annotation is present. Copied from
/// `src/codegen/lower/init.rs::extract_external` per the agent-guide's
/// "no imports from frozen files" rule.
fn extract_external(annotations: &[Annotation]) -> Option<(String, String)> {
    annotations.iter().find(|a| a.name == "external").and_then(|a| {
        if a.args.len() >= 3
            && let (Lit::String(module, _), Lit::String(func, _)) = (&a.args[1], &a.args[2])
        {
            Some((module.clone(), func.clone()))
        } else {
            None
        }
    })
}

/// Lower an `@external` `FunSignature` decl into a wrapper `CFunDef`.
///
/// Returns `Some((CFunDef, exported_arity, public))` for FunSignature decls
/// carrying an `@external("runtime", "<mod>", "<func>")` annotation;
/// `None` for any other decl shape (callers skip those).
///
/// **Shape.** Under the new path's uniform calling convention, every
/// callable receives `(user_args..., _Evidence, _ReturnK)`. External
/// wrappers bridge to a raw BIF that doesn't know about evidence or
/// continuations — so the wrapper:
///
/// ```text
/// fun (_Ext0, ..., _ExtN, _Evidence, _ReturnK) ->
///   apply _ReturnK(call '<mod>':'<func>'(_Ext0, ..., _ExtN))
/// ```
///
/// `_Evidence` is unused at the wrapper level (the wrapped BIF performs
/// no effects), but the param is included so the wrapper has the uniform
/// arity every caller of the new path expects.
///
/// **Unit-type filtering.** The old lowerer skips `Unit`-typed params
/// from the BIF call (`is_unit_type_expr(ty)`) — Saga's `Unit` becomes
/// the runtime atom `'unit'`, which most BIFs don't accept. We mirror
/// the same filter so the emitted call shape matches the old path.
pub(super) fn lower_external_wrapper(decl: &Decl) -> Option<(CFunDef, usize, bool)> {
    let Decl::FunSignature {
        public,
        name,
        params,
        annotations,
        ..
    } = decl
    else {
        return None;
    };
    let (erl_module, erl_func) = extract_external(annotations)?;
    let user_arity = params.len();

    // User-arg param names; Evidence + ReturnK appended for uniform shape.
    let mut param_vars: Vec<String> = (0..user_arity).map(|i| format!("_Ext{}", i)).collect();
    let call_args: Vec<CExpr> = param_vars
        .iter()
        .zip(params.iter())
        .filter(|(_, (_, ty))| !is_unit_type_expr(ty))
        .map(|(v, _)| CExpr::Var(v.clone()))
        .collect();
    param_vars.push(EVIDENCE_VAR.to_string());
    param_vars.push(RETURN_K_VAR.to_string());
    let total_arity = param_vars.len();

    let call = CExpr::Call(erl_module, erl_func, call_args);
    let body = CExpr::Apply(
        Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
        vec![call],
    );

    Some((
        CFunDef {
            name: name.clone(),
            arity: total_arity,
            body: CExpr::Fun(param_vars, Box::new(body)),
        },
        total_arity,
        *public,
    ))
}

/// Returns `true` if the given AST type expression resolves to `Unit`.
/// Copied verbatim from `src/codegen/lower/mod.rs::is_unit_type_expr`.
fn is_unit_type_expr(ty: &TypeExpr) -> bool {
    match ty {
        TypeExpr::Named { name, .. } => {
            crate::typechecker::canonicalize_type_name(name)
                == crate::typechecker::canonicalize_type_name("Unit")
        }
        TypeExpr::Labeled { inner, .. } => is_unit_type_expr(inner),
        _ => false,
    }
}

// Keep `ast` import referenced to avoid an "unused" warning when the
// concrete `Decl::FunSignature` pattern above doesn't drag the prelude
// in by itself.
const _: fn() = || {
    let _ = std::marker::PhantomData::<ast::Decl>;
};
