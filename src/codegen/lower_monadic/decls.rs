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
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CPat};
use crate::codegen::monadic::ir::{Atom, MDictConstructor, MExpr, MFunBinding, MVal};

use super::pats::lower_param_names;
use super::util::{identity_k, lower_external_native_call, type_expr_function_arity};
use super::{LowerCtx, Lowerer};

/// Variable name for the evidence-vector parameter on every emitted CFunDef.
pub(super) const EVIDENCE_VAR: &str = "_Evidence";
/// Variable name for the return-continuation parameter on every emitted CFunDef.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";

impl<'ctx> Lowerer<'ctx> {
    /// Lower an `MDecl::FunBinding` to a `CFunDef`.
    ///
    /// Signature: `(param_0, ..., param_{n-1}, _Evidence, _ReturnK)`.
    ///
    /// If any source param is a non-Var pattern (tuple destructure, literal,
    /// constructor pattern, etc.), route through [`lower_fun_binding_clauses`]
    /// with a single-element group — that already builds a `case` over the
    /// arg tuple, which is exactly what we need to bind the pattern's
    /// sub-variables so the body's references resolve. Without this, e.g.
    /// `normalize_suite (module_name, entries) = …` would get `_Arg0` as the
    /// param and leave `module_name` / `entries` unbound in the body.
    pub(super) fn lower_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        if fb.guard.is_some() || fb.params.iter().any(|p| !matches!(p, Pat::Var { .. })) {
            return self.lower_fun_binding_clauses(&[fb]);
        }
        let mut params = lower_param_names(&fb.params);
        params.push(EVIDENCE_VAR.to_string());
        params.push(RETURN_K_VAR.to_string());
        let arity = params.len();
        self.reset_counters();
        let body_ctx = LowerCtx::fresh().with_param_locals(&fb.params);
        let body = self.lower_expr(&fb.body, &body_ctx);
        CFunDef {
            name: fb.name.clone(),
            arity,
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    /// Lower a multi-clause function (group of `MFunBinding`s with the same
    /// name and arity) into a single `CFunDef`. Each clause's user-arg
    /// patterns become arms of a `case` over a tuple of fresh `_Arg{i}`
    /// parameters; the clause body is lowered under the standard K-threading
    /// rules — same convention as [`lower_fun_binding`].
    ///
    /// Saga source like:
    /// ```text
    /// supervised 0 f = body0
    /// supervised n f = body1
    /// ```
    /// emits:
    /// ```text
    /// 'supervised'/4 = fun (_Arg0, _Arg1, _Evidence, _ReturnK) ->
    ///   case {_Arg0, _Arg1} of
    ///     {0, F}  -> <body0>
    ///     {N, F}  -> <body1>
    ///   end
    /// ```
    /// Mirrors the old lowerer's `clause_groups` ([lower/mod.rs:1624-1648]).
    ///
    /// Invariant (asserted): every clause in `group` has the same arity.
    /// The translator preserves this from the source (the typechecker
    /// rejects clauses with mismatched arities).
    pub(super) fn lower_fun_binding_clauses(&mut self, group: &[&MFunBinding]) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_fun_binding_clauses: empty group is impossible"
        );
        let n_user = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                n_user,
                "lower_fun_binding_clauses: clause arity mismatch for '{}'",
                fb.name
            );
        }

        // Synthesize positional `_Arg{i}` user-arg params plus the uniform
        // `_Evidence` / `_ReturnK`. Names are uppercase so they're valid Core
        // Erlang variables and don't collide with source-level identifiers
        // (which `core_var` always produces with at least an `_` prefix or
        // capitalization mangling — `_Arg{i}` is in the same namespace).
        let arg_names: Vec<String> = (0..n_user).map(|i| format!("_Arg{}", i)).collect();
        let mut params = arg_names.clone();
        params.push(EVIDENCE_VAR.to_string());
        params.push(RETURN_K_VAR.to_string());
        let arity = params.len();

        // Build the case scrutinee: a tuple of the arg-var refs. Single-arg
        // functions could in principle skip the wrapping tuple; emitting it
        // uniformly keeps the lowering symmetric and matches the old path.
        let scrut = CExpr::Tuple(arg_names.iter().map(|v| CExpr::Var(v.clone())).collect());

        // Lower each clause body under a fresh K state (each clause is its
        // own tail context but they share the function-entry `_ReturnK`).
        let mut arms: Vec<CArm> = Vec::with_capacity(group.len());
        for fb in group {
            self.reset_counters();
            let pat = CPat::Tuple(fb.params.iter().map(|p| self.lower_pat(p)).collect());
            let body_ctx = LowerCtx::fresh().with_param_locals(&fb.params);
            let guard = fb.guard.as_ref().map(|g| self.lower_guard(g, &body_ctx));
            let body = self.lower_expr(&fb.body, &body_ctx);
            arms.push(CArm { pat, guard, body });
        }

        let case_body = CExpr::Case(Box::new(scrut), arms);
        CFunDef {
            name: group[0].name.clone(),
            arity,
            body: CExpr::Fun(params, Box::new(case_body)),
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
    /// `lower_expr` ends every tail with `apply <ctx.return_k>(value)`,
    /// so we bind `_ReturnK` locally to the identity function inside the
    /// arity-0 wrapper — the final `apply` then beta-reduces (in spirit;
    /// the Erlang compiler does the actual inlining) to just the value.
    ///
    /// `_Evidence` is similarly bound to a dummy atom so any stray
    /// reference (defensive — pure bodies should not produce one) doesn't
    /// surface as an unbound-var error in `erlc`.
    pub(super) fn lower_val(&mut self, v: &MVal) -> CFunDef {
        self.reset_counters();
        let body_inner = self.lower_expr(&v.value, &LowerCtx::fresh());
        // let <_Evidence> = 'unit', <_ReturnK> = fun (_X) -> _X in <body_inner>
        let id_k = identity_k("_X");
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

    /// Lower an `MDecl::DictConstructor` to a `CFunDef` under the uniform
    /// calling convention.
    ///
    /// Signature: `(dict_params..., _Evidence, _ReturnK)`. The body
    /// synthesises the dict tuple `{method_0, method_1, ...}` (each method
    /// statically `Pure(Atom::Lambda { .. })` per [`MDictConstructor`]'s
    /// IR spec) and feeds it through `_ReturnK`, exactly like every other
    /// callable in the new path.
    pub(super) fn lower_dict_constructor(&mut self, dc: &MDictConstructor) -> CFunDef {
        let mut params: Vec<String> = dc
            .dict_params
            .iter()
            .map(|p| super::util::core_var(p))
            .collect();
        params.push(EVIDENCE_VAR.to_string());
        params.push(RETURN_K_VAR.to_string());
        let arity = params.len();
        self.reset_counters();

        let method_ces: Vec<CExpr> = dc
            .methods
            .iter()
            .map(|m| match m {
                MExpr::Pure(atom @ Atom::Lambda { .. }) => {
                    let body_ctx =
                        super::ctx::LowerCtx::fresh().with_locals(dc.dict_params.iter().cloned());
                    self.lower_atom(atom, &body_ctx)
                }
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
    // Uniform calling convention: dict ctors expose the same
    // `(args…, _Evidence, _ReturnK)` shape as every other callable.
    dc.dict_params.len() + 2
}

/// Extract the `(erl_module, erl_func)` pair from an
/// `@external("runtime", "<mod>", "<func>")` annotation list. Returns
/// `None` when no such annotation is present. Copied from
/// `src/codegen/lower/init.rs::extract_external` per the agent-guide's
/// "no imports from frozen files" rule.
fn extract_external(annotations: &[Annotation]) -> Option<(String, String)> {
    annotations
        .iter()
        .find(|a| a.name == "external")
        .and_then(|a| {
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

    // For each function-typed param, the wrapper receives a uniform-CPS Saga
    // lambda but the native BIF expects a native-arity Erlang fun. Build an
    // adapter `_Adapter{i} = fun(args...) -> apply _Ext{i}(args..., _Evidence,
    // identity_K)` and pass the adapter to the BIF in that position. Identity
    // K means the Saga callback's resumption flows through as the apply's
    // return value — correct for pure callbacks; effectful callbacks (which
    // would route control through K rather than returning) are an open design
    // question, not blocked here.
    let mut adapter_bindings: Vec<(String, CExpr)> = Vec::new();
    let call_args: Vec<(usize, CExpr)> = param_vars
        .iter()
        .zip(params.iter())
        .enumerate()
        .filter(|(_, (_, (_, ty)))| !is_unit_type_expr(ty))
        .map(|(idx, (v, (_, ty)))| {
            if let Some(callback_arity) = type_expr_function_arity(ty) {
                let adapter_name = format!("_Adapter{}", idx);
                let adapter = build_callback_adapter(v, callback_arity, EVIDENCE_VAR);
                adapter_bindings.push((adapter_name.clone(), adapter));
                (idx, CExpr::Var(adapter_name))
            } else {
                (idx, CExpr::Var(v.clone()))
            }
        })
        .collect();
    param_vars.push(EVIDENCE_VAR.to_string());
    param_vars.push(RETURN_K_VAR.to_string());
    let total_arity = param_vars.len();

    let call = lower_external_native_call(&erl_module, &erl_func, call_args);
    let mut body = CExpr::Apply(Box::new(CExpr::Var(RETURN_K_VAR.to_string())), vec![call]);
    // Wrap adapter bindings inside-out: outer adapter visible to all inner
    // code, but order doesn't matter (each adapter only closes over `_ExtN`).
    for (adapter_name, adapter) in adapter_bindings.into_iter().rev() {
        body = CExpr::Let(adapter_name, Box::new(adapter), Box::new(body));
    }

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

/// Build `fun(_CbArg0, …, _CbArg{n-1}) -> apply <callback_var>(_CbArg0, …,
/// _CbArg{n-1}, <evidence_var>, fun(_V) -> _V end)`. Wraps a Saga uniform-CPS
/// callback (`fun(args…, _Evidence, _ReturnK)`) for use by a native BIF that
/// expects `fun(args…)`. Identity K means the callback's return value flows
/// through as the apply's result.
fn build_callback_adapter(callback_var: &str, arity: usize, evidence_var: &str) -> CExpr {
    let cb_args: Vec<String> = (0..arity).map(|i| format!("_CbArg{}", i)).collect();
    let k_var = "_CbK".to_string();
    let v_var = "_CbV".to_string();
    let id_k = identity_k(v_var);
    let mut apply_args: Vec<CExpr> = cb_args.iter().cloned().map(CExpr::Var).collect();
    apply_args.push(CExpr::Var(evidence_var.to_string()));
    apply_args.push(CExpr::Var(k_var.clone()));
    let apply_callback = CExpr::Apply(Box::new(CExpr::Var(callback_var.to_string())), apply_args);
    CExpr::Fun(
        cb_args,
        Box::new(CExpr::Let(k_var, Box::new(id_k), Box::new(apply_callback))),
    )
}

/// Lower a `@builtin` `FunSignature` decl into a wrapper `CFunDef` that
/// performs the intrinsic inline. Returns `None` for non-builtin decls or
/// for builtins this stage doesn't know how to wrap yet.
///
/// **Why a wrapper?** Builtins like `Std.Process.catch_panic` are
/// `@builtin`-annotated decls that the old lowerer special-cases at every
/// `App` site via `lower_intrinsic`. The new path's uniform calling
/// convention means a builtin used in value position (`let f = catch_panic
/// in …`) — or even called via the standard `App` path — needs an actual
/// callable function with the uniform shape `(user_args…, _Evidence,
/// _ReturnK)`. Generating one wrapper per builtin per defining module
/// keeps the lowerer's App/value paths uniform with no intrinsic-specific
/// branches.
pub(super) fn lower_builtin_wrapper(decl: &Decl) -> Option<(CFunDef, usize, bool)> {
    let Decl::FunSignature {
        public,
        name,
        annotations,
        ..
    } = decl
    else {
        return None;
    };
    if !annotations.iter().any(|a| a.name == "builtin") {
        return None;
    }
    match name.as_str() {
        "catch_panic" => Some((build_catch_panic_wrapper(name.clone()), 3, *public)),
        "print_stdout" => Some((build_print_wrapper(name.clone(), false), 3, *public)),
        "print_stderr" => Some((build_print_wrapper(name.clone(), true), 3, *public)),
        "dbg" => Some((build_dbg_wrapper(name.clone()), 4, *public)),
        _ => None,
    }
}

/// Wrapper for `print_stdout` / `print_stderr` builtins. Shape:
///
/// ```text
/// fun (S, _Evidence, _ReturnK) ->
///   let <_R> = call 'io':'format' (["standard_error", ]"~ts", [S])
///   in apply _ReturnK('unit')
/// ```
fn build_print_wrapper(name: String, stderr: bool) -> CFunDef {
    let s_param = "S".to_string();
    let r_var = "_R".to_string();

    let mut fmt_args: Vec<CExpr> = vec![
        CExpr::Lit(crate::codegen::cerl::CLit::Str("~ts".to_string())),
        CExpr::Cons(Box::new(CExpr::Var(s_param.clone())), Box::new(CExpr::Nil)),
    ];
    if stderr {
        fmt_args.insert(
            0,
            CExpr::Lit(crate::codegen::cerl::CLit::Atom(
                "standard_error".to_string(),
            )),
        );
    }
    let print_call = CExpr::Call("io".to_string(), "format".to_string(), fmt_args);
    let apply_k = CExpr::Apply(
        Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
        vec![CExpr::Lit(crate::codegen::cerl::CLit::Atom(
            "unit".to_string(),
        ))],
    );
    let body = CExpr::Let(r_var, Box::new(print_call), Box::new(apply_k));

    CFunDef {
        name,
        arity: 3,
        body: CExpr::Fun(
            vec![s_param, EVIDENCE_VAR.to_string(), RETURN_K_VAR.to_string()],
            Box::new(body),
        ),
    }
}

/// Wrapper for `dbg` builtin. After elaboration the user-facing call
/// `dbg x` becomes `dbg dict x`, so the uniform wrapper has shape
/// `(Dict, X, _Evidence, _ReturnK)`.
///
/// ```text
/// fun (Dict, X, _Evidence, _ReturnK) ->
///   let <_DebugFn> = call 'erlang':'element'(1, Dict) in
///   let <_Str> = apply _DebugFn(X) in
///   let <_R> = call 'io':'format'('standard_error', "~ts~n", [_Str])
///   in apply _ReturnK('unit')
/// ```
///
/// **Note.** The dict's debug method is itself a uniform-shape closure
/// (`fun(X, _Evidence, _ReturnK) -> …`), so applying it as `_DebugFn(X)`
/// alone would underfill the arity. The wrapper threads outer
/// `_Evidence` and an identity continuation through.
fn build_dbg_wrapper(name: String) -> CFunDef {
    let dict_param = "Dict".to_string();
    let x_param = "X".to_string();
    let debug_fn_var = "_DebugFn".to_string();
    let id_k_var = "_IdK".to_string();
    let v_param = "_V".to_string();
    let str_var = "_Str".to_string();
    let r_var = "_R".to_string();

    let extract = CExpr::Call(
        "erlang".to_string(),
        "element".to_string(),
        vec![
            CExpr::Lit(crate::codegen::cerl::CLit::Int(1)),
            CExpr::Var(dict_param.clone()),
        ],
    );
    let id_k = identity_k(v_param);
    let apply_debug = CExpr::Apply(
        Box::new(CExpr::Var(debug_fn_var.clone())),
        vec![
            CExpr::Var(x_param.clone()),
            CExpr::Var(EVIDENCE_VAR.to_string()),
            CExpr::Var(id_k_var.clone()),
        ],
    );
    let print = CExpr::Call(
        "io".to_string(),
        "format".to_string(),
        vec![
            CExpr::Lit(crate::codegen::cerl::CLit::Atom(
                "standard_error".to_string(),
            )),
            CExpr::Lit(crate::codegen::cerl::CLit::Str("~ts~n".to_string())),
            CExpr::Cons(Box::new(CExpr::Var(str_var.clone())), Box::new(CExpr::Nil)),
        ],
    );
    let apply_k = CExpr::Apply(
        Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
        vec![CExpr::Lit(crate::codegen::cerl::CLit::Atom(
            "unit".to_string(),
        ))],
    );

    let let_r = CExpr::Let(r_var, Box::new(print), Box::new(apply_k));
    let let_str = CExpr::Let(str_var, Box::new(apply_debug), Box::new(let_r));
    let let_id_k = CExpr::Let(id_k_var, Box::new(id_k), Box::new(let_str));
    let let_debug_fn = CExpr::Let(debug_fn_var, Box::new(extract), Box::new(let_id_k));

    CFunDef {
        name,
        arity: 4,
        body: CExpr::Fun(
            vec![
                dict_param,
                x_param,
                EVIDENCE_VAR.to_string(),
                RETURN_K_VAR.to_string(),
            ],
            Box::new(let_debug_fn),
        ),
    }
}

/// Build the wrapper for `Std.Process.catch_panic`. Equivalent to the old
/// lowerer's `lower_catch_panic` but materialized as a standalone
/// `CFunDef`. Shape (3-arity uniform: 1 user param + `_Evidence` +
/// `_ReturnK`):
///
/// ```text
/// fun (F, _Evidence, _ReturnK) ->
///   let <_IdK> = fun (_V) -> _V in
///   let <_Result> =
///     try apply F('unit', _Evidence, _IdK)
///     of <_OkVal> -> {'ok', _OkVal}
///     catch <_Cls, _Reason, _Trace> ->
///       case _Reason of
///         {'saga_error', _, Msg, _, _, _, _} -> {'error', Msg}
///         _ -> {'error', call 'saga_runtime':'format_caught_panic'(_Cls, _Reason)}
///       end
///   in apply _ReturnK(_Result)
/// ```
///
/// The `_IdK` (identity continuation) isolates the thunk's tail-apply from
/// the outer `_ReturnK`: the thunk is invoked under uniform CPS shape, but
/// its result must materialize as a value so we can wrap it in `{'ok', …}`
/// and pass through `_ReturnK` only after the try/catch resolves.
fn build_catch_panic_wrapper(name: String) -> CFunDef {
    let f_param = "F".to_string();
    let id_k_var = "_IdK".to_string();
    let id_k_param = "_V".to_string();
    let ok_var = "_OkVal".to_string();
    let class_var = "_Cls".to_string();
    let reason_var = "_Reason".to_string();
    let trace_var = "_Trace".to_string();
    let msg_var = "Msg".to_string();
    let result_var = "_Result".to_string();

    let id_k = identity_k(id_k_param);

    let applied = CExpr::Apply(
        Box::new(CExpr::Var(f_param.clone())),
        vec![
            CExpr::Lit(crate::codegen::cerl::CLit::Atom("unit".to_string())),
            CExpr::Var(EVIDENCE_VAR.to_string()),
            CExpr::Var(id_k_var.clone()),
        ],
    );

    let ok_body = CExpr::Tuple(vec![
        CExpr::Lit(crate::codegen::cerl::CLit::Atom("ok".to_string())),
        CExpr::Var(ok_var.clone()),
    ]);

    let catch_body = CExpr::Case(
        Box::new(CExpr::Var(reason_var.clone())),
        vec![
            CArm {
                pat: CPat::Tuple(vec![
                    CPat::Lit(crate::codegen::cerl::CLit::Atom("saga_error".to_string())),
                    CPat::Wildcard,
                    CPat::Var(msg_var.clone()),
                    CPat::Wildcard,
                    CPat::Wildcard,
                    CPat::Wildcard,
                    CPat::Wildcard,
                ]),
                guard: None,
                body: CExpr::Tuple(vec![
                    CExpr::Lit(crate::codegen::cerl::CLit::Atom("error".to_string())),
                    CExpr::Var(msg_var),
                ]),
            },
            CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: CExpr::Tuple(vec![
                    CExpr::Lit(crate::codegen::cerl::CLit::Atom("error".to_string())),
                    CExpr::Call(
                        "saga_runtime".to_string(),
                        "format_caught_panic".to_string(),
                        vec![
                            CExpr::Var(class_var.clone()),
                            CExpr::Var(reason_var.clone()),
                        ],
                    ),
                ]),
            },
        ],
    );

    let try_expr = CExpr::Try {
        expr: Box::new(applied),
        ok_var,
        ok_body: Box::new(ok_body),
        catch_vars: (class_var, reason_var, trace_var),
        catch_body: Box::new(catch_body),
    };

    let apply_k = CExpr::Apply(
        Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
        vec![CExpr::Var(result_var.clone())],
    );

    let let_result = CExpr::Let(result_var, Box::new(try_expr), Box::new(apply_k));
    let body = CExpr::Let(id_k_var, Box::new(id_k), Box::new(let_result));

    CFunDef {
        name,
        arity: 3,
        body: CExpr::Fun(
            vec![f_param, EVIDENCE_VAR.to_string(), RETURN_K_VAR.to_string()],
            Box::new(body),
        ),
    }
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
