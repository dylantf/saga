//! Monadic-IR → Core Erlang expression lowering.
//!
//! Sub-step 7b: `Atom → CExpr` lowering for every variant of the `Atom`
//! enum from `monadic-ir-spec.md`. Structural `MExpr` variants are still
//! stubbed; they arrive in sub-step 7c.

use crate::ast::Pat;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::monadic::ir::{Atom, MExpr, MVar};

use super::pats::lower_param_names;
use super::util::core_var;
use super::{LowerCtx, Lowerer};

// Name of the function-entry return-continuation variable. Every emitted
// CFunDef binds this as its trailing parameter (after `_Evidence`); the body
// applies it to the function's final value. Kept in sync with `decls.rs`.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";
/// Function-entry evidence-vector parameter name. Kept in sync with
/// `decls.rs`'s [`EVIDENCE_VAR`].
pub(super) const EVIDENCE_VAR: &str = "_Evidence";
const ABORT_TAG: &str = "__saga_handler_abort";

impl<'ctx> Lowerer<'ctx> {
    // ---------------------------------------------------------------
    // MExpr lowering (sub-step 7c)
    // ---------------------------------------------------------------

    /// Lower an `MExpr` in tail position relative to the surrounding function/
    /// lambda's return continuation.
    ///
    /// The ambient continuation is read from `ctx.return_k`. Every
    /// computation either passes its result to that K (`Pure`, `App`,
    /// arms of `Case`/`If`) or rebinds K to a fresh continuation that
    /// performs the rest of the work (`Bind`).
    ///
    /// 7c scope: `Pure`, `Bind`, `Let`, `Case`, `If`, `App`. Everything
    /// else panics with a deferred-step message; effect machinery (`Yield`,
    /// `With`, `Resume`) lands in 7d; foreign / builtin ops in 7g.
    pub(super) fn lower_expr(&mut self, expr: &MExpr, ctx: &LowerCtx) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_pure(atom, ctx),
            MExpr::Bind { var, value, body } => self.lower_bind(var, value, body, ctx),
            MExpr::Let { var, value, body } => self.lower_let(var, value, body, ctx),
            MExpr::Case {
                scrutinee, arms, ..
            } => self.lower_case(scrutinee, arms, ctx),
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(cond, then_branch, else_branch, ctx),
            MExpr::App { head, args, .. } => self.lower_app(head, args, ctx),
            MExpr::Yield { op, args, .. } => self.lower_yield(op, args, ctx),
            MExpr::With { handler, body, .. } => self.lower_with(handler, body, ctx),
            MExpr::Resume { value, .. } => self.lower_resume(value, ctx),
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                ..
            } => self.lower_field_access(record, field, record_name.as_deref(), ctx),
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                ..
            } => self.lower_record_update(record, fields, record_name.as_deref(), ctx),
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => self.lower_dict_method_access(dict, *method_index, ctx),
            MExpr::ForeignCall {
                module, func, args, ..
            } => self.lower_foreign_call(module, func, args, ctx),
            MExpr::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right, ctx),
            MExpr::UnaryMinus { value, .. } => self.lower_unary_minus(value, ctx),
            MExpr::BitString { segments, .. } => self.lower_bitstring(segments, ctx),
            MExpr::Receive { arms, after, .. } => self.lower_receive(arms, after.as_ref(), ctx),
            MExpr::LetFun {
                name,
                params,
                body,
                rest,
                ..
            } => self.lower_let_fun(name, params, body, rest, ctx),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => self.lower_handler_value(arms, return_clause.as_deref(), ctx),
        }
    }

    /// Lower `MExpr::HandlerValue` to a runtime op-tuple. Each arm is
    /// compiled as a direct-returning handler-value closure: it can call the
    /// perform-site `resume` continuation, then returns the arm result to the
    /// dynamic `with` delimiter instead of applying the definition-site K.
    fn lower_handler_value(
        &mut self,
        arms: &[crate::codegen::monadic::ir::MHandlerArm],
        return_clause: Option<&crate::codegen::monadic::ir::MHandlerArm>,
        ctx: &LowerCtx,
    ) -> CExpr {
        // Use a fresh context so arm closures are self-contained and don't
        // capture the definition site's return_k/evidence.
        let mut sorted_arms: Vec<&crate::codegen::monadic::ir::MHandlerArm> = arms.iter().collect();
        sorted_arms.sort_by_key(|a| (a.op.effect.clone(), a.op.op_index));
        let elements: Vec<CExpr> = sorted_arms
            .iter()
            .map(|arm| self.build_handler_value_arm_closure(arm, ctx))
            .collect();
        // Dynamic handler return clauses need an explicit runtime ABI slot;
        // until that lands, only op arms participate in the op tuple.
        let _ = return_clause;
        let tuple = CExpr::Tuple(elements);
        self.apply_current_k(tuple, ctx)
    }

    /// Lower `MExpr::LetFun { name, params, body, rest }` to a Core Erlang
    /// `letrec`. The bound function follows the uniform calling
    /// convention `(params…, _Evidence, _ReturnK)` so call sites that
    /// resolved the name to a `BeamFunction { erlang_mod: None }` via
    /// the backend resolution map find it at the expected arity.
    ///
    /// Body lowers under a fresh K context — its `_ReturnK` is its own
    /// parameter, not the enclosing fn's continuation.
    fn lower_let_fun(
        &mut self,
        name: &str,
        params: &[Pat],
        body: &MExpr,
        rest: &MExpr,
        ctx: &LowerCtx,
    ) -> CExpr {
        let has_non_var_pat = params.iter().any(|p| !matches!(p, Pat::Var { .. }));
        let mut param_vars: Vec<String> = if has_non_var_pat {
            (0..params.len()).map(|i| format!("_Arg{}", i)).collect()
        } else {
            lower_param_names(params)
        };
        param_vars.push(EVIDENCE_VAR.to_string());
        param_vars.push(RETURN_K_VAR.to_string());
        let arity = param_vars.len();

        let snap = self.snapshot_counters();
        self.reset_counters();
        let body_ctx = LowerCtx::fresh().with_param_locals(params);
        let body_ce_inner = self.lower_expr(body, &body_ctx);
        let body_ce = if has_non_var_pat {
            let scrut = CExpr::Tuple(
                (0..params.len())
                    .map(|i| CExpr::Var(format!("_Arg{}", i)))
                    .collect(),
            );
            let pat = CPat::Tuple(params.iter().map(|p| self.lower_pat(p)).collect());
            CExpr::Case(
                Box::new(scrut),
                vec![CArm {
                    pat,
                    guard: None,
                    body: body_ce_inner,
                }],
            )
        } else {
            body_ce_inner
        };
        self.restore_counters(snap);

        let fun = CExpr::Fun(param_vars, Box::new(body_ce));
        let rest_ce = self.lower_expr(rest, ctx);
        CExpr::LetRec(vec![(name.to_string(), arity, fun)], Box::new(rest_ce))
    }

    /// `Resume(atom)` → bind the value returned by the perform-site K, then
    /// continue locally.
    ///
    /// Inside a handler arm, the captured `_K_arm{n}` is a delimited
    /// continuation: applying it returns the eventual value of the enclosing
    /// `with` body from the perform site. `resume` is therefore a
    /// value-producing expression, not just a tail jump. The local
    /// `ctx.return_k` still matters for suffixes such as `let r = resume s;
    /// r s`.
    fn lower_resume(&mut self, value: &Atom, ctx: &LowerCtx) -> CExpr {
        let v = self.lower_atom(value, ctx);
        let k = ctx.arm_k.as_ref().unwrap_or_else(|| {
            panic!(
                "lower_resume: arm_k is None — `resume` reached without an enclosing arm body. \
                 This indicates either a translator bug (Resume outside arm body) or an arm_k \
                 propagation bug (lambda body lost the enclosing arm K)."
            )
        });
        let resumed = self.fresh_helper_name();
        let resume_call = CExpr::Apply(Box::new(CExpr::Var(k.clone())), vec![v]);
        let resumed_value = if let Some(marker) = &ctx.abort_marker {
            let raw_resumed = self.fresh_helper_name();
            let abort_value = self.fresh_helper_name();
            let other_marker = self.fresh_helper_name();
            let other_abort_value = self.fresh_helper_name();
            CExpr::Let(
                raw_resumed.clone(),
                Box::new(resume_call),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(raw_resumed)),
                    vec![
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom(ABORT_TAG.to_string())),
                                CPat::Lit(CLit::Atom(marker.clone())),
                                CPat::Var(abort_value.clone()),
                            ]),
                            guard: None,
                            body: CExpr::Var(abort_value),
                        },
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom(ABORT_TAG.to_string())),
                                CPat::Var(other_marker.clone()),
                                CPat::Var(other_abort_value.clone()),
                            ]),
                            guard: None,
                            body: CExpr::Tuple(vec![
                                CExpr::Lit(CLit::Atom(ABORT_TAG.to_string())),
                                CExpr::Var(other_marker),
                                CExpr::Var(other_abort_value),
                            ]),
                        },
                        CArm {
                            pat: CPat::Var("_ResumeValue".to_string()),
                            guard: None,
                            body: CExpr::Var("_ResumeValue".to_string()),
                        },
                    ],
                )),
            )
        } else {
            resume_call
        };

        if let Some(finally_expr) = ctx.finally_block.clone() {
            let cleanup_k = self.fresh_helper_name();
            let cleanup_ctx = ctx.without_finally().with_return_k(cleanup_k.clone());
            let cleanup_ce = self.lower_expr(&finally_expr, &cleanup_ctx);
            let cleanup_done_k = CExpr::Fun(
                vec!["_".to_string()],
                Box::new(CExpr::Lit(crate::codegen::cerl::CLit::Atom(
                    "unit".to_string(),
                ))),
            );
            CExpr::Let(
                cleanup_k,
                Box::new(cleanup_done_k),
                Box::new(CExpr::Let(
                    resumed.clone(),
                    Box::new(resumed_value),
                    Box::new(CExpr::Let(
                        "_".to_string(),
                        Box::new(cleanup_ce),
                        Box::new(self.apply_current_k(CExpr::Var(resumed), ctx)),
                    )),
                )),
            )
        } else {
            CExpr::Let(
                resumed.clone(),
                Box::new(resumed_value),
                Box::new(self.apply_current_k(CExpr::Var(resumed), ctx)),
            )
        }
    }

    /// `Pure(atom)` → `apply <current_K>(<atom>)`.
    fn lower_pure(&mut self, atom: &Atom, ctx: &LowerCtx) -> CExpr {
        let value = self.lower_atom(atom, ctx);
        self.apply_current_k(value, ctx)
    }

    /// Apply the in-scope return continuation to a single value.
    pub(super) fn apply_current_k(&self, value: CExpr, ctx: &LowerCtx) -> CExpr {
        CExpr::Apply(Box::new(CExpr::Var(ctx.return_k.clone())), vec![value])
    }

    /// Lower `Bind { var, value, body }`:
    ///
    /// ```text
    /// let _K{n} = fun (Var) -> <body under outer K>
    /// in <value under _K{n}>
    /// ```
    ///
    /// The body is lowered first so it sees the *current* K. We then mint a
    /// fresh K name, build the continuation closure, swap it in as the
    /// ambient K, and lower the bound `value` under it. The result is a
    /// plain Core Erlang `let` binding the continuation — straightforward
    /// CPS reification.
    fn lower_bind(&mut self, var: &MVar, value: &MExpr, body: &MExpr, ctx: &LowerCtx) -> CExpr {
        let body_ctx = ctx.with_local(var.name.clone());
        let body_ce = self.lower_expr(body, &body_ctx);
        let bound_var = core_var(&var.name);
        let k_name = self.fresh_k_name();
        let k_fun = CExpr::Fun(vec![bound_var], Box::new(body_ce));
        let value_ce = self.lower_expr(value, &ctx.with_return_k(k_name.clone()));
        CExpr::Let(k_name, Box::new(k_fun), Box::new(value_ce))
    }

    /// Lower `Let { var, value, body }` — a pure (non-yielding) binder
    /// produced by effect optimization's Bind→Let promotion rewrite.
    ///
    /// 7c restriction: `value` must be `Pure(atom)`. The translator never
    /// emits `Let`, so this restriction is reachable only via hand-built
    /// IR (tests). It is sound at this stage.
    ///
    /// **Deadline: step 10.** The effect-optimization spec's §2 purity
    /// predicate (see `effect-optimization-spec.md`) classifies a much
    /// richer subset as pure — pure `App`, `Case` with all-pure arms, `If`
    /// with both-pure branches, nested `Let`, etc. By the time step 10
    /// (Bind→Let promotion) lands, `Let.value` will routinely be one of
    /// those shapes, and this restriction breaks. The right shape then is
    /// a separate `lower_pure_expr(&self, &MExpr) -> CExpr` defined only
    /// on the pure subset — it returns a direct CExpr value with no
    /// `_ReturnK` threading. `lower_let` becomes
    /// `CExpr::Let(var, lower_pure_expr(value), lower_expr(body))`. That
    /// function is structurally different from `lower_expr` (no K
    /// threading), so it deserves to live separately rather than being
    /// merged in. Don't build it speculatively here — wait for step 10's
    /// optimizer output to drive the cases.
    fn lower_let(&mut self, var: &MVar, value: &MExpr, body: &MExpr, ctx: &LowerCtx) -> CExpr {
        let value_ce = match value {
            MExpr::Pure(atom) => self.lower_atom(atom, ctx),
            other => panic!(
                "lower_let: Let value must be Pure(atom) until step 10's Bind→Let promotion lands \
                 and brings a `lower_pure_expr` for the broader pure subset; got {:?}",
                std::mem::discriminant(other)
            ),
        };
        let body_ctx = ctx.with_local(var.name.clone());
        let body_ce = self.lower_expr(body, &body_ctx);
        CExpr::Let(core_var(&var.name), Box::new(value_ce), Box::new(body_ce))
    }

    /// Lower an `Atom::Lambda` — closure value at construction.
    ///
    /// Uniform calling convention: every lambda receives `_Evidence` and
    /// `_ReturnK` after its user params, regardless of whether the body
    /// performs effects. The body is STUBBED in 7b (delegates to
    /// `lower_body_stub`); sub-step 7c replaces the body with real MExpr
    /// lowering.
    ///
    /// Lambda body lowers under a fresh K context: the lambda's `_ReturnK`
    /// param shadows whatever the outer scope's ambient K was. We save the
    /// outer state, reset to the entry-fn defaults (current K = `_ReturnK`,
    /// fresh K counter starts back at zero so nested lambdas get stable
    /// names), lower the body, then restore.
    pub(super) fn lower_lambda_atom(
        &mut self,
        params: &[Pat],
        body: &MExpr,
        enclosing: &LowerCtx,
    ) -> CExpr {
        // Non-Var patterns in lambda params (e.g. `fun (Currency a) -> show a`)
        // need a case-on-tuple-of-args destructure inside the body — same
        // shape as multi-clause fun bindings. `lower_param_names` collapses
        // every non-Var pattern to a fresh `_Arg{i}`, so without this wrap
        // the body's references to the pattern's sub-vars (`a` here) would
        // be unbound at runtime.
        let has_non_var_pat = params.iter().any(|p| !matches!(p, Pat::Var { .. }));
        let mut param_vars: Vec<String> = if has_non_var_pat {
            (0..params.len()).map(|i| format!("_Arg{}", i)).collect()
        } else {
            lower_param_names(params)
        };
        param_vars.push(EVIDENCE_VAR.to_string());
        param_vars.push(RETURN_K_VAR.to_string());
        let snap = self.snapshot_counters();
        self.reset_counters();
        // Lambda body lowers under fresh return_k/evidence (the lambda's own
        // params shadow the enclosing _ReturnK / _Evidence), but inherits
        // arm_k from the enclosing context. A `resume` inside a lambda
        // defined inside a handler arm body must call the *enclosing arm's*
        // K via lexical closure capture — losing arm_k here silently
        // miscompiles into a `resume` that calls the lambda's own _ReturnK.
        let body_ctx = LowerCtx {
            return_k: RETURN_K_VAR.to_string(),
            evidence: EVIDENCE_VAR.to_string(),
            arm_k: enclosing.arm_k.clone(),
            abort_marker: enclosing.abort_marker.clone(),
            finally_block: enclosing.finally_block.clone(),
            locals: enclosing.locals.clone(),
        }
        .with_param_locals(params);
        let body_ce_inner = self.lower_expr(body, &body_ctx);
        let body_ce = if has_non_var_pat {
            let scrut = CExpr::Tuple(
                (0..params.len())
                    .map(|i| CExpr::Var(format!("_Arg{}", i)))
                    .collect(),
            );
            let pat = CPat::Tuple(params.iter().map(|p| self.lower_pat(p)).collect());
            CExpr::Case(
                Box::new(scrut),
                vec![CArm {
                    pat,
                    guard: None,
                    body: body_ce_inner,
                }],
            )
        } else {
            body_ce_inner
        };
        self.restore_counters(snap);
        CExpr::Fun(param_vars, Box::new(body_ce))
    }
}
