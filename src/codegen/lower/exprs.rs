//! Monadic-IR → Core Erlang expression lowering.
//!
//! Sub-step 7b: `Atom → CExpr` lowering for every variant of the `Atom`
//! enum from `monadic-ir-spec.md`. Structural `MExpr` variants are still
//! stubbed; they arrive in sub-step 7c.

use crate::ast::Pat;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::monadic::ir::{Atom, BindMode, MExpr, MVar};

use super::exprs_edge::binop_atoms;
use super::pats::lower_param_names;
use super::util::{
    ABORT_TAG, VALUE_RESULT_TAG, core_var, marked_control_pattern, marked_control_tuple,
    marked_control_var_pattern,
};
use super::{LowerCtx, Lowerer};

// Name of the function-entry return-continuation variable. Every emitted
// CFunDef binds this as its trailing parameter (after `_Evidence`); the body
// applies it to the function's final value. Kept in sync with `decls.rs`.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";
/// Function-entry evidence-vector parameter name. Kept in sync with
/// `decls.rs`'s [`EVIDENCE_VAR`].
pub(super) const EVIDENCE_VAR: &str = "_Evidence";
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
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => self.lower_bind(var, value, body, *mode, ctx),
            MExpr::Let { var, value, body } => self.lower_let(var, value, body, ctx),
            MExpr::Ensure { body, cleanup } => self.lower_ensure(body, cleanup, ctx),
            MExpr::Case {
                scrutinee, arms, ..
            } => self.lower_case(scrutinee, arms, ctx),
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(cond, then_branch, else_branch, ctx),
            MExpr::App { head, args, source } => self.lower_app(head, args, *source, ctx),
            MExpr::Yield { op, args, .. } => self.lower_yield(op, args, ctx),
            MExpr::With { handler, body, .. } => self.lower_with(handler, body, ctx),
            MExpr::Resume { value, .. } => self.lower_resume(value, ctx),
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self.lower_field_access(
                record,
                field,
                record_name.as_deref(),
                anon_fields.as_deref(),
                ctx,
            ),
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                anon_fields,
                ..
            } => self.lower_record_update(
                record,
                fields,
                record_name.as_deref(),
                anon_fields.as_deref(),
                ctx,
            ),
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => self.lower_dict_method_access(dict, *method_index, ctx),
            MExpr::ForeignCall {
                module, func, args, ..
            } => self.lower_foreign_call(module, func, args, ctx),
            MExpr::BinOp {
                op,
                left,
                right,
                source,
            } => self.lower_binop(op, left, right, *source, ctx),
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
        //
        // Element 2 is a tuple of `{EffectAtom, OpTuple}` pairs ordered
        // alphabetically by effect — same shape as `build_handler_value_tuple`
        // in atom.rs. See its doc comment for the runtime layout.
        let ops_by_effect = self.build_ops_by_effect_tuple(arms, ctx);
        let return_value = return_clause
            .map(|arm| self.build_handler_value_return_lambda(arm, ctx))
            .unwrap_or_else(|| CExpr::Lit(CLit::Atom("unit".to_string())));
        let handler_value = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("__saga_handler_value".to_string())),
            ops_by_effect,
            return_value,
        ]);
        self.apply_current_k(handler_value, ctx)
    }

    fn lower_ensure(&mut self, body: &MExpr, cleanup: &MExpr, ctx: &LowerCtx) -> CExpr {
        let ensure_result = self.fresh_helper_name();
        let ensure_k = self.fresh_helper_name();
        let body_ctx = ctx.with_return_k(ensure_k.clone());
        let body_ce = self.lower_expr(body, &body_ctx);
        let forward_result = self.apply_current_k(CExpr::Var(ensure_result.clone()), ctx);
        CExpr::Let(
            ensure_k,
            Box::new(CExpr::Fun(
                vec![ensure_result],
                Box::new(self.sequence_finally_then(cleanup, ctx, forward_result)),
            )),
            Box::new(body_ce),
        )
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
        let resume_call = CExpr::Apply(Box::new(CExpr::Var(k.clone())), vec![v]);

        let continue_with_value = |this: &mut Self, value: CExpr, ctx: &LowerCtx| {
            if let Some(finally_expr) = ctx.finally_block.clone() {
                this.sequence_finally_then(&finally_expr, ctx, this.apply_current_k(value, ctx))
            } else {
                this.apply_current_k(value, ctx)
            }
        };
        let cleanup_then_value = |this: &mut Self, value: CExpr, ctx: &LowerCtx| {
            if let Some(finally_expr) = ctx.finally_block.clone() {
                this.sequence_finally_then(&finally_expr, ctx, value)
            } else {
                value
            }
        };

        if let Some(marker) = &ctx.abort_marker {
            let raw_resumed = self.fresh_helper_name();
            let abort_value = self.fresh_helper_name();
            let other_marker = self.fresh_helper_name();
            let other_abort_value = self.fresh_helper_name();
            let value_result = self.fresh_helper_name();
            let other_value_marker = self.fresh_helper_name();
            let other_value = self.fresh_helper_name();
            CExpr::Let(
                raw_resumed.clone(),
                Box::new(resume_call),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(raw_resumed)),
                    vec![
                        CArm {
                            pat: marked_control_pattern(
                                ABORT_TAG,
                                CPat::Lit(CLit::Atom(marker.clone())),
                                abort_value.clone(),
                            ),
                            guard: None,
                            body: continue_with_value(self, CExpr::Var(abort_value), ctx),
                        },
                        CArm {
                            pat: marked_control_pattern(
                                VALUE_RESULT_TAG,
                                CPat::Lit(CLit::Atom(marker.clone())),
                                value_result.clone(),
                            ),
                            guard: None,
                            body: continue_with_value(self, CExpr::Var(value_result.clone()), ctx),
                        },
                        CArm {
                            pat: marked_control_var_pattern(
                                VALUE_RESULT_TAG,
                                other_value_marker.clone(),
                                other_value.clone(),
                            ),
                            guard: None,
                            body: marked_control_tuple(
                                VALUE_RESULT_TAG,
                                CExpr::Var(other_value_marker),
                                CExpr::Var(other_value),
                            ),
                        },
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom(VALUE_RESULT_TAG.to_string())),
                                CPat::Var(value_result.clone()),
                            ]),
                            guard: None,
                            body: continue_with_value(self, CExpr::Var(value_result), ctx),
                        },
                        CArm {
                            pat: marked_control_var_pattern(
                                ABORT_TAG,
                                other_marker.clone(),
                                other_abort_value.clone(),
                            ),
                            guard: None,
                            body: if ctx.finally_block.is_some() {
                                cleanup_then_value(
                                    self,
                                    marked_control_tuple(
                                        ABORT_TAG,
                                        CExpr::Var(other_marker),
                                        CExpr::Var(other_abort_value),
                                    ),
                                    ctx,
                                )
                            } else {
                                marked_control_tuple(
                                    ABORT_TAG,
                                    CExpr::Var(other_marker),
                                    CExpr::Var(other_abort_value),
                                )
                            },
                        },
                        CArm {
                            pat: CPat::Var("_ResumeValue".to_string()),
                            guard: None,
                            body: continue_with_value(
                                self,
                                CExpr::Var("_ResumeValue".to_string()),
                                ctx,
                            ),
                        },
                    ],
                )),
            )
        } else {
            let resumed = self.fresh_helper_name();
            let value_result = self.fresh_helper_name();
            let other_value_marker = self.fresh_helper_name();
            let other_value = self.fresh_helper_name();
            CExpr::Let(
                resumed.clone(),
                Box::new(resume_call),
                Box::new(CExpr::Case(
                    Box::new(CExpr::Var(resumed)),
                    vec![
                        CArm {
                            pat: marked_control_var_pattern(
                                VALUE_RESULT_TAG,
                                other_value_marker.clone(),
                                other_value.clone(),
                            ),
                            guard: None,
                            body: marked_control_tuple(
                                VALUE_RESULT_TAG,
                                CExpr::Var(other_value_marker),
                                CExpr::Var(other_value),
                            ),
                        },
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom(VALUE_RESULT_TAG.to_string())),
                                CPat::Var(value_result.clone()),
                            ]),
                            guard: None,
                            body: continue_with_value(self, CExpr::Var(value_result), ctx),
                        },
                        CArm {
                            pat: CPat::Var("_ResumeValue".to_string()),
                            guard: None,
                            body: continue_with_value(
                                self,
                                CExpr::Var("_ResumeValue".to_string()),
                                ctx,
                            ),
                        },
                    ],
                )),
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
    fn lower_bind(
        &mut self,
        var: &MVar,
        value: &MExpr,
        body: &MExpr,
        mode: BindMode,
        ctx: &LowerCtx,
    ) -> CExpr {
        // A perform already receives the captured continuation for the
        // surrounding expression. If a stale/synthetic IR node marks a Yield as
        // value-position, keep the semantically correct sequencing path.
        if matches!(mode, BindMode::ValuePosition) && !matches!(value, MExpr::Yield { .. }) {
            return self.lower_value_position_bind(var, value, body, ctx);
        }
        let body_ctx = ctx.with_local(var.name.clone());
        let mut body_ce = self.lower_expr(body, &body_ctx);
        body_ce = self.bubble_abort_to_k(body_ce, &ctx.return_k);
        let bound_var = core_var(&var.name);
        let k_name = self.fresh_k_name();
        let k_arg = self.fresh_helper_name();
        let mut k_arms = self.apply_marked_control_arms_to_k(&ctx.return_k);
        k_arms.push(CArm {
            pat: CPat::Var("_BindArg".to_string()),
            guard: None,
            body: CExpr::Let(
                bound_var,
                Box::new(CExpr::Var("_BindArg".to_string())),
                Box::new(body_ce),
            ),
        });
        let k_body = CExpr::Case(Box::new(CExpr::Var(k_arg.clone())), k_arms);
        let k_fun = CExpr::Fun(vec![k_arg], Box::new(k_body));
        let value_ce = self.lower_expr(value, &ctx.with_return_k(k_name.clone()));
        let bind_ce = CExpr::Let(k_name, Box::new(k_fun), Box::new(value_ce));
        self.bubble_abort_to_k(bind_ce, &ctx.return_k)
    }

    fn bubble_abort_to_k(&mut self, body_ce: CExpr, return_k: &str) -> CExpr {
        let result = self.fresh_helper_name();
        let mut arms = self.apply_marked_control_arms_to_k(return_k);
        arms.push(CArm {
            pat: CPat::Var("_BindValue".to_string()),
            guard: None,
            body: CExpr::Var("_BindValue".to_string()),
        });
        CExpr::Let(
            result.clone(),
            Box::new(body_ce),
            Box::new(CExpr::Case(Box::new(CExpr::Var(result)), arms)),
        )
    }

    fn lower_value_position_bind(
        &mut self,
        var: &MVar,
        value: &MExpr,
        body: &MExpr,
        ctx: &LowerCtx,
    ) -> CExpr {
        let local_k = self.fresh_k_name();
        let raw_result = self.fresh_helper_name();
        // Two `__saga_value_result` shapes intentionally coexist:
        //
        //   {__saga_value_result, V}
        //     Local-only signal for this value-position bind. It must be
        //     consumed by the immediately following case below.
        //
        //   {__saga_value_result, Marker, V}
        //     Marked control result that routes to a specific handler prompt.
        //     It must bubble like an abort tuple until that marker catches it.
        //
        // Core Erlang tuple arity keeps the two protocols distinct.
        let success_tag = CLit::Atom(VALUE_RESULT_TAG.to_string());
        let bound_var = core_var(&var.name);
        let local_k_fun = CExpr::Fun(
            vec![bound_var.clone()],
            Box::new(CExpr::Tuple(vec![
                CExpr::Lit(success_tag.clone()),
                CExpr::Var(bound_var.clone()),
            ])),
        );
        let value_ctx = ctx
            .with_return_k(local_k.clone())
            .with_preserve_abort_marker(true);
        let value_ce = self.lower_expr(value, &value_ctx);
        let body_ctx = ctx.with_local(var.name.clone());
        let body_ce = self.lower_expr(body, &body_ctx);
        let raw_value = self.fresh_helper_name();
        let mut value_arms = vec![CArm {
            pat: CPat::Tuple(vec![CPat::Lit(success_tag), CPat::Var(bound_var.clone())]),
            guard: None,
            body: body_ce.clone(),
        }];
        value_arms.extend(self.propagate_marked_control_arms());
        value_arms.push(CArm {
            pat: CPat::Var(raw_value.clone()),
            guard: None,
            body: CExpr::Let(
                bound_var,
                Box::new(CExpr::Var(raw_value)),
                Box::new(body_ce),
            ),
        });
        let value_bind = CExpr::Let(
            local_k,
            Box::new(local_k_fun),
            Box::new(CExpr::Let(
                raw_result.clone(),
                Box::new(value_ce),
                Box::new(CExpr::Case(Box::new(CExpr::Var(raw_result)), value_arms)),
            )),
        );
        self.bubble_abort_to_k(value_bind, &ctx.return_k)
    }

    /// Lower `Let { var, value, body }` — a non-yielding binder
    /// produced by effect optimization's Bind→Let promotion rewrite.
    fn lower_let(&mut self, var: &MVar, value: &MExpr, body: &MExpr, ctx: &LowerCtx) -> CExpr {
        let value_ce = self.lower_pure_expr(value, ctx);
        let body_ctx = ctx.with_local(var.name.clone());
        let body_ce = self.lower_expr(body, &body_ctx);
        CExpr::Let(core_var(&var.name), Box::new(value_ce), Box::new(body_ce))
    }

    /// Lower the non-yielding subset accepted by Bind→Let promotion to a
    /// Core expression that returns its value directly, rather than applying
    /// the ambient continuation.
    fn lower_pure_expr(&mut self, expr: &MExpr, ctx: &LowerCtx) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_atom(atom, ctx),
            MExpr::Let { var, value, body } => {
                let value_ce = self.lower_pure_expr(value, ctx);
                let body_ctx = ctx.with_local(var.name.clone());
                let body_ce = self.lower_pure_expr(body, &body_ctx);
                CExpr::Let(core_var(&var.name), Box::new(value_ce), Box::new(body_ce))
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                let scrutinee = self.lower_atom(scrutinee, ctx);
                let arms = arms
                    .iter()
                    .map(|arm| self.lower_pure_arm(arm, ctx))
                    .collect();
                CExpr::Case(Box::new(scrutinee), arms)
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond = self.lower_atom(cond, ctx);
                let then_branch = self.lower_pure_expr(then_branch, ctx);
                let else_branch = self.lower_pure_expr(else_branch, ctx);
                CExpr::Case(
                    Box::new(cond),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body: then_branch,
                        },
                        CArm {
                            pat: CPat::Lit(CLit::Atom("false".to_string())),
                            guard: None,
                            body: else_branch,
                        },
                    ],
                )
            }
            MExpr::BinOp {
                op, left, right, ..
            } => {
                let l = self.lower_atom(left, ctx);
                let r = self.lower_atom(right, ctx);
                binop_atoms(op, l, r)
            }
            MExpr::UnaryMinus { value, .. } => {
                let v = self.lower_atom(value, ctx);
                CExpr::Call(
                    "erlang".to_string(),
                    "-".to_string(),
                    vec![CExpr::Lit(CLit::Int(0)), v],
                )
            }
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => {
                let d = self.lower_atom(dict, ctx);
                CExpr::Call(
                    "erlang".to_string(),
                    "element".to_string(),
                    vec![CExpr::Lit(CLit::Int(*method_index as i64 + 1)), d],
                )
            }
            MExpr::App { .. }
            | MExpr::FieldAccess { .. }
            | MExpr::RecordUpdate { .. }
            | MExpr::BitString { .. } => self.lower_pure_expr_via_identity_k(expr, ctx),
            other => panic!(
                "lower_pure_expr: MExpr variant is not in Bind→Let's pure subset: {:?}",
                std::mem::discriminant(other)
            ),
        }
    }

    fn lower_pure_arm(&mut self, arm: &crate::codegen::monadic::ir::MArm, ctx: &LowerCtx) -> CArm {
        let pat = self.lower_pat(&arm.pattern);
        let arm_ctx = ctx.with_pat_locals(&arm.pattern);
        let guard = arm.guard.as_ref().map(|g| self.lower_guard(g, &arm_ctx));
        let body = self.lower_pure_expr(&arm.body, &arm_ctx);
        CArm { pat, guard, body }
    }

    /// Bridge pure uniform-CPS calls back to direct value position. Pure Saga
    /// functions still have the uniform `(args..., Evidence, ReturnK)` ABI, so
    /// value-position lowering supplies an identity K and uses the apply result.
    fn lower_pure_expr_via_identity_k(&mut self, expr: &MExpr, ctx: &LowerCtx) -> CExpr {
        let k_name = self.fresh_helper_name();
        let k_arg = self.fresh_helper_name();
        let id_k = CExpr::Fun(vec![k_arg.clone()], Box::new(CExpr::Var(k_arg)));
        let value_ctx = ctx.with_return_k(k_name.clone());
        CExpr::Let(
            k_name,
            Box::new(id_k),
            Box::new(self.lower_expr(expr, &value_ctx)),
        )
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
            preserve_abort_marker: enclosing.preserve_abort_marker,
            result_delimiter: enclosing.result_delimiter.clone(),
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
