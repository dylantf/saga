//! `Case`/`If` lowering for the monadic-IR → Core Erlang pipeline.

use crate::ast::Pat;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::monadic::ir::{Atom, MArm, MExpr};

use super::exprs_edge::binop_atoms;
use super::util::core_var;
use super::{LowerCtx, Lowerer};

impl<'ctx> Lowerer<'ctx> {
    /// Lower `Case { scrutinee, arms }`. By ANF the scrutinee is atomic, so
    /// we lower it inline. Each arm body lowers under the *same* ambient K
    /// — branches share the enclosing continuation, exactly what makes
    /// `case` a tail form rather than a value form.
    ///
    /// Guard semantics, confirmed via typechecker (`infer.rs::check_guard`):
    /// effect calls are forbidden in guards, so a guard MExpr is structurally
    /// pure (no `Yield`, no `Bind`, no `With`, no `Resume`). Pure guards lower
    /// into a `CExpr` placed directly in `CArm.guard`; see
    /// [`lower_guard`](Self::lower_guard) for the supported shape.
    pub(super) fn lower_case(&mut self, scrutinee: &Atom, arms: &[MArm], ctx: &LowerCtx) -> CExpr {
        // Complex guards (function calls, `Yield`, anything not legal in a
        // Core Erlang guard) cannot be emitted as `case … when …`. Emit a
        // right-associated chain of one-arm cases where each complex guard
        // is scrutinised at the value level — mirrors the old lowerer's
        // [`lower_case_expr_chain`] in `lower/exprs.rs:409`.
        let needs_chain = arms
            .iter()
            .any(|a| a.guard.as_ref().is_some_and(|g| !guard_safe(g)));
        if needs_chain {
            return self.lower_case_chain(scrutinee, arms, ctx);
        }

        let scrut_ce = self.lower_atom(scrutinee, ctx);
        let mut carms: Vec<CArm> = arms.iter().map(|arm| self.lower_arm(arm, ctx)).collect();
        // erlc's `bs_start_match3` consistency check requires a wildcard
        // fallthrough on bitstring case-expressions even when the typechecker
        // already proved exhaustiveness. The old lowerer adds one
        // unconditionally when no Var/Wildcard arm is present (see
        // [`lower/exprs.rs:359-368`]); the new path mirrors that.
        let has_total_catchall = arms.iter().any(|arm| {
            arm.guard.is_none() && matches!(&arm.pattern, Pat::Wildcard { .. } | Pat::Var { .. })
        });
        if !has_total_catchall {
            carms.push(CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: self.case_clause_error(),
            });
        }
        CExpr::Case(Box::new(scrut_ce), carms)
    }

    /// Emit a case as a right-associated chain of one-arm cases, with the
    /// fallthrough of each step thunked into a `fun () -> rest` and applied
    /// when the arm doesn't match. Complex (non-guard-safe) guards are
    /// CPS-evaluated outside the inner `case` and scrutinised on their
    /// boolean value.
    fn lower_case_chain(&mut self, scrutinee: &Atom, arms: &[MArm], ctx: &LowerCtx) -> CExpr {
        let scrut_ce = self.lower_atom(scrutinee, ctx);
        let scrut_var = self.fresh_helper_name();

        let mut rest: CExpr = self.case_clause_error();
        for arm in arms.iter().rev() {
            let rest_var = self.fresh_helper_name();
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            let pat = self.lower_pat(&arm.pattern);
            let is_catchall = matches!(&arm.pattern, Pat::Wildcard { .. } | Pat::Var { .. });

            let current = match arm.guard.as_ref() {
                None => {
                    let body_ce = self.lower_expr(&arm.body, ctx);
                    if is_catchall {
                        self.bind_catchall_pattern(&scrut_var, &arm.pattern, body_ce)
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.clone())),
                            vec![
                                CArm {
                                    pat,
                                    guard: None,
                                    body: body_ce,
                                },
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: rest_ref(),
                                },
                            ],
                        )
                    }
                }
                Some(guard) if guard_safe(guard) => {
                    let g = self.lower_guard(guard, ctx);
                    let body_ce = self.lower_expr(&arm.body, ctx);
                    CExpr::Case(
                        Box::new(CExpr::Var(scrut_var.clone())),
                        vec![
                            CArm {
                                pat,
                                guard: Some(g),
                                body: body_ce,
                            },
                            CArm {
                                pat: CPat::Wildcard,
                                guard: None,
                                body: rest_ref(),
                            },
                        ],
                    )
                }
                Some(guard) => {
                    // CPS-evaluate the guard: bind its value through a fresh
                    // K, then scrutinise the bound value on 'true'/_.
                    let body_ce = self.lower_expr(&arm.body, ctx);
                    let guard_val = self.fresh_helper_name();
                    let inner_case = CExpr::Case(
                        Box::new(CExpr::Var(guard_val.clone())),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: body_ce,
                            },
                            CArm {
                                pat: CPat::Wildcard,
                                guard: None,
                                body: rest_ref(),
                            },
                        ],
                    );
                    let k_inner = CExpr::Fun(vec![guard_val], Box::new(inner_case));
                    let k_name = self.fresh_k_name();
                    let guard_ce = self.lower_expr(guard, &ctx.with_return_k(k_name.clone()));
                    let guarded_body = CExpr::Let(k_name, Box::new(k_inner), Box::new(guard_ce));
                    if is_catchall {
                        self.bind_catchall_pattern(&scrut_var, &arm.pattern, guarded_body)
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.clone())),
                            vec![
                                CArm {
                                    pat,
                                    guard: None,
                                    body: guarded_body,
                                },
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: rest_ref(),
                                },
                            ],
                        )
                    }
                }
            };

            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }

        CExpr::Let(scrut_var, Box::new(scrut_ce), Box::new(rest))
    }

    /// Bind a catchall (`Wildcard` or `Var`) arm pattern directly without an
    /// enclosing `case` — the wildcard pattern matches everything, and a
    /// var pattern is bound to the scrutinee with a `let`.
    fn bind_catchall_pattern(&self, scrut_var: &str, pat: &Pat, body: CExpr) -> CExpr {
        match pat {
            Pat::Wildcard { .. } => body,
            Pat::Var { name, .. } => CExpr::Let(
                core_var(name),
                Box::new(CExpr::Var(scrut_var.to_string())),
                Box::new(body),
            ),
            _ => unreachable!("bind_catchall_pattern called on non-catchall pattern"),
        }
    }

    /// Emit a Core Erlang expression that crashes with a `case_clause` error,
    /// used as the body of the synthetic wildcard fallthrough arm. The
    /// typechecker's exhaustiveness check makes this unreachable at runtime;
    /// the arm exists only to satisfy `erlc`'s bitstring-match invariant.
    fn case_clause_error(&self) -> CExpr {
        CExpr::Call(
            "erlang".to_string(),
            "error".to_string(),
            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
        )
    }

    /// Lower a single MArm into a `CArm`. Shared between `Case` and `Receive`.
    pub(super) fn lower_arm(&mut self, arm: &MArm, ctx: &LowerCtx) -> CArm {
        let pat = self.lower_pat(&arm.pattern);
        let guard = arm.guard.as_ref().map(|g| self.lower_guard(g, ctx));
        let body = self.lower_expr(&arm.body, ctx);
        CArm { pat, guard, body }
    }

    /// Lower a guard MExpr into a `CExpr` suitable for a Core Erlang
    /// `case`/`receive` arm guard position.
    ///
    /// Guards are statically guaranteed pure by the typechecker — see
    /// `src/typechecker/infer.rs::check_guard`, which forbids effect calls.
    /// The MExpr we receive is therefore structurally a subset: `Pure(atom)`,
    /// `BinOp` of atoms, `UnaryMinus` of atom, or `ForeignCall` of a
    /// guard-safe BIF over atoms. Other shapes (Case, If, App, FieldAccess,
    /// RecordUpdate, DictMethodAccess, BitString) are syntactically illegal
    /// in Core Erlang guards anyway — we panic with a clear message rather
    /// than emit invalid CEL.
    pub(super) fn lower_guard(&mut self, guard: &MExpr, ctx: &LowerCtx) -> CExpr {
        match guard {
            MExpr::Pure(atom) => self.lower_atom(atom, ctx),
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
            MExpr::ForeignCall {
                module, func, args, ..
            } => CExpr::Call(
                module.clone(),
                func.clone(),
                args.iter().map(|a| self.lower_atom(a, ctx)).collect(),
            ),
            // ANF atomizes sub-expressions in guards too (e.g. `n % 15 == 0`
            // becomes `let v0 = n % 15 in v0 == 0`), and the translator
            // emits a `Bind` for that let. Core Erlang permits `let` in
            // guard position as long as both the bound value and the body
            // are themselves guard expressions, so we recurse into both
            // sides under `lower_guard` and rebuild as a `CExpr::Let`.
            // `Let` (post-Bind→Let promotion) gets the same treatment.
            MExpr::Bind { var, value, body } | MExpr::Let { var, value, body } => {
                let val_ce = self.lower_guard(value, ctx);
                let body_ce = self.lower_guard(body, ctx);
                CExpr::Let(core_var(&var.name), Box::new(val_ce), Box::new(body_ce))
            }
            other => panic!(
                "lower_guard: guard MExpr variant not legal in Core Erlang guard position: {:?}",
                std::mem::discriminant(other)
            ),
        }
    }

    /// Lower `If { cond, then, else }` to a Core Erlang `case` over the
    /// boolean condition. Both arms lower under the same ambient K — same
    /// shape rule as `Case` arms.
    pub(super) fn lower_if(
        &mut self,
        cond: &Atom,
        then_branch: &MExpr,
        else_branch: &MExpr,
        ctx: &LowerCtx,
    ) -> CExpr {
        let cond_ce = self.lower_atom(cond, ctx);
        let then_ce = self.lower_expr(then_branch, ctx);
        let else_ce = self.lower_expr(else_branch, ctx);
        CExpr::Case(
            Box::new(cond_ce),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("true".to_string())),
                    guard: None,
                    body: then_ce,
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("false".to_string())),
                    guard: None,
                    body: else_ce,
                },
            ],
        )
    }
}

/// Whether `g` is structurally legal in a Core Erlang `case` arm guard.
/// Matches the subset accepted by [`Lowerer::lower_guard`]: `Pure`, `BinOp`,
/// `UnaryMinus`, guard-safe `ForeignCall` (BIFs), and `Bind`/`Let` whose
/// value and body are themselves guard-safe. `App`, `Yield`, etc. require
/// the case-chain fallback.
fn guard_safe(g: &MExpr) -> bool {
    match g {
        MExpr::Pure(_) | MExpr::BinOp { .. } | MExpr::UnaryMinus { .. } => true,
        MExpr::ForeignCall { .. } => true,
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            guard_safe(value) && guard_safe(body)
        }
        _ => false,
    }
}
