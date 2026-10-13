use crate::ast::{Expr, ExprKind};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::*;

impl<'a> Lowerer<'a> {
    /// The one tail lowering. With `k`, the value of `expr` is passed to
    /// that continuation; without, it is returned.
    ///
    /// The continuation goes to whatever performs: an operation or an
    /// effectful call takes it as its own, a `with` inherits it, and `if`,
    /// `case`, blocks, `do` and `receive` hand it to their branches. Any
    /// other expression is a value (`lower_expr`), to which `k` is applied.
    /// `lower_expr` sends the branching forms back here with no
    /// continuation, so there is one implementation of each.
    pub(crate) fn lower_tail(&mut self, expr: &Expr, k: Option<CExpr>) -> CExpr {
        match &expr.kind {
            ExprKind::Block { stmts, .. } => self.with_continuation_var(k, |this, k| {
                let stmts: Vec<_> = stmts.iter().map(|a| a.node.clone()).collect();
                this.lower_block(&stmts, k)
            }),
            ExprKind::With {
                expr: inner,
                handler,
            } => self.with_continuation_var(k, |this, k| {
                this.lower_with_inherited_return_k(inner, handler, k)
            }),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.with_continuation_var(k, |this, k| {
                let cond_var = this.fresh();
                let cond_ce = this.lower_operand(cond, "if");
                let then_ce = this.lower_tail(then_branch, k.clone());
                let else_ce = this.lower_tail(else_branch, k);
                let arm = |value: &str, body| CArm {
                    pat: CPat::Lit(CLit::Atom(value.to_string())),
                    guard: None,
                    body,
                };
                CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
                        vec![arm("true", then_ce), arm("false", else_ce)],
                    )),
                )
            }),
            ExprKind::Case {
                scrutinee, arms, ..
            } => self.with_continuation_var(k, |this, k| {
                let scrut_var = this.fresh();
                let scrut_ce = this.lower_operand(scrutinee, "case");
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                let case = this.lower_case_expr(&scrut_var, &arms, k.as_ref());
                CExpr::Let(scrut_var, Box::new(scrut_ce), Box::new(case))
            }),
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => self.with_continuation_var(k, |this, k| {
                let else_arms: Vec<_> = else_arms.iter().map(|a| a.node.clone()).collect();
                this.lower_do(bindings, success, &else_arms, k.as_ref())
            }),
            ExprKind::Receive {
                arms, after_clause, ..
            } => self.with_continuation_var(k, |this, k| {
                this.lower_receive(arms, after_clause.as_ref(), k.as_ref())
            }),
            ExprKind::App { .. } => self.lower_app(expr, k),
            _ => {
                let Some(k) = k else {
                    return self.lower_expr(expr);
                };
                if let Some((name, qualifier)) = self.nullary_operation(expr) {
                    self.lower_effect_call(expr.id, name, qualifier, &[], Some(k))
                } else {
                    let value = self.lower_expr(expr);
                    self.apply_return_k_with(Some(k), value)
                }
            }
        }
    }

    /// Run `body` with the continuation as a variable, binding it first if
    /// it is not one already. A form with branches refers to it once per
    /// branch, and a form that binds names must not capture the ones the
    /// continuation refers to: it was built in the enclosing scope.
    fn with_continuation_var(
        &mut self,
        k: Option<CExpr>,
        body: impl FnOnce(&mut Self, Option<CExpr>) -> CExpr,
    ) -> CExpr {
        match k {
            Some(k) if !matches!(k, CExpr::Var(_)) => {
                let k_var = self.fresh();
                let body = body(self, Some(CExpr::Var(k_var.clone())));
                CExpr::Let(k_var, Box::new(k), Box::new(body))
            }
            k => body(self, k),
        }
    }
}
