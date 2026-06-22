use crate::ast::{Expr, ExprKind, Pat, Stmt};
use crate::codegen::cerl::{CExpr};
use crate::token::Span;
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;

impl<'a> Lowerer<'a> {
    /// Lower an expression in an explicit lowering mode.
    ///
    /// This is currently a thin compatibility layer over the existing ambient
    /// continuation machinery. The goal is to migrate call sites toward
    /// explicit value/tail intent before simplifying the internals further.
    pub(crate) fn lower_expr_in(&mut self, expr: &Expr, mode: LowerMode) -> CExpr {
        match mode {
            LowerMode::Value => self.lower_expr_with_installed_return_k(expr, None),
            LowerMode::Tail(k) => self.lower_expr_tail_compat(expr, k),
        }
    }


    /// Lower a block in an explicit lowering mode.
    pub(crate) fn lower_block_in(&mut self, stmts: &[Stmt], mode: LowerMode) -> CExpr {
        match mode {
            LowerMode::Value => self.lower_expr_in(
                &Expr::synth(
                    Span { start: 0, end: 0 },
                    ExprKind::Block {
                        stmts: stmts
                            .iter()
                            .cloned()
                            .map(crate::ast::Annotated::bare)
                            .collect(),
                        dangling_trivia: vec![],
                    },
                ),
                LowerMode::Value,
            ),
            LowerMode::Tail(k) => {
                let k_var = self.fresh();
                let body = self.lower_block_with_k(stmts, &k_var);
                CExpr::Let(k_var, Box::new(k), Box::new(body))
            }
        }
    }


    /// Lower an expression as a value-producing subexpression.
    ///
    /// This temporarily clears the ambient return continuation so nested
    /// blocks used in expression position don't tail-call the enclosing
    /// `_ReturnK` before the surrounding `let`/statement has a chance to
    /// continue.
    pub(crate) fn lower_expr_value(&mut self, expr: &Expr) -> CExpr {
        self.lower_expr_in(expr, LowerMode::Value)
    }


    /// Lower an expression in terminal position with an explicit continuation.
    pub(crate) fn lower_expr_tail(&mut self, expr: &Expr, k: CExpr) -> CExpr {
        self.lower_expr_in(expr, LowerMode::Tail(k))
    }


    pub(crate) fn lower_expr_with_call_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        if self.expr_is_effectful_call(expr) {
            if let Some((module, func_name, head, args)) = crate::codegen::lower::util::collect_qualified_call(expr)
                && let Some(call) = self.lower_qualified_call(crate::codegen::lower::QualifiedCallSite {
                    app_id: expr.id,
                    module,
                    func_name,
                    head,
                    args: &args,
                    return_k: return_k.clone(),
                    call_span: Some(&expr.span),
                })
            {
                return call;
            }
            if let Some((func_name, head_expr, args)) = collect_fun_call(expr) {
                if let Some(call) = self.lower_resolved_fun_call(crate::codegen::lower::ResolvedCallSite {
                    app_id: expr.id,
                    lookup_name: func_name,
                    emit_name: func_name,
                    head: head_expr,
                    args: &args,
                    return_k: return_k.clone(),
                    call_span: Some(&expr.span),
                    fallback_erlang_module: None,
                }) {
                    return call;
                }
                if let Some(call) =
                    self.lower_effectful_var_call(expr.id, func_name, &args, return_k.clone())
                {
                    return call;
                }
            }
            if let Some((dict, trait_name, method_index, args)) =
                crate::codegen::lower::util::collect_dict_method_call(expr)
                && let Some(call) = self.lower_dict_method_call(
                    expr.id,
                    dict,
                    trait_name,
                    method_index,
                    &args,
                    return_k.clone(),
                )
            {
                return call;
            }
            if let Some((lambda, args)) = crate::codegen::lower::util::collect_lambda_head_call(expr)
                && let Some(call) = self.lower_lambda_head_call(expr.id, lambda, &args, return_k.clone())
            {
                return call;
            }
            if let Some((head, args)) =
                crate::codegen::lower::util::collect_field_access_head_call(expr)
                && let Some(call) = self.lower_field_access_head_call(expr.id, head, &args, return_k)
            {
                return call;
            }
            self.panic_unhandled_effectful_app(expr, None);
        }

        self.lower_expr(expr)
    }


    /// Lower an expression with an explicitly installed return continuation.
    ///
    /// Block expressions route through block lowering directly so the return
    /// continuation applies at the terminal statement instead of through an
    /// extra ambient wrapper.
    pub(crate) fn lower_expr_with_installed_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        match &expr.kind {
            ExprKind::Block { stmts, .. } => {
                let stmts: Vec<_> = stmts.iter().map(|a| a.node.clone()).collect();
                self.lower_block_with_return_k(&stmts, return_k)
            }
            ExprKind::With { expr, handler, .. } if return_k.is_some() => {
                self.lower_with_inherited_return_k(expr, handler, return_k)
            }
            _ => {
                if return_k.is_some() {
                    self.lower_terminal_effectful_expr_with_return_k(expr, return_k)
                } else {
                    self.lower_expr(expr)
                }
            }
        }
    }


    /// Compatibility implementation for explicit tail-mode lowering.
    ///
    /// We currently preserve the old branch-aware K-threading behavior rather
    /// than approximating tail lowering with an ambient return continuation.
    /// That old structural lowering is what correctly threads continuations
    /// through `if`, `case`, and nested blocks.
    pub(crate) fn lower_expr_tail_compat(&mut self, expr: &Expr, k: CExpr) -> CExpr {
        let k_var = self.fresh();
        let body = self.lower_expr_with_k_inner(expr, &k_var);
        CExpr::Let(k_var, Box::new(k), Box::new(body))
    }


    /// Lower a non-block expression in a context where `return_k`
    /// should govern terminal effect semantics.
    ///
    /// This centralizes the common decision tree used for effectful function
    /// bodies and lambdas:
    /// - direct effect ops receive `return_k` as their continuation
    /// - nested effectful control flow threads `return_k` through branches
    /// - direct effectful function calls receive it explicitly as `_ReturnK`
    /// - pure expressions are lowered normally and wrapped with `return_k`
    pub(crate) fn lower_terminal_effectful_expr_with_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        if let Some((head_expr, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
            let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
            self.lower_effect_call(head_expr.id, op_name, qualifier, &args_owned, return_k)
        } else if let ExprKind::With { expr, handler, .. } = &expr.kind
            && return_k.is_some()
        {
            self.lower_with_inherited_return_k(expr, handler, return_k)
        } else if self.has_nested_effectful_expr(expr) {
            let k_var = self.fresh();
            let k_ce = return_k.expect("nested terminal effectful expr requires return_k");
            let body_ce = self.lower_expr_with_k(expr, &k_var);
            CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
        } else if self.expr_is_effectful_call(expr) {
            self.lower_expr_with_call_return_k(expr, return_k)
        } else {
            let body_ce = self.lower_expr(expr);
            self.apply_return_k_with(return_k, body_ce)
        }
    }


    /// Lower the terminal expression of a block, respecting any enclosing
    /// handled-computation return continuation passed explicitly.
    ///
    /// `with` remains a delimiter here: it manages inherited return handling
    /// internally and must not be wrapped again outside.
    pub(crate) fn lower_block_terminal_expr_with_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        if return_k.is_some() {
            // Block-terminal `with` must thread the host return_k into the
            // handler's outer-K context. Routing through `lower_expr` would
            // call `lower_with` with no inherited K — silently discarding
            // the host's continuation, so any abort handler body lowers
            // without the host's CPS chain to thread into. Forward the
            // return_k explicitly.
            if let ExprKind::With {
                expr: inner,
                handler,
                ..
            } = &expr.kind
            {
                return self.lower_with_inherited_return_k(inner, handler, return_k);
            }
            return self.lower_terminal_effectful_expr_with_return_k(expr, return_k);
        }

        let val = self.lower_expr(expr);
        self.apply_return_k_with(return_k, val)
    }


    /// Build the continuation representing the rest of a block after the
    /// current statement, optionally destructuring the result through `pat`.
    pub(crate) fn lower_rest_block_k_with_return_k(
        &mut self,
        pat: Option<&Pat>,
        rest: &[Stmt],
        return_k: Option<CExpr>,
    ) -> CExpr {
        let rest_ce = self.lower_block_with_return_k(rest, return_k);
        let (k_param, rest_ce) = match pat {
            Some(p) => self.destructure_pat(p, rest_ce),
            None => (self.fresh(), rest_ce),
        };
        CExpr::Fun(vec![k_param], Box::new(rest_ce))
    }


    /// Build the continuation representing the rest of a K-threaded block after
    /// the current statement, optionally destructuring the result through `pat`.
    pub(crate) fn lower_rest_block_with_k_k(
        &mut self,
        pat: Option<&Pat>,
        rest: &[Stmt],
        k_var: &str,
    ) -> CExpr {
        let rest_ce = self.lower_block_with_k(rest, k_var);
        let (k_param, rest_ce) = match pat {
            Some(p) => self.destructure_pat(p, rest_ce),
            None => (self.fresh(), rest_ce),
        };
        CExpr::Fun(vec![k_param], Box::new(rest_ce))
    }


    /// Lower a pure/value expression, then apply the result to `k_var`.
    pub(crate) fn lower_value_to_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        let v = self.fresh();
        let ce = self.lower_expr_value(expr);
        CExpr::Let(
            v.clone(),
            Box::new(ce),
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(k_var.to_string())),
                vec![CExpr::Var(v)],
            )),
        )
    }


    /// Lower an expression in a context where successful completion should
    /// flow to the explicit continuation `k_var`.
    pub(crate) fn lower_terminal_effectful_expr_to_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        if let Some((head_expr, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
            let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
            self.lower_effect_call(
                head_expr.id,
                op_name,
                qualifier,
                &args_owned,
                Some(CExpr::Var(k_var.to_string())),
            )
        } else if self.expr_is_effectful_call(expr) {
            self.lower_expr_with_call_return_k(expr, Some(CExpr::Var(k_var.to_string())))
        } else if self.has_nested_effectful_expr(expr)
            || matches!(expr.kind, ExprKind::Block { .. })
        {
            self.lower_expr_with_k_inner(expr, k_var)
        } else {
            self.lower_value_to_k(expr, k_var)
        }
    }

}
