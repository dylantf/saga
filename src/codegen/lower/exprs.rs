/// Expression-lowering helper methods on Lowerer.
/// General expression forms: case arms, constructors, binops, blocks, do-else, etc.
/// Effect system lowering is in effects.rs.
use crate::ast::{self, BinOp, BitSegment, CaseArm, Expr, ExprKind, Lit, Pat, Stmt};
use crate::codegen::cerl::{CArm, CBinSeg, CExpr, CLit, CPat};
use crate::codegen::runtime_shape::RuntimeFunctionShape;
use crate::token::Span;
use crate::typechecker::Type;
use std::collections::HashMap;

use super::pats;
use super::util::{
    arity_and_effects_from_type, binop_call, cerl_call, collect_effect_call_expr, collect_fun_call,
    core_var, lower_string_to_binary, mangle_ctor_atom, param_absorbed_effects_from_type,
    param_types_from_type, pat_binding_var,
};
use super::{EvidenceCtx, FunInfo, LowerMode, Lowerer};

/// One "hole" in a composite expression being assembled by
/// [`Lowerer::lower_with_cps_slots`]. The slot kind controls whether the
/// value comes from a pre-lowered CExpr or from CPS-chained lowering of a
/// source expression that may be effectful.
pub(super) enum CpsSlot<'e> {
    /// Already-lowered value. Bound to a plain `let`. Use for values
    /// computed by the caller (e.g. `element(idx, rec_var)`).
    Pure(CExpr),
    /// Source expression to lower. CPS-chained if effectful; otherwise
    /// lowered as a value with the optional expected type.
    Expr {
        expr: &'e Expr,
        expected: Option<Type>,
    },
}

/// Returns true if `expr` is a valid Core Erlang guard expression:
/// comparisons, arithmetic, boolean ops, unary minus, and literals/variables.
/// Any function application (user-defined or unknown BIF) returns false.
fn is_guard_safe(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit { .. } | ExprKind::Var { .. } => true,
        ExprKind::BinOp { left, right, .. } => is_guard_safe(left) && is_guard_safe(right),
        ExprKind::UnaryMinus { expr, .. } => is_guard_safe(expr),
        // No App, Constructor, Block, If, Case, etc. -- too complex for a guard
        _ => false,
    }
}

impl<'a> Lowerer<'a> {
    /// Lower an expression in an explicit lowering mode.
    ///
    /// This is currently a thin compatibility layer over the existing ambient
    /// continuation machinery. The goal is to migrate call sites toward
    /// explicit value/tail intent before simplifying the internals further.
    pub(super) fn lower_expr_in(&mut self, expr: &Expr, mode: LowerMode) -> CExpr {
        match mode {
            LowerMode::Value => self.lower_expr_with_installed_return_k(expr, None),
            LowerMode::Tail(k) => self.lower_expr_tail_compat(expr, k),
        }
    }

    /// Lower a block in an explicit lowering mode.
    pub(super) fn lower_block_in(&mut self, stmts: &[Stmt], mode: LowerMode) -> CExpr {
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
    pub(super) fn lower_expr_value(&mut self, expr: &Expr) -> CExpr {
        self.lower_expr_in(expr, LowerMode::Value)
    }

    /// Lower an expression in terminal position with an explicit continuation.
    pub(super) fn lower_expr_tail(&mut self, expr: &Expr, k: CExpr) -> CExpr {
        self.lower_expr_in(expr, LowerMode::Tail(k))
    }

    pub(super) fn lower_expr_with_call_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        if self.expr_is_effectful_call(expr) {
            if let Some((module, func_name, head, args)) = super::util::collect_qualified_call(expr)
                && let Some(call) = self.lower_qualified_call(super::QualifiedCallSite {
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
                if let Some(call) = self.lower_resolved_fun_call(super::ResolvedCallSite {
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
            if let Some((dict, method_index, args)) = super::util::collect_dict_method_call(expr)
                && let Some(call) = self.lower_dict_method_call(
                    expr.id,
                    dict,
                    method_index,
                    &args,
                    return_k.clone(),
                )
            {
                return call;
            }
            if let Some((lambda, args)) = super::util::collect_lambda_head_call(expr)
                && let Some(call) = self.lower_lambda_head_call(expr.id, lambda, &args, return_k)
            {
                return call;
            }
            panic!(
                "effectful App {:?} was classified by call_effects but no lowerer dispatch path handled it",
                expr.id
            );
        }

        self.lower_expr(expr)
    }

    /// Lower an expression with an explicitly installed return continuation.
    ///
    /// Block expressions route through block lowering directly so the return
    /// continuation applies at the terminal statement instead of through an
    /// extra ambient wrapper.
    pub(super) fn lower_expr_with_installed_return_k(
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
    fn lower_expr_tail_compat(&mut self, expr: &Expr, k: CExpr) -> CExpr {
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
    pub(super) fn lower_terminal_effectful_expr_with_return_k(
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
    fn lower_block_terminal_expr_with_return_k(
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
    fn lower_rest_block_k_with_return_k(
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
    fn lower_rest_block_with_k_k(
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
    fn lower_value_to_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
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
    fn lower_terminal_effectful_expr_to_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
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

    /// Lower a `case` expression over an already-bound scrutinee variable.
    ///
    /// Complex guards cannot be emitted directly in Core Erlang. When any arm
    /// contains one, we build a right-associated chain of one-arm cases so the
    /// fallthrough for each suffix is lowered exactly once.
    pub(super) fn lower_case_expr(&mut self, scrut_var: &str, arms: &[CaseArm]) -> CExpr {
        let arms_ref: Vec<&CaseArm> = arms.iter().collect();
        if arms_ref
            .iter()
            .all(|arm| arm.guard.as_ref().is_none_or(is_guard_safe))
        {
            let mut lowered = self.lower_case_arms_inner(scrut_var, &arms_ref);
            let has_total_catchall = arms_ref
                .iter()
                .any(|arm| arm.guard.is_none() && Self::is_catchall_pat(&arm.pattern));
            if !has_total_catchall {
                lowered.push(CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: self.case_clause_error_expr(),
                });
            }
            return CExpr::Case(Box::new(CExpr::Var(scrut_var.to_string())), lowered);
        }

        self.lower_case_expr_chain(scrut_var, &arms_ref)
    }

    fn lower_case_arms_inner(&mut self, _scrut_var: &str, arms: &[&CaseArm]) -> Vec<CArm> {
        let mut result = Vec::new();

        for arm in arms {
            let pat = self.lower_pat(
                &arm.pattern,
                &self.constructor_atoms,
                self.handler_origin_module(),
            );

            match &arm.guard {
                None => {
                    result.push(CArm {
                        pat,
                        guard: None,
                        body: self.lower_expr(&arm.body),
                    });
                }
                Some(guard) if is_guard_safe(guard) => {
                    result.push(CArm {
                        pat,
                        guard: Some(self.lower_expr(guard)),
                        body: self.lower_expr(&arm.body),
                    });
                }
                Some(_guard) => {
                    unreachable!("complex guards should be handled by lower_case_expr_chain");
                }
            }
        }

        result
    }

    fn lower_case_expr_chain(&mut self, scrut_var: &str, arms: &[&CaseArm]) -> CExpr {
        let mut rest = self.case_clause_error_expr();

        for arm in arms.iter().rev() {
            let rest_var = self.fresh();
            let rest_ref = CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            let pat = self.lower_pat(
                &arm.pattern,
                &self.constructor_atoms,
                self.handler_origin_module(),
            );
            let body_ce = self.lower_expr(&arm.body);

            let current = match &arm.guard {
                None => {
                    if Self::is_catchall_pat(&arm.pattern) {
                        self.bind_catchall_pattern(scrut_var, &arm.pattern, body_ce)
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.to_string())),
                            vec![
                                CArm {
                                    pat,
                                    guard: None,
                                    body: body_ce,
                                },
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: rest_ref,
                                },
                            ],
                        )
                    }
                }
                Some(guard) if is_guard_safe(guard) => CExpr::Case(
                    Box::new(CExpr::Var(scrut_var.to_string())),
                    vec![
                        CArm {
                            pat,
                            guard: Some(self.lower_expr(guard)),
                            body: body_ce,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref,
                        },
                    ],
                ),
                Some(guard) => {
                    let guarded_body = CExpr::Case(
                        Box::new(self.lower_expr(guard)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: body_ce,
                            },
                            CArm {
                                pat: CPat::Wildcard,
                                guard: None,
                                body: rest_ref.clone(),
                            },
                        ],
                    );

                    if Self::is_catchall_pat(&arm.pattern) {
                        self.bind_catchall_pattern(scrut_var, &arm.pattern, guarded_body)
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.to_string())),
                            vec![
                                CArm {
                                    pat,
                                    guard: None,
                                    body: guarded_body,
                                },
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: rest_ref,
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

        rest
    }

    fn case_clause_error_expr(&self) -> CExpr {
        CExpr::Call(
            "erlang".to_string(),
            "error".to_string(),
            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
        )
    }

    fn is_catchall_pat(pat: &Pat) -> bool {
        matches!(pat, Pat::Wildcard { .. } | Pat::Var { .. })
    }

    fn bind_catchall_pattern(&self, scrut_var: &str, pat: &Pat, body: CExpr) -> CExpr {
        match pat {
            Pat::Wildcard { .. } => body,
            Pat::Var { name, .. } => CExpr::Let(
                core_var(name),
                Box::new(CExpr::Var(scrut_var.to_string())),
                Box::new(body),
            ),
            _ => unreachable!("only catchall patterns should be rebound directly"),
        }
    }

    /// Lower a saturated constructor call to the appropriate Core Erlang form.
    pub(super) fn lower_ctor(&mut self, name: &str, args: Vec<&Expr>) -> CExpr {
        let bare_name = name.rsplit('.').next().unwrap_or(name);
        match bare_name {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ if args.is_empty()
                && super::beam_interop::exit_reason_bare_atom(bare_name).is_some() =>
            {
                return CExpr::Lit(CLit::Atom(
                    super::beam_interop::exit_reason_bare_atom(bare_name)
                        .unwrap()
                        .to_string(),
                ));
            }
            _ => {}
        }
        match name {
            "Cons" if args.len() == 2 => {
                let head_var = self.fresh();
                let tail_var = self.fresh();
                let head_ce = self.lower_expr_value(args[0]);
                let tail_ce = self.lower_expr_value(args[1]);
                CExpr::Let(
                    head_var.clone(),
                    Box::new(head_ce),
                    Box::new(CExpr::Let(
                        tail_var.clone(),
                        Box::new(tail_ce),
                        Box::new(CExpr::Cons(
                            Box::new(CExpr::Var(head_var)),
                            Box::new(CExpr::Var(tail_var)),
                        )),
                    )),
                )
            }
            _ => {
                // ADT constructor: tagged tuple {name, arg1, arg2, ...}
                // Look up field types from the constructor's scheme so that
                // lambda args inherit a `lambda_effect_context` and get the
                // proper CPS expansion (evidence + _ReturnK).
                let field_tys: Vec<Option<crate::typechecker::Type>> = {
                    let scheme = self.check_result.constructors.get(name);
                    if let Some(scheme) = scheme {
                        let mut tys = Vec::new();
                        let mut current = &scheme.ty;
                        while let crate::typechecker::Type::Fun(param, ret, _) = current {
                            tys.push(Some((**param).clone()));
                            current = ret;
                        }
                        tys
                    } else {
                        vec![None; args.len()]
                    }
                };

                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for (idx, arg) in args.iter().enumerate() {
                    let var = self.fresh();
                    let val = match field_tys.get(idx).and_then(|t| t.as_ref()) {
                        Some(ty) => self.lower_expr_value_with_expected_type(arg, Some(ty)),
                        None => self.lower_expr_value(arg),
                    };
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let atom =
                    mangle_ctor_atom(name, &self.constructor_atoms, self.handler_origin_module());
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
        }
    }

    /// Bind a possibly-effectful expression to `var_name` for use in `body`.
    /// If the expression is effectful, this CPS-chains it so that an aborting
    /// handler bypasses `body` entirely; otherwise emits a plain `let`.
    ///
    /// This is the load-bearing primitive for routing potentially-effectful
    /// sub-expressions through composite forms (constructor args, tuple
    /// elements, binop operands, case scrutinees, etc.).
    pub(super) fn lower_bind_expr_with_cps(
        &mut self,
        expr: &Expr,
        var_name: String,
        expected: Option<Type>,
        body: CExpr,
    ) -> CExpr {
        if self.expr_is_effectful_call(expr) || self.has_nested_effectful_expr(expr) {
            let inner_k = CExpr::Fun(vec![var_name], Box::new(body));
            let inner_k_var = self.fresh();
            let inner_body = if self.expr_is_effectful_call(expr) {
                self.lower_expr_with_call_return_k(expr, Some(CExpr::Var(inner_k_var.clone())))
            } else {
                self.lower_expr_with_k_inner(expr, &inner_k_var)
            };
            CExpr::Let(inner_k_var, Box::new(inner_k), Box::new(inner_body))
        } else {
            let ce = match expected {
                Some(ty) => self.lower_expr_value_with_expected_type(expr, Some(&ty)),
                None => self.lower_expr_value(expr),
            };
            CExpr::Let(var_name, Box::new(ce), Box::new(body))
        }
    }

    /// Assemble a composite expression from `slots`, then apply `k_var` to
    /// the result. Effectful slots are CPS-chained so an aborting handler
    /// bypasses both the assembly and the outer continuation.
    ///
    /// `build` receives one fresh variable name per slot, in order, and
    /// returns the CExpr that combines them into the final value.
    /// Evaluation order is left-to-right (slot 0 evaluates first).
    pub(super) fn lower_with_cps_slots<F>(
        &mut self,
        slots: Vec<CpsSlot<'_>>,
        k_var: &str,
        build: F,
    ) -> CExpr
    where
        F: FnOnce(&mut Self, &[String]) -> CExpr,
    {
        let vars: Vec<String> = (0..slots.len()).map(|_| self.fresh()).collect();
        let built = build(self, &vars);
        let mut body = CExpr::Apply(Box::new(CExpr::Var(k_var.to_string())), vec![built]);
        for (slot, var) in slots.into_iter().zip(vars.iter()).rev() {
            body = match slot {
                CpsSlot::Pure(ce) => CExpr::Let(var.clone(), Box::new(ce), Box::new(body)),
                CpsSlot::Expr { expr, expected } => {
                    self.lower_bind_expr_with_cps(expr, var.clone(), expected, body)
                }
            };
        }
        body
    }

    /// Lower a saturated constructor call and apply `k_var` to the constructed
    /// value. Effectful args are CPS-chained so an aborting handler skips the
    /// constructor wrapping (and `k_var`) instead of leaking its abort tuple
    /// into a constructor slot.
    ///
    /// Mirrors [`lower_record_create_with_k`] for ADT constructors.
    pub(super) fn lower_ctor_with_k(&mut self, name: &str, args: Vec<&Expr>, k_var: &str) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        let is_cons = name == "Cons" && args.len() == 2;
        let is_bare_atom = args.is_empty()
            && (matches!(bare, "Nil" | "True" | "False")
                || super::beam_interop::exit_reason_bare_atom(bare).is_some());

        // For bare-atom/empty-arg ctors there's nothing to CPS-chain; defer.
        if is_bare_atom {
            let ce = self.lower_ctor(name, args);
            return self.lower_value_to_k_with_ce(ce, k_var);
        }

        let field_tys: Vec<Option<crate::typechecker::Type>> = if is_cons {
            vec![None, None]
        } else if let Some(scheme) = self.check_result.constructors.get(name) {
            let mut tys = Vec::new();
            let mut current = &scheme.ty;
            while let crate::typechecker::Type::Fun(param, ret, _) = current {
                tys.push(Some((**param).clone()));
                current = ret;
            }
            tys
        } else {
            vec![None; args.len()]
        };

        let slots: Vec<CpsSlot<'_>> = args
            .iter()
            .enumerate()
            .map(|(i, &arg)| CpsSlot::Expr {
                expr: arg,
                expected: field_tys.get(i).and_then(|t| t.clone()),
            })
            .collect();

        let is_cons_local = is_cons;
        let name_owned = name.to_string();
        self.lower_with_cps_slots(slots, k_var, |this, vars| {
            if is_cons_local {
                CExpr::Cons(
                    Box::new(CExpr::Var(vars[0].clone())),
                    Box::new(CExpr::Var(vars[1].clone())),
                )
            } else {
                let atom = mangle_ctor_atom(
                    &name_owned,
                    &this.constructor_atoms,
                    this.handler_origin_module(),
                );
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                CExpr::Tuple(elems)
            }
        })
    }

    /// Tuple-literal variant of [`Self::lower_ctor_with_k`]: CPS-chain
    /// effectful elements so an aborting handler bypasses the tuple build
    /// and the outer continuation.
    pub(super) fn lower_tuple_with_k(&mut self, elems: &[Expr], k_var: &str) -> CExpr {
        let slots: Vec<CpsSlot<'_>> = elems
            .iter()
            .map(|e| CpsSlot::Expr {
                expr: e,
                expected: None,
            })
            .collect();
        self.lower_with_cps_slots(slots, k_var, |_, vars| {
            CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect())
        })
    }

    /// BinOp variant of [`Self::lower_ctor_with_k`]: CPS-chain effectful
    /// operands so an aborting handler bypasses the arithmetic/comparison
    /// call and the outer continuation. Short-circuit `&&` / `||` route
    /// through the case-with-k path via `lower_expr_with_k_inner` instead.
    pub(super) fn lower_binop_with_k(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        span: Option<&crate::token::Span>,
        k_var: &str,
    ) -> CExpr {
        if matches!(op, BinOp::And | BinOp::Or) {
            // Short-circuit semantics: case on left, k threaded into branches.
            return self.lower_short_circuit_with_k(left, right, matches!(op, BinOp::And), k_var);
        }

        let op_owned = op.clone();
        let span_owned: Option<crate::token::Span> = span.cloned();
        self.lower_with_cps_slots(
            vec![
                CpsSlot::Expr {
                    expr: left,
                    expected: None,
                },
                CpsSlot::Expr {
                    expr: right,
                    expected: None,
                },
            ],
            k_var,
            |this, vars| {
                this.annotate(
                    binop_call(&op_owned, &vars[0], &vars[1]),
                    span_owned.as_ref(),
                )
            },
        )
    }

    fn lower_short_circuit_with_k(
        &mut self,
        left: &Expr,
        right: &Expr,
        and: bool,
        k_var: &str,
    ) -> CExpr {
        let left_var = self.fresh();
        let short_val = CExpr::Lit(CLit::Atom(if and { "false" } else { "true" }.to_string()));
        let short_arm = CExpr::Apply(Box::new(CExpr::Var(k_var.to_string())), vec![short_val]);
        let right_arm = self.lower_branch_with_k(right, k_var);
        let (true_arm, false_arm) = if and {
            (right_arm, short_arm)
        } else {
            (short_arm, right_arm)
        };
        let case_expr = CExpr::Case(
            Box::new(CExpr::Var(left_var.clone())),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("true".to_string())),
                    guard: None,
                    body: true_arm,
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("false".to_string())),
                    guard: None,
                    body: false_arm,
                },
            ],
        );
        self.lower_bind_expr_with_cps(left, left_var, None, case_expr)
    }

    /// Field-access variant: `(eff_expr).field`. CPS-chains the record
    /// sub-expression so an aborting handler skips the `element/2` call
    /// (which would otherwise crash with `badarg` on the abort tuple).
    pub(super) fn lower_field_access_with_k(
        &mut self,
        record_expr: &Expr,
        field_idx: i64,
        k_var: &str,
    ) -> CExpr {
        self.lower_with_cps_slots(
            vec![CpsSlot::Expr {
                expr: record_expr,
                expected: None,
            }],
            k_var,
            |_, vars| {
                cerl_call(
                    "erlang",
                    "element",
                    vec![
                        CExpr::Lit(CLit::Int(field_idx)),
                        CExpr::Var(vars[0].clone()),
                    ],
                )
            },
        )
    }

    /// Record-update variant of [`Self::lower_record_create_with_k`]: CPS-chain
    /// effectful field updates (and the base record sub-expression) so an
    /// aborting handler bypasses the rebuilt tuple and the outer continuation.
    pub(super) fn lower_record_update_with_k(
        &mut self,
        record_expr: &Expr,
        field_order: Vec<String>,
        fields: &[(String, crate::token::Span, Expr)],
        k_var: &str,
    ) -> CExpr {
        use std::collections::HashMap;
        let field_map: HashMap<&str, &Expr> =
            fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();

        let rec_var = self.fresh();

        // Slot layout: [tag, field_0, field_1, ...]. Tag and untouched
        // fields are Pure slots reading from the base record via
        // `element/2` (rec_var is bound by the outer `lower_bind_expr_with_cps`
        // wrap, so it's in scope when these CExprs are evaluated).
        // Updated fields are Expr slots that get CPS-chained if effectful.
        let mut slots: Vec<CpsSlot<'_>> = Vec::with_capacity(field_order.len() + 1);
        slots.push(CpsSlot::Pure(cerl_call(
            "erlang",
            "element",
            vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(rec_var.clone())],
        )));
        for (pos, name) in field_order.iter().enumerate() {
            slots.push(match field_map.get(name.as_str()) {
                Some(new_expr) => CpsSlot::Expr {
                    expr: new_expr,
                    expected: None,
                },
                None => {
                    let idx = (pos + 2) as i64;
                    CpsSlot::Pure(cerl_call(
                        "erlang",
                        "element",
                        vec![CExpr::Lit(CLit::Int(idx)), CExpr::Var(rec_var.clone())],
                    ))
                }
            });
        }

        let inner = self.lower_with_cps_slots(slots, k_var, |_, vars| {
            CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect())
        });

        self.lower_bind_expr_with_cps(record_expr, rec_var, None, inner)
    }

    fn lower_value_to_k_with_ce(&mut self, ce: CExpr, k_var: &str) -> CExpr {
        let v = self.fresh();
        CExpr::Let(
            v.clone(),
            Box::new(ce),
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(k_var.to_string())),
                vec![CExpr::Var(v)],
            )),
        )
    }

    pub(super) fn lower_binop(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        span: Option<&crate::token::Span>,
    ) -> CExpr {
        match op {
            BinOp::And => return self.lower_short_circuit(left, right, true),
            BinOp::Or => return self.lower_short_circuit(left, right, false),
            _ => {}
        }

        let left_var = self.fresh();
        let right_var = self.fresh();
        let left_ce = self.lower_expr_value(left);
        let right_ce = self.lower_expr_value(right);
        let call = self.annotate(binop_call(op, &left_var, &right_var), span);

        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Let(
                right_var.clone(),
                Box::new(right_ce),
                Box::new(call),
            )),
        )
    }

    /// `a && b` -> `case a of true -> b; false -> false end`
    /// `a || b` -> `case a of true -> true; false -> b end`
    fn lower_short_circuit(&mut self, left: &Expr, right: &Expr, and: bool) -> CExpr {
        let left_var = self.fresh();
        let left_ce = self.lower_expr_value(left);
        let right_ce = self.lower_expr_value(right);
        let short_val = CExpr::Lit(CLit::Atom(if and { "false" } else { "true" }.to_string()));
        let (true_arm, false_arm) = if and {
            (right_ce, short_val)
        } else {
            (short_val, right_ce)
        };
        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(left_var)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: true_arm,
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: false_arm,
                    },
                ],
            )),
        )
    }

    /// Apply an optional return continuation to a final value.
    pub(super) fn apply_return_k_with(&mut self, return_k: Option<CExpr>, val: CExpr) -> CExpr {
        if let Some(k) = return_k {
            let v = self.fresh();
            CExpr::Let(
                v.clone(),
                Box::new(val),
                Box::new(CExpr::Apply(Box::new(k), vec![CExpr::Var(v)])),
            )
        } else {
            val
        }
    }

    /// Bind a pattern to a single variable name, wrapping the body in a
    /// destructuring `case` if the pattern is non-trivial (tuple, constructor, etc.).
    /// Returns `(var_name, body)` where `var_name` is safe to use in a `Let` or `Fun` param.
    pub(super) fn destructure_pat(&mut self, pat: &Pat, body: CExpr) -> (String, CExpr) {
        self.destructure_pat_inner(pat, body, false, None)
    }

    fn destructure_pat_assert(&mut self, pat: &Pat, body: CExpr, span: Span) -> (String, CExpr) {
        self.destructure_pat_inner(pat, body, true, Some(span))
    }

    fn destructure_pat_inner(
        &mut self,
        pat: &Pat,
        body: CExpr,
        is_assert: bool,
        span: Option<Span>,
    ) -> (String, CExpr) {
        if !is_assert && let Some(var) = pat_binding_var(pat) {
            return (var, body);
        }
        let tmp = self.fresh();
        let cpat = self.lower_pat(pat, &self.constructor_atoms, self.handler_origin_module());
        let mut arms = vec![CArm {
            pat: cpat,
            guard: None,
            body,
        }];
        if is_assert {
            // Add wildcard arm that panics with structured error info
            let msg = lower_string_to_binary("Assertion failed: pattern did not match");
            arms.push(CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: self.make_error(super::errors::ErrorKind::AssertFail, msg, span.as_ref()),
            });
        }
        let wrapped = CExpr::Case(Box::new(CExpr::Var(tmp.clone())), arms);
        (tmp, wrapped)
    }

    pub(super) fn lower_block_with_return_k(
        &mut self,
        stmts: &[Stmt],
        return_k: Option<CExpr>,
    ) -> CExpr {
        match stmts {
            [] => self.apply_return_k_with(return_k, CExpr::Tuple(vec![])), // unit
            [Stmt::Expr(e)] => self.lower_block_terminal_expr_with_return_k(e, return_k),
            [Stmt::Let { pattern, value, .. }] => {
                let var = pat_binding_var(pattern).unwrap_or_else(|| self.fresh());
                let expected = self.let_pat_resolved_type(pattern);
                let val_ce = self.lower_expr_value_with_expected_type(value, expected.as_ref());
                let body = self.apply_return_k_with(return_k, CExpr::Var(var.clone()));
                CExpr::Let(var, Box::new(val_ce), Box::new(body))
            }
            [Stmt::LetFun { .. }, ..] => {
                // Group consecutive LetFun clauses with the same name
                let (fun_name, fun_id) = match &stmts[0] {
                    Stmt::LetFun { id, name, .. } => (name.clone(), *id),
                    _ => unreachable!(),
                };
                let mut clauses: Vec<super::Clause> = Vec::new();
                let mut consumed = 0;
                for stmt in stmts {
                    if let Stmt::LetFun {
                        name,
                        params,
                        guard,
                        body,
                        ..
                    } = stmt
                    {
                        if *name != fun_name {
                            break;
                        }
                        clauses.push((params, guard, body));
                        consumed += 1;
                    } else {
                        break;
                    }
                }
                let rest = &stmts[consumed..];

                // Build the function body (same logic as top-level multi-clause funs)
                let source_arity = pats::lower_params(clauses[0].0).len();
                let (arity, effects, is_open_row, param_absorbed_effects, param_types) = self
                    .check_result
                    .resolved_type_for_node(fun_id)
                    .map(|ty| {
                        let (base_arity, effects) = arity_and_effects_from_type(&ty);
                        let effects = self.canonicalize_effects(effects);
                        let shape = RuntimeFunctionShape::from_type(&ty, |effects| {
                            self.canonicalize_effects(effects)
                        });
                        let is_open_row = shape.cps_shape().is_some_and(|shape| shape.is_open_row);
                        let expanded_arity = shape.expanded_arity(base_arity);
                        let param_absorbed_effects = param_absorbed_effects_from_type(&ty)
                            .into_iter()
                            .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                            .collect::<HashMap<usize, Vec<String>>>();
                        let param_types = param_types_from_type(&ty);
                        (
                            expanded_arity,
                            effects,
                            is_open_row,
                            param_absorbed_effects,
                            param_types,
                        )
                    })
                    .unwrap_or_else(|| {
                        (source_arity, Vec::new(), false, HashMap::new(), Vec::new())
                    });
                let param_names: Vec<String> = (0..arity).map(|i| format!("_LF{}", i)).collect();

                // Register in fun_info BEFORE lowering body so recursive
                // calls are recognized as saturated apply
                self.fun_info.insert(
                    fun_name.clone(),
                    FunInfo {
                        arity,
                        effects: effects.clone(),
                        is_open_row,
                        param_absorbed_effects: param_absorbed_effects.clone(),
                        param_types: param_types.clone(),
                    },
                );

                let handler_ops = self.effect_handler_ops(&effects);

                let has_effects = !handler_ops.is_empty() || is_open_row;
                let base_arity = arity - if has_effects { 2 } else { 0 };
                let effect_return_k = has_effects.then(|| CExpr::Var("_ReturnK".to_string()));

                // Install the evidence context for the body of effectful
                // local functions. Op-call emission inside the body reads
                // handler closures out of `current_evidence`.
                let saved_evidence = self.current_evidence.clone();
                if has_effects {
                    self.current_evidence = Some(EvidenceCtx {
                        var: "_Evidence".to_string(),
                        layout: super::evidence::EvidenceLayout::new(effects.iter().cloned()),
                        is_open: is_open_row,
                    });
                }

                let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() {
                    // Single clause, no guard
                    let mut params_ce = pats::lower_params(clauses[0].0);
                    if has_effects {
                        params_ce.push("_Evidence".to_string());
                        params_ce.push("_ReturnK".to_string());
                    }
                    let body = clauses[0].2;
                    let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                        self.lower_terminal_effectful_expr_with_return_k(
                            body,
                            effect_return_k.clone(),
                        )
                    } else {
                        self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                    };
                    CExpr::Fun(params_ce, Box::new(body_ce))
                } else {
                    // Multi-clause: build case expression over params
                    let scrutinee = if base_arity == 1 {
                        CExpr::Var(param_names[0].clone())
                    } else if base_arity == 0 {
                        CExpr::Lit(CLit::Atom("unit".to_string()))
                    } else {
                        CExpr::Values(
                            param_names[..base_arity]
                                .iter()
                                .map(|n| CExpr::Var(n.clone()))
                                .collect(),
                        )
                    };
                    let arms: Vec<CArm> = clauses
                        .iter()
                        .map(|(params, guard, body)| {
                            let pat = if base_arity == 1 {
                                self.lower_pat(&params[0], &self.constructor_atoms, None)
                            } else if base_arity == 0 {
                                CPat::Wildcard
                            } else {
                                CPat::Values(
                                    params
                                        .iter()
                                        .map(|p| self.lower_pat(p, &self.constructor_atoms, None))
                                        .collect(),
                                )
                            };
                            let guard_ce = guard.as_ref().map(|g| self.lower_expr(g));
                            let body_ce =
                                if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                                    self.lower_terminal_effectful_expr_with_return_k(
                                        body,
                                        effect_return_k.clone(),
                                    )
                                } else {
                                    self.lower_expr_with_installed_return_k(
                                        body,
                                        effect_return_k.clone(),
                                    )
                                };
                            CArm {
                                pat,
                                guard: guard_ce,
                                body: body_ce,
                            }
                        })
                        .collect();
                    CExpr::Fun(
                        {
                            let mut params = param_names[..base_arity].to_vec();
                            if has_effects {
                                params.push("_Evidence".to_string());
                                params.push("_ReturnK".to_string());
                            }
                            params
                        },
                        Box::new(CExpr::Case(Box::new(scrutinee), arms)),
                    )
                };
                self.current_evidence = saved_evidence;

                let rest_ce = if rest.is_empty() {
                    self.apply_return_k_with(return_k, CExpr::Tuple(vec![]))
                } else {
                    self.lower_block_with_return_k(rest, return_k)
                };

                CExpr::LetRec(vec![(fun_name, arity, fun_body)], Box::new(rest_ce))
            }
            [first, rest @ ..] => {
                // Handle binding: register as a handler alias so `with name`
                // resolves correctly. For static references, this is purely a
                // compile-time alias. For conditionals, we lower the condition
                // and register a synthetic handler that dispatches at runtime.
                // Dynamic handlers lower the RHS and bind it to a variable.
                // Let bindings with handler values: detect and register the
                // handler so `with name` resolves correctly.
                if let Stmt::Let { pattern, value, .. } = first
                    && let Pat::Var {
                        name, id: pat_id, ..
                    } = pattern
                    && self.is_handler_value(value)
                {
                    self.lower_handle_binding(name, Some(*pat_id), value);
                    if let Some((var, _effects, _has_return)) =
                        self.handle_dynamic_vars.get(name.as_str()).cloned()
                    {
                        let rhs_ce = self.lower_expr(value);
                        let rest_ce = self.lower_block_with_return_k(rest, return_k);
                        return CExpr::Let(var, Box::new(rhs_ce), Box::new(rest_ce));
                    }
                    return self.lower_block_with_return_k(rest, return_k);
                }

                // Check if the value is a call to an effectful function. If so,
                // capture the rest of the block as _ReturnK so abort-style handlers
                // skip subsequent statements (same CPS treatment as `with`).
                {
                    let value_expr = match first {
                        Stmt::Let { value, .. } => value,
                        Stmt::Expr(e) => e,
                        Stmt::LetFun { .. } => unreachable!(),
                    };
                    if self.expr_is_effectful_call(value_expr) {
                        let (pat_opt, value_expr) = match first {
                            Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                            Stmt::Expr(e) => (None, e),
                            Stmt::LetFun { .. } => unreachable!(),
                        };
                        let rest_k = self.lower_rest_block_k_with_return_k(pat_opt, rest, return_k);
                        return self.lower_expr_with_call_return_k(value_expr, Some(rest_k));
                    }
                }

                // Check if the first statement contains an effect call -- if so, CPS transform:
                // everything in `rest` becomes the continuation closure K.
                // Effect calls may be bare (EffectCall) or wrapped in App nodes
                // (App(EffectCall, arg1), arg2, ...).
                let effect_info = match first {
                    Stmt::Expr(e) => collect_effect_call_expr(e)
                        .map(|(head, name, qual, args)| (None, head.id, name, qual, args)),
                    Stmt::Let { pattern, value, .. } => collect_effect_call_expr(value)
                        .map(|(head, name, qual, args)| (Some(pattern), head.id, name, qual, args)),
                    Stmt::LetFun { .. } => None,
                };

                if let Some((pat, effect_call_id, op_name, qualifier, args)) = effect_info {
                    let k = self.lower_rest_block_k_with_return_k(pat, rest, return_k);
                    // We need to own the args for lower_effect_call
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(effect_call_id, op_name, qualifier, &args_owned, Some(k))
                } else {
                    // Check if value expression has effect calls nested in branches.
                    // If so, build a continuation K from the remaining statements and
                    // thread it through branches so abort-style handlers skip the rest.
                    let value_has_nested = match first {
                        Stmt::Expr(e) => self.has_nested_effectful_expr(e),
                        Stmt::Let { value, .. } => self.has_nested_effectful_expr(value),
                        Stmt::LetFun { .. } => false,
                    };

                    if value_has_nested {
                        let (pat_opt, value_expr) = match first {
                            Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                            Stmt::Expr(e) => (None, e),
                            Stmt::LetFun { .. } => unreachable!(),
                        };
                        let k = self.lower_rest_block_k_with_return_k(pat_opt, rest, return_k);
                        let k_var = self.fresh();
                        let body = self.lower_expr_with_k(value_expr, &k_var);
                        CExpr::Let(k_var, Box::new(k), Box::new(body))
                    } else {
                        // Normal (non-effect) statement
                        let (pat_opt, is_assert, let_span, val_ce) = match first {
                            Stmt::Let {
                                pattern,
                                value,
                                assert,
                                span,
                                ..
                            } => {
                                let expected = self.let_pat_resolved_type(pattern);
                                let val_ce = self
                                    .lower_expr_value_with_expected_type(value, expected.as_ref());
                                (Some(pattern), *assert, *span, val_ce)
                            }
                            Stmt::Expr(e) => (None, false, e.span, self.lower_expr_value(e)),
                            Stmt::LetFun { .. } => unreachable!(),
                        };
                        let rest_ce = self.lower_block_with_return_k(rest, return_k);
                        let (var, rest_ce) = match pat_opt {
                            Some(p) if is_assert => {
                                self.destructure_pat_assert(p, rest_ce, let_span)
                            }
                            Some(p) => self.destructure_pat(p, rest_ce),
                            None => (self.fresh(), rest_ce),
                        };
                        CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
                    }
                }
            }
        }
    }

    // --- Outer-K threading for nested effect calls in branches ---
    //
    // When an if/case/block has effect calls inside its branches and there is
    // an outer continuation (more statements after it in the enclosing block),
    // these methods thread K through the branches. Abort-style handlers that
    // don't call K will skip the rest of the enclosing block, matching the
    // interpreter's semantics.

    /// Lower an expression with an outer continuation K threaded through branches.
    pub(super) fn lower_expr_with_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        self.lower_expr_tail(expr, CExpr::Var(k_var.to_string()))
    }

    fn lower_expr_with_k_inner(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        match &expr.kind {
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_var = self.fresh();
                let then_ce = self.lower_branch_with_k(then_branch, k_var);
                let else_ce = self.lower_branch_with_k(else_branch, k_var);
                let case = CExpr::Case(
                    Box::new(CExpr::Var(cond_var.clone())),
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
                );
                self.lower_bind_expr_with_cps(cond, cond_var, None, case)
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_var = self.fresh();
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                let arms_ce: Vec<CArm> = arms
                    .iter()
                    .map(|arm| {
                        let pat = self.lower_pat(
                            &arm.pattern,
                            &self.constructor_atoms,
                            self.handler_origin_module(),
                        );
                        let guard_ce = arm.guard.as_ref().map(|g| self.lower_expr_value(g));
                        let body_ce = self.lower_branch_with_k(&arm.body, k_var);
                        CArm {
                            pat,
                            guard: guard_ce,
                            body: body_ce,
                        }
                    })
                    .collect();
                let case = CExpr::Case(Box::new(CExpr::Var(scrut_var.clone())), arms_ce);
                self.lower_bind_expr_with_cps(scrutinee, scrut_var, None, case)
            }
            ExprKind::Block { stmts, .. } => {
                let stmts: Vec<_> = stmts.iter().map(|a| a.node.clone()).collect();
                self.lower_block_in(&stmts, LowerMode::Tail(CExpr::Var(k_var.to_string())))
            }
            ExprKind::With { expr, handler, .. } => self.lower_with_inherited_return_k(
                expr,
                handler,
                Some(CExpr::Var(k_var.to_string())),
            ),
            ExprKind::RecordCreate { name, fields, .. } => {
                self.lower_record_create_with_k(Some(name.as_str()), expr.id, fields, k_var)
            }
            ExprKind::AnonRecordCreate { fields } => {
                self.lower_record_create_with_k(None, expr.id, fields, k_var)
            }
            ExprKind::Tuple { elements, .. }
                if elements.iter().any(|e| {
                    self.expr_is_effectful_call(e) || self.has_nested_effectful_expr(e)
                }) =>
            {
                self.lower_tuple_with_k(elements, k_var)
            }
            ExprKind::BinOp {
                op, left, right, ..
            } if self.expr_is_effectful_call(left)
                || self.has_nested_effectful_expr(left)
                || self.expr_is_effectful_call(right)
                || self.has_nested_effectful_expr(right) =>
            {
                self.lower_binop_with_k(op, left, right, Some(&expr.span), k_var)
            }
            ExprKind::FieldAccess {
                expr: rec_expr,
                field,
                record_name: resolved_name,
            } if self.expr_is_effectful_call(rec_expr)
                || self.has_nested_effectful_expr(rec_expr) =>
            {
                let idx = resolved_name
                    .as_deref()
                    .and_then(|rname| self.record_fields.get(rname))
                    .and_then(|fields| fields.iter().position(|f| f == field))
                    .map(|pos| pos + 2)
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for field access '.{}' at node {:?} (record_name={:?})",
                            field, rec_expr.id, resolved_name
                        )
                    }) as i64;
                self.lower_field_access_with_k(rec_expr, idx, k_var)
            }
            ExprKind::RecordUpdate {
                record: rec_expr,
                fields,
                record_name: resolved_name,
            } if self.expr_is_effectful_call(rec_expr)
                || self.has_nested_effectful_expr(rec_expr)
                || fields.iter().any(|(_, _, e)| {
                    self.expr_is_effectful_call(e) || self.has_nested_effectful_expr(e)
                }) =>
            {
                let order = resolved_name
                    .as_deref()
                    .and_then(|rname| self.record_fields.get(rname))
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for record update at node {:?} (record_name={:?})",
                            expr.id, resolved_name
                        )
                    });
                self.lower_record_update_with_k(rec_expr, order, fields, k_var)
            }
            _ => {
                if let Some((ctor_name, args)) = super::util::collect_ctor_call(expr)
                    && args.iter().any(|a| {
                        self.expr_is_effectful_call(a) || self.has_nested_effectful_expr(a)
                    })
                {
                    return self.lower_ctor_with_k(ctor_name, args, k_var);
                }
                // Non-constructor App whose outer call is pure but whose
                // args contain effectful sub-calls — e.g. `from (decode x)`
                // where `from` is pure and `decode x` is effectful. Without
                // this branch the inner effectful call would get lowered as
                // a plain value (no handler-arg threading), since the
                // value-mode path never receives a return continuation to
                // wrap around it. CPS-chain each argument via slot bindings
                // so effectful args run in CPS with handlers, and the
                // pure outer call assembles them through `k_var`.
                if matches!(expr.kind, ExprKind::App { .. }) && !self.expr_is_effectful_call(expr) {
                    let mut current: &Expr = expr;
                    let mut args_rev: Vec<&Expr> = Vec::new();
                    while let ExprKind::App { func, arg, .. } = &current.kind {
                        args_rev.push(arg);
                        current = func;
                    }
                    args_rev.reverse();
                    let callee = current;
                    let any_eff = args_rev.iter().any(|a| {
                        self.expr_is_effectful_call(a) || self.has_nested_effectful_expr(a)
                    });
                    if any_eff {
                        let slots: Vec<CpsSlot<'_>> = args_rev
                            .iter()
                            .map(|a| CpsSlot::Expr {
                                expr: a,
                                expected: None,
                            })
                            .collect();
                        return self.lower_with_cps_slots(slots, k_var, move |this, arg_vars| {
                            let callee_ce = this.lower_expr(callee);
                            CExpr::Apply(
                                Box::new(callee_ce),
                                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                            )
                        });
                    }
                }
                self.lower_value_to_k(expr, k_var)
            }
        }
    }

    /// Lower a record-creation expression and apply `k_var` to the constructed
    /// tuple. Effectful field values are CPS-chained so an aborting handler
    /// skips the rest of the construction (and `k_var`) instead of leaking its
    /// abort tuple into a record slot.
    fn lower_record_create_with_k(
        &mut self,
        name: Option<&str>,
        node_id: crate::ast::NodeId,
        fields: &[(String, crate::token::Span, Expr)],
        k_var: &str,
    ) -> CExpr {
        use std::collections::HashMap;

        let order: Vec<String> = match name {
            Some(rname) => self
                .resolved_record_fields(node_id, rname)
                .cloned()
                .unwrap_or_else(|| fields.iter().map(|(n, _, _)| n.clone()).collect()),
            None => {
                let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                let mut sorted: Vec<String> = names.iter().map(|s| s.to_string()).collect();
                sorted.sort();
                sorted
            }
        };
        let field_map: HashMap<&str, &Expr> =
            fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();

        let tag = match name {
            Some(rname) => super::util::mangle_ctor_atom(
                rname,
                &self.constructor_atoms,
                self.handler_origin_module(),
            ),
            None => {
                let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                crate::ast::anon_record_tag(&names)
            }
        };

        let slots: Vec<CpsSlot<'_>> = order
            .iter()
            .map(|field_name| CpsSlot::Expr {
                expr: field_map
                    .get(field_name.as_str())
                    .copied()
                    .expect("field missing in record-create"),
                expected: None,
            })
            .collect();

        self.lower_with_cps_slots(slots, k_var, |_, vars| {
            let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
            elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
            CExpr::Tuple(elems)
        })
    }

    /// Lower a branch expression with an outer continuation K.
    /// Dispatches based on whether the branch is a direct effect call,
    /// contains nested effects, or is a plain expression.
    fn lower_branch_with_k(&mut self, expr: &Expr, k_var: &str) -> CExpr {
        self.lower_terminal_effectful_expr_to_k(expr, k_var)
    }

    /// Lower a block with an outer continuation K threaded to the terminal.
    /// Like `lower_block` but applies K at terminal positions instead of return_k.
    fn lower_block_with_k(&mut self, stmts: &[Stmt], k_var: &str) -> CExpr {
        match stmts {
            [] => CExpr::Apply(
                Box::new(CExpr::Var(k_var.to_string())),
                vec![CExpr::Tuple(vec![])],
            ),
            [Stmt::Expr(e)] => self.lower_branch_with_k(e, k_var),
            [Stmt::Let { value, .. }] => self.lower_branch_with_k(value, k_var),
            [first, rest @ ..] => {
                // Handler-value let binding: register so `with name` resolves.
                // Mirrors the same detection in `lower_block_with_return_k`.
                if let Stmt::Let { pattern, value, .. } = first
                    && let Pat::Var {
                        name, id: pat_id, ..
                    } = pattern
                    && self.is_handler_value(value)
                {
                    self.lower_handle_binding(name, Some(*pat_id), value);
                    if let Some((var, _effects, _has_return)) =
                        self.handle_dynamic_vars.get(name.as_str()).cloned()
                    {
                        let rhs_ce = self.lower_expr(value);
                        let rest_ce = self.lower_block_with_k(rest, k_var);
                        return CExpr::Let(var, Box::new(rhs_ce), Box::new(rest_ce));
                    }
                    return self.lower_block_with_k(rest, k_var);
                }

                let effect_info = match first {
                    Stmt::Expr(e) => collect_effect_call_expr(e)
                        .map(|(head, name, qual, args)| (None, head.id, name, qual, args)),
                    Stmt::Let { pattern, value, .. } => collect_effect_call_expr(value)
                        .map(|(head, name, qual, args)| (Some(pattern), head.id, name, qual, args)),
                    Stmt::LetFun { .. } => None,
                };

                if let Some((pat, effect_call_id, op_name, qualifier, args)) = effect_info {
                    // Direct effect call at statement level: CPS with rest -> K-threaded
                    let inner_k = self.lower_rest_block_with_k_k(pat, rest, k_var);
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(
                        effect_call_id,
                        op_name,
                        qualifier,
                        &args_owned,
                        Some(inner_k),
                    )
                } else {
                    let (pat_opt, value_expr) = match first {
                        Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                        Stmt::Expr(e) => (None, e),
                        Stmt::LetFun { .. } => unreachable!(),
                    };

                    // Check for call to an effectful function. Capture the
                    // rest of the block as _ReturnK so CPS chains correctly
                    // (e.g. state-threading handlers need real continuations).
                    if self.expr_is_effectful_call(value_expr) {
                        let rest_k = self.lower_rest_block_with_k_k(pat_opt, rest, k_var);
                        return self.lower_expr_with_call_return_k(value_expr, Some(rest_k));
                    }

                    if self.has_nested_effectful_expr(value_expr) {
                        // Value has nested effects: build inner K and thread through
                        let inner_k = self.lower_rest_block_with_k_k(pat_opt, rest, k_var);
                        let inner_k_var = self.fresh();
                        let body = self.lower_expr_with_k_inner(value_expr, &inner_k_var);
                        CExpr::Let(inner_k_var, Box::new(inner_k), Box::new(body))
                    } else {
                        // Normal statement: evaluate, bind, then rest with K
                        let val_ce = self.lower_expr(value_expr);
                        let rest_ce = self.lower_block_with_k(rest, k_var);
                        let (var, rest_ce) = match pat_opt {
                            Some(p) => self.destructure_pat(p, rest_ce),
                            None => (self.fresh(), rest_ce),
                        };
                        CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
                    }
                }
            }
        }
    }

    /// Bind each element to a fresh variable, then build a tuple.
    /// Used for both tuple literals and record/constructor field lists.
    /// Lower a `do { Pat <- expr ... success } else { arms }` expression.
    ///
    /// Desugars to nested case expressions: each binding is a case on the
    /// scrutinee; a successful pattern match continues to the next binding,
    /// a mismatch routes the raw value to the else arms.
    pub(super) fn lower_do(
        &mut self,
        bindings: &[(Pat, Expr)],
        success: &Expr,
        else_arms: &[CaseArm],
    ) -> CExpr {
        // Pre-lower the else arms once; clone them at each failure point.
        let else_arms_ce: Vec<CArm> = else_arms
            .iter()
            .map(|arm| CArm {
                pat: self.lower_pat(
                    &arm.pattern,
                    &self.constructor_atoms,
                    self.handler_origin_module(),
                ),
                guard: arm.guard.as_ref().map(|g| self.lower_expr_value(g)),
                body: self.lower_expr(&arm.body),
            })
            .collect();

        // Build from the innermost binding outward.
        let mut inner = self.lower_expr(success);

        for (pat, expr) in bindings.iter().rev() {
            let scrut_var = self.fresh();
            let fail_var = self.fresh();
            let val_ce = self.lower_expr_value(expr);

            let success_pat =
                self.lower_pat(pat, &self.constructor_atoms, self.handler_origin_module());
            // If the success pattern is a catch-all (e.g. Just(x) lowers to a
            // bare variable), put the else arms first so they get a chance to
            // match before the catch-all swallows everything.
            let is_catchall = matches!(success_pat, CPat::Var(_));
            let success_arm = CArm {
                pat: success_pat,
                guard: None,
                body: inner,
            };
            let mut else_with_fallthrough: Vec<CArm> = else_arms_ce.clone();
            let has_catchall = else_with_fallthrough
                .iter()
                .any(|arm| arm.guard.is_none() && matches!(arm.pat, CPat::Var(_) | CPat::Wildcard));
            if !has_catchall {
                else_with_fallthrough.push(CArm {
                    pat: CPat::Var(fail_var.clone()),
                    guard: None,
                    body: CExpr::Var(fail_var),
                });
            }
            let fail_arm = CArm {
                pat: CPat::Var(self.fresh()),
                guard: None,
                body: CExpr::Case(
                    Box::new(CExpr::Var(scrut_var.clone())),
                    else_with_fallthrough,
                ),
            };
            let arms = if is_catchall {
                // Else arms first, then success as fallback
                let mut arms: Vec<CArm> = else_arms_ce
                    .iter()
                    .map(|arm| CArm {
                        pat: arm.pat.clone(),
                        guard: arm.guard.clone(),
                        body: arm.body.clone(),
                    })
                    .collect();
                arms.push(success_arm);
                arms
            } else {
                vec![success_arm, fail_arm]
            };
            let case_expr = CExpr::Case(Box::new(CExpr::Var(scrut_var.clone())), arms);
            inner = CExpr::Let(scrut_var, Box::new(val_ce), Box::new(case_expr));
        }

        inner
    }

    /// Check if an expression produces a handler value.
    pub(super) fn is_handler_value(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::HandlerExpr { .. } => true,
            ExprKind::Var { name } => {
                self.known_handler_binding_name(expr.id, name)
                    .is_some_and(|resolved_name| {
                        self.check_result.handlers.contains_key(&resolved_name)
                            || self.handler_defs.contains_key(&resolved_name)
                            || self.handle_dynamic_vars.contains_key(&resolved_name)
                            || self.handle_cond_vars.contains_key(&resolved_name)
                    })
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self.is_handler_value(then_branch) || self.is_handler_value(else_branch),
            _ => self.dynamic_handler_info_from_expr(expr).is_some(),
        }
    }

    pub(super) fn lower_tuple_elems(&mut self, elems: &[Expr]) -> CExpr {
        let mut vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for elem in elems {
            let var = self.fresh();
            let val = self.lower_expr_value(elem);
            vars.push(var.clone());
            bindings.push((var, val));
        }
        let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
        bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    /// Lower a handle binding statement. Routes the binding into one of four
    /// metadata stores depending on the RHS shape; `lower_with` later picks
    /// the matching compilation strategy based on which store the name is in.
    ///
    /// Although evidence-wrapping itself only happens at the `with` boundary
    /// (see [`Self::lower_with`]), the four paths still need to remain
    /// distinct because each captures a different *source* of handler
    /// information:
    ///
    /// - **Static alias** (`Var`): compile-time resolved canonical name in
    ///   `handler_canonical`. The handler's arms are already in
    ///   `handler_defs` from registration.
    /// - **HandlerExpr**: arms are in the `value` expression itself; we
    ///   register them under a synthetic name in `handler_defs`.
    /// - **Conditional** (`If`): both branches resolve statically; we store
    ///   the lowered condition + both canonicals in `handle_cond_vars` so
    ///   `lower_with` can emit a runtime case-split.
    /// - **Dynamic**: arbitrary RHS; we store the value's effect signature
    ///   from the typechecker in `handle_dynamic_vars` so `lower_with` can
    ///   emit a closure-call dispatch.
    ///
    /// Collapsing the four paths into one would hide these distinct
    /// metadata flows behind a uniform interface without reducing branching
    /// at the `with` boundary.
    pub(super) fn lower_handle_binding(
        &mut self,
        name: &str,
        pat_id: Option<crate::ast::NodeId>,
        value: &Expr,
    ) {
        if self.handle_dynamic_vars.contains_key(name) || self.handle_cond_vars.contains_key(name) {
            return;
        }

        // Direct handler reference: compile-time alias
        if let ExprKind::Var { name: handler_name } = &value.kind
            && let Some(canonical) = self.known_handler_binding_name(value.id, handler_name)
        {
            self.handler_canonical.insert(name.to_string(), canonical);
            return;
        }
        // Handler expression: register arms directly under synthetic name
        if let ExprKind::HandlerExpr { body } = &value.kind {
            let synthetic = format!("__handler_expr_{}", value.id.0);
            let semantic_module_name = self.current_semantic_module_name().to_string();
            let canonical_effects =
                self.resolved_effect_refs_for_module(&semantic_module_name, &body.effects);
            self.handler_defs.insert(
                synthetic.clone(),
                super::HandlerInfo {
                    effects: canonical_effects,
                    arms: body.arms.iter().map(|a| a.node.clone()).collect(),
                    return_clause: body.return_clause.clone(),
                    source_module: None,
                },
            );
            self.handler_canonical.insert(name.to_string(), synthetic);
            return;
        }
        // Conditional: generate runtime dispatch
        if let ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } = &value.kind
        {
            let then_canonical = self.resolve_handle_value(then_branch);
            let else_canonical = self.resolve_handle_value(else_branch);

            if let (Some(then_c), Some(else_c)) = (then_canonical, else_canonical) {
                let cond_ce = self.lower_expr_value(cond);
                let cond_var = self.fresh();
                self.handle_cond_vars.insert(
                    name.to_string(),
                    (cond_var, cond_ce, then_c.clone(), else_c),
                );
                // Alias to then-branch for static resolution; conditional
                // dispatch is handled in lower_with
                self.handler_canonical.insert(name.to_string(), then_c);
                return;
            }
        }

        // Dynamic handler: RHS is an arbitrary expression (e.g. function call).
        // Look up effect names from the typechecker's check result. Prefer the
        // pat-id-keyed entry, which survives the per-clause `handlers`
        // save/restore in the typechecker.
        let dynamic_info = pat_id
            .and_then(|id| self.check_result.let_binding_handlers.get(&id))
            .or_else(|| self.check_result.handlers.get(name))
            .map(|info| {
                let effects = info
                    .effects
                    .iter()
                    .map(|e| self.canonicalize_effect(e))
                    .collect();
                let has_return = info.return_type.is_some();
                (effects, has_return)
            })
            .or_else(|| {
                self.check_result
                    .type_at_node
                    .get(&value.id)
                    .and_then(|ty| self.dynamic_handler_info_from_type(ty))
                    .map(|effects| (effects, false))
            });
        let dynamic_info = dynamic_info.or_else(|| self.dynamic_handler_info_from_expr(value));
        if let Some((effects, has_return)) = dynamic_info {
            let var = self.fresh();
            self.handle_dynamic_vars
                .insert(name.to_string(), (var, effects, has_return));
        }
    }

    fn dynamic_handler_info_from_expr(&self, expr: &Expr) -> Option<(Vec<String>, bool)> {
        let cr = &self.check_result;
        if let Some(ty) = cr.type_at_node.get(&expr.id)
            && let Some(effects) = self.dynamic_handler_info_from_type(ty)
        {
            return Some((effects, false));
        }

        if let ExprKind::Var { name } = &expr.kind
            && let Some(scheme) = cr.env.get(&self.resolved_env_lookup_name(expr.id, name))
            && let Some(effects) = self.dynamic_handler_info_from_type(&scheme.ty)
        {
            return Some((effects, false));
        }

        if let Some((func_name, head_expr, args)) = collect_fun_call(expr)
            && let Some(scheme) = cr
                .env
                .get(&self.resolved_env_lookup_name(head_expr.id, func_name))
        {
            let mut ty = scheme.ty.clone();
            let arg_count = args.len();
            for _ in 0..arg_count {
                match ty {
                    Type::Fun(_, ret, _) => ty = *ret,
                    _ => break,
                }
            }
            if let Some(effects) = self.dynamic_handler_info_from_type(&ty) {
                return Some((effects, false));
            }
        }

        None
    }

    fn dynamic_handler_info_from_type(&self, ty: &Type) -> Option<Vec<String>> {
        if let Type::Con(name, args) = ty
            && name == crate::typechecker::canonicalize_type_name("Handler")
        {
            let effects: Vec<String> = args
                .iter()
                .filter_map(|arg| {
                    if let Type::Con(effect_name, _) = arg {
                        Some(self.canonicalize_effect(effect_name))
                    } else {
                        None
                    }
                })
                .collect();
            if effects.is_empty() {
                None
            } else {
                Some(effects)
            }
        } else {
            None
        }
    }

    /// Resolve a handle binding's RHS to a canonical handler name.
    /// Walks through variable references, if/else branches, and handler expressions.
    fn resolve_handle_value(&self, expr: &Expr) -> Option<String> {
        match &expr.kind {
            ExprKind::Var { name } => self.known_handler_binding_name(expr.id, name),
            ExprKind::HandlerExpr { .. } => {
                // Handler expressions registered under synthetic name
                let synthetic = format!("__handler_expr_{}", expr.id.0);
                if self.handler_defs.contains_key(&synthetic) {
                    Some(synthetic)
                } else {
                    None
                }
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self
                .resolve_handle_value(then_branch)
                .or_else(|| self.resolve_handle_value(else_branch)),
            _ => None,
        }
    }

    /// Lower a `<<seg1, seg2, ...>>` bitstring expression to `CExpr::Binary`.
    pub(super) fn lower_bitstring_expr(&mut self, segments: &[BitSegment<Expr>]) -> CExpr {
        use super::util::{
            resolve_bit_segment_flags, resolve_bit_segment_meta, resolve_bit_segment_size,
        };

        let mut segs = Vec::new();
        for seg in segments {
            // String literal sugar: expand to byte segments
            if let ExprKind::Lit {
                value: Lit::String(s, kind),
                ..
            } = &seg.value.kind
            {
                let resolved = if kind.is_multiline() {
                    super::util::process_string_escapes(s)
                } else {
                    s.clone()
                };
                for b in resolved.as_bytes() {
                    segs.push(CBinSeg::Byte(*b));
                }
                continue;
            }

            let is_binary = seg.specs.contains(&ast::BitSegSpec::Binary);
            let value = self.lower_expr_value(&seg.value);

            if is_binary && seg.size.is_none() {
                segs.push(CBinSeg::BinaryAll(value));
                continue;
            }

            let (type_name, default_size, unit) = resolve_bit_segment_meta(&seg.specs);
            let flags = resolve_bit_segment_flags(&seg.specs);
            let size = seg.size.as_ref().map(|s| self.lower_expr_value(s));
            let size_expr = resolve_bit_segment_size(size, &type_name, default_size);

            segs.push(CBinSeg::Segment {
                value,
                size: size_expr,
                unit,
                type_name,
                flags,
            });
        }
        CExpr::Binary(segs)
    }
}
