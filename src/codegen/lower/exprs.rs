/// Expression-lowering helper methods on Lowerer.
/// General expression forms: case arms, constructors, binops, blocks, do-else, etc.
/// Effect system lowering is in effects.rs.
use crate::ast::{self, BinOp, BitSegment, CaseArm, Expr, ExprKind, Lit, Pat, Stmt};
use crate::codegen::cerl::{CArm, CBinSeg, CExpr, CLit, CPat};
use crate::token::Span;
use crate::typechecker::Type;
use std::collections::HashMap;

use super::pats::{self, lower_pat};
use super::util::{
    arity_and_effects_from_type, binop_call, collect_effect_call, collect_fun_call,
    has_nested_effect_call, lower_string_to_binary, mangle_ctor_atom,
    param_absorbed_effects_from_type, pat_binding_var,
};
use super::{FunInfo, LowerMode, Lowerer};

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
        if let Some((module, func_name, head, args)) = super::util::collect_qualified_call(expr) {
            return self.lower_qualified_call(
                module,
                func_name,
                head,
                &args,
                return_k,
                Some(&expr.span),
            );
        }
        if let Some((func_name, head_expr, args)) = collect_fun_call(expr) {
            if let Some(call) = self.lower_resolved_fun_call(
                func_name,
                head_expr,
                &args,
                return_k.clone(),
                Some(&expr.span),
            ) {
                return call;
            }
            if let Some(call) = self.lower_effectful_var_call(func_name, &args, return_k) {
                return call;
            }
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
        if let Some((op_name, qualifier, args)) = collect_effect_call(expr) {
            let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
            self.lower_effect_call(op_name, qualifier, &args_owned, return_k)
        } else if self.has_nested_effectful_expr(expr) {
            let k_var = self.fresh();
            let k_ce = return_k.expect("nested terminal effectful expr requires return_k");
            let body_ce = self.lower_expr_with_k(expr, &k_var);
            CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
        } else {
            let is_eff_call = collect_fun_call(expr)
                .map(|(name, _, _)| {
                    self.is_effectful(name) || self.current_effectful_vars.contains_key(name)
                })
                .unwrap_or(false);
            if is_eff_call {
                self.lower_expr_with_call_return_k(expr, return_k)
            } else {
                let body_ce = self.lower_expr(expr);
                self.apply_return_k_with(return_k, body_ce)
            }
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
            if matches!(expr.kind, ExprKind::With { .. }) {
                return self.lower_expr(expr);
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
        if let Some((op_name, qualifier, args)) = collect_effect_call(expr) {
            let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
            self.lower_effect_call(
                op_name,
                qualifier,
                &args_owned,
                Some(CExpr::Var(k_var.to_string())),
            )
        } else if collect_fun_call(expr)
            .map(|(name, _, _)| {
                self.is_effectful(name) || self.current_effectful_vars.contains_key(name)
            })
            .unwrap_or(false)
        {
            self.lower_expr_with_call_return_k(expr, Some(CExpr::Var(k_var.to_string())))
        } else if has_nested_effect_call(expr) || matches!(expr.kind, ExprKind::Block { .. }) {
            self.lower_expr_with_k_inner(expr, k_var)
        } else {
            self.lower_value_to_k(expr, k_var)
        }
    }

    /// Lower a list of case arms, handling complex guards by desugaring them
    /// into conditional expressions inside the arm body.
    ///
    /// A "complex" guard (one containing a function call) can't be emitted
    /// directly in Core Erlang. Instead we transform:
    ///   `Pat if complex_guard -> body`
    /// into:
    ///   `Pat -> if complex_guard then body else case scrut_var of <remaining arms>`
    pub(super) fn lower_case_arms(&mut self, scrut_var: &str, arms: &[CaseArm]) -> Vec<CArm> {
        let arms_ref: Vec<&CaseArm> = arms.iter().collect();
        self.lower_case_arms_inner(scrut_var, &arms_ref)
    }

    fn lower_case_arms_inner(&mut self, scrut_var: &str, arms: &[&CaseArm]) -> Vec<CArm> {
        let mut result = Vec::new();

        for (i, arm) in arms.iter().enumerate() {
            let pat = lower_pat(&arm.pattern, &self.record_fields, &self.constructor_atoms);

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
                Some(guard) => {
                    // Complex guard: desugar into the arm body.
                    // Remaining arms become the fallthrough when the pattern
                    // matches but the guard evaluates to false. We still keep
                    // the remaining arms in the outer case so pattern
                    // mismatches continue trying later arms normally.
                    let remaining = &arms[i + 1..];
                    let fallthrough = if remaining.is_empty() {
                        CExpr::Call(
                            "erlang".to_string(),
                            "error".to_string(),
                            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
                        )
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.to_string())),
                            self.lower_case_arms_inner(scrut_var, remaining),
                        )
                    };

                    let guard_ce = self.lower_expr(guard);
                    let body_ce = self.lower_expr(&arm.body);
                    let complex_body = CExpr::Case(
                        Box::new(guard_ce),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: body_ce,
                            },
                            CArm {
                                pat: CPat::Wildcard,
                                guard: None,
                                body: fallthrough,
                            },
                        ],
                    );
                    result.push(CArm {
                        pat,
                        guard: None,
                        body: complex_body,
                    });
                }
            }
        }

        result
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
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for arg in &args {
                    let var = self.fresh();
                    let val = self.lower_expr_value(arg);
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let atom = mangle_ctor_atom(name, &self.constructor_atoms);
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
        }
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
        let cpat = lower_pat(pat, &self.record_fields, &self.constructor_atoms);
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
                let val_ce = self.lower_expr_value(value);
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
                let (arity, effects, param_absorbed_effects) = self
                    .check_result
                    .as_ref()
                    .and_then(|cr| cr.resolved_type_for_node(fun_id))
                    .map(|ty| {
                        let (base_arity, effects) = arity_and_effects_from_type(&ty);
                        let effects = self.canonicalize_effects(effects);
                        let handler_count = self.effect_handler_ops(&effects).len();
                        let expanded_arity =
                            base_arity + handler_count + if handler_count > 0 { 1 } else { 0 };
                        let param_absorbed_effects = param_absorbed_effects_from_type(&ty)
                            .into_iter()
                            .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                            .collect::<HashMap<usize, Vec<String>>>();
                        (expanded_arity, effects, param_absorbed_effects)
                    })
                    .unwrap_or_else(|| (source_arity, Vec::new(), HashMap::new()));
                let param_names: Vec<String> = (0..arity).map(|i| format!("_LF{}", i)).collect();

                // Register in fun_info BEFORE lowering body so recursive
                // calls are recognized as saturated apply
                self.fun_info.insert(
                    fun_name.clone(),
                    FunInfo {
                        arity,
                        effects: effects.clone(),
                        param_absorbed_effects: param_absorbed_effects.clone(),
                    },
                );

                let handler_ops = self.effect_handler_ops(&effects);
                let handler_params: Vec<String> = handler_ops
                    .iter()
                    .map(|(eff, op)| Self::handler_param_name(eff, op))
                    .collect();
                let saved_handler_params = std::mem::take(&mut self.current_handler_params);
                for ((eff, op), param) in handler_ops.iter().zip(handler_params.iter()) {
                    let key = format!("{}.{}", eff, op);
                    self.current_handler_params.insert(key, param.clone());
                }

                let saved_effectful_vars = std::mem::take(&mut self.current_effectful_vars);
                for (idx, effs) in &param_absorbed_effects {
                    if let Some(pat) = clauses[0].0.get(*idx)
                        && let Pat::Var { name, .. } = pat
                    {
                        self.current_effectful_vars
                            .insert(name.clone(), effs.clone());
                    }
                }

                let has_effects = !handler_params.is_empty();
                let base_arity = arity - handler_params.len() - if has_effects { 1 } else { 0 };
                let effect_return_k = has_effects.then(|| CExpr::Var("_ReturnK".to_string()));
                let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() {
                    // Single clause, no guard
                    let mut params_ce = pats::lower_params(clauses[0].0);
                    params_ce.extend(handler_params.iter().cloned());
                    if has_effects {
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
                                pats::lower_pat(
                                    &params[0],
                                    &self.record_fields,
                                    &self.constructor_atoms,
                                )
                            } else if base_arity == 0 {
                                CPat::Wildcard
                            } else {
                                CPat::Values(
                                    params
                                        .iter()
                                        .map(|p| {
                                            pats::lower_pat(
                                                p,
                                                &self.record_fields,
                                                &self.constructor_atoms,
                                            )
                                        })
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
                            params.extend(handler_params.iter().cloned());
                            if has_effects {
                                params.push("_ReturnK".to_string());
                            }
                            params
                        },
                        Box::new(CExpr::Case(Box::new(scrutinee), arms)),
                    )
                };
                self.current_handler_params = saved_handler_params;
                self.current_effectful_vars = saved_effectful_vars;

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
                    && let Pat::Var { name, .. } = pattern
                    && self.is_handler_value(value)
                {
                    self.lower_handle_binding(name, value);
                    if let Some((var, _effects, _has_return)) =
                        self.handle_dynamic_vars.get(name.as_str()).cloned()
                    {
                        let rhs_ce = self.lower_expr(value);
                        let rest_ce = self.lower_block_with_return_k(rest, return_k);
                        return CExpr::Let(var, Box::new(rhs_ce), Box::new(rest_ce));
                    }
                    return self.lower_block_with_return_k(rest, return_k);
                }

                // If this let binding partially applies an effectful function,
                // register the bound variable so call sites thread handlers.
                if let Stmt::Let { pattern, .. } = first
                    && let Pat::Var { name, .. } = pattern
                    && let Some(effects) = self.ctx.let_effect_bindings.get(name).cloned()
                    && !effects.is_empty()
                {
                    self.current_effectful_vars.insert(name.clone(), effects);
                }

                // Check if the value is a call to an effectful function. If so,
                // capture the rest of the block as _ReturnK so abort-style handlers
                // skip subsequent statements (same CPS treatment as `with`).
                if return_k.is_some() {
                    let value_expr = match first {
                        Stmt::Let { value, .. } => value,
                        Stmt::Expr(e) => e,
                        Stmt::LetFun { .. } => unreachable!(),
                    };
                    let is_effectful_call = collect_fun_call(value_expr)
                        .map(|(name, _, _)| {
                            self.is_effectful(name)
                                || self.current_effectful_vars.contains_key(name)
                        })
                        .unwrap_or(false);
                    if is_effectful_call {
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
                    Stmt::Expr(e) => {
                        collect_effect_call(e).map(|(name, qual, args)| (None, name, qual, args))
                    }
                    Stmt::Let { pattern, value, .. } => collect_effect_call(value)
                        .map(|(name, qual, args)| (Some(pattern), name, qual, args)),
                    Stmt::LetFun { .. } => None,
                };

                if let Some((pat, op_name, qualifier, args)) = effect_info {
                    let k = self.lower_rest_block_k_with_return_k(pat, rest, return_k);
                    // We need to own the args for lower_effect_call
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(op_name, qualifier, &args_owned, Some(k))
                } else {
                    // Check if value expression has effect calls nested in branches.
                    // If so, build a continuation K from the remaining statements and
                    // thread it through branches so abort-style handlers skip the rest.
                    let value_has_nested = match first {
                        Stmt::Expr(e) => has_nested_effect_call(e),
                        Stmt::Let { value, .. } => has_nested_effect_call(value),
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
                            } => (Some(pattern), *assert, *span, self.lower_expr_value(value)),
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
                let cond_ce = self.lower_expr_value(cond);
                let then_ce = self.lower_branch_with_k(then_branch, k_var);
                let else_ce = self.lower_branch_with_k(else_branch, k_var);
                CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
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
                    )),
                )
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_var = self.fresh();
                let scrut_ce = self.lower_expr_value(scrutinee);
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                let arms_ce: Vec<CArm> = arms
                    .iter()
                    .map(|arm| {
                        let pat =
                            lower_pat(&arm.pattern, &self.record_fields, &self.constructor_atoms);
                        let guard_ce = arm.guard.as_ref().map(|g| self.lower_expr_value(g));
                        let body_ce = self.lower_branch_with_k(&arm.body, k_var);
                        CArm {
                            pat,
                            guard: guard_ce,
                            body: body_ce,
                        }
                    })
                    .collect();
                CExpr::Let(
                    scrut_var.clone(),
                    Box::new(scrut_ce),
                    Box::new(CExpr::Case(Box::new(CExpr::Var(scrut_var)), arms_ce)),
                )
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
            _ => self.lower_value_to_k(expr, k_var),
        }
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
                let effect_info = match first {
                    Stmt::Expr(e) => {
                        collect_effect_call(e).map(|(name, qual, args)| (None, name, qual, args))
                    }
                    Stmt::Let { pattern, value, .. } => collect_effect_call(value)
                        .map(|(name, qual, args)| (Some(pattern), name, qual, args)),
                    Stmt::LetFun { .. } => None,
                };

                if let Some((pat, op_name, qualifier, args)) = effect_info {
                    // Direct effect call at statement level: CPS with rest -> K-threaded
                    let inner_k = self.lower_rest_block_with_k_k(pat, rest, k_var);
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(op_name, qualifier, &args_owned, Some(inner_k))
                } else {
                    let (pat_opt, value_expr) = match first {
                        Stmt::Let { pattern, value, .. } => (Some(pattern), value),
                        Stmt::Expr(e) => (None, e),
                        Stmt::LetFun { .. } => unreachable!(),
                    };

                    // Check for call to an effectful function. Capture the
                    // rest of the block as _ReturnK so CPS chains correctly
                    // (e.g. state-threading handlers need real continuations).
                    let is_effectful_call = collect_fun_call(value_expr)
                        .map(|(name, _, _)| {
                            self.is_effectful(name)
                                || self.current_effectful_vars.contains_key(name)
                        })
                        .unwrap_or(false);
                    if is_effectful_call {
                        let rest_k = self.lower_rest_block_with_k_k(pat_opt, rest, k_var);
                        return self.lower_expr_with_call_return_k(value_expr, Some(rest_k));
                    }

                    if has_nested_effect_call(value_expr) {
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
                pat: lower_pat(&arm.pattern, &self.record_fields, &self.constructor_atoms),
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

            let success_pat = lower_pat(pat, &self.record_fields, &self.constructor_atoms);
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
            let has_catchall = else_with_fallthrough.iter().any(|arm| {
                arm.guard.is_none() && matches!(arm.pat, CPat::Var(_) | CPat::Wildcard)
            });
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
                self.resolve_handler_name_opt(name).is_some()
                    || self.check_result.as_ref().is_some_and(|cr| {
                        cr.handlers.contains_key(name)
                            || self.dynamic_handler_info_from_expr(expr).is_some()
                    })
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self.is_handler_value(then_branch) || self.is_handler_value(else_branch),
            ExprKind::App { .. } => self.dynamic_handler_info_from_expr(expr).is_some(),
            _ => false,
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

    /// Lower a handle binding statement. For direct handler references, registers
    /// a compile-time alias. For conditionals, the condition is lowered and the
    /// handle binding stores a flag variable; handler dispatch uses both handlers'
    /// arms wrapped in a conditional at runtime.
    pub(super) fn lower_handle_binding(&mut self, name: &str, value: &Expr) {
        if self.handle_dynamic_vars.contains_key(name) || self.handle_cond_vars.contains_key(name) {
            return;
        }

        // Direct handler reference: compile-time alias
        if let ExprKind::Var { name: handler_name } = &value.kind
            && self.resolve_handler_name_opt(handler_name).is_some()
        {
            let canonical = self.resolve_handler_name(handler_name);
            self.handler_canonical.insert(name.to_string(), canonical);
            return;
        }
        // Handler expression: register arms directly under synthetic name
        if let ExprKind::HandlerExpr { body } = &value.kind {
            let synthetic = format!("__handler_expr_{}", value.id.0);
            let canonical_effects = body
                .effects
                .iter()
                .map(|e| self.canonicalize_effect(&e.name))
                .collect();
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
        // Look up effect names from the typechecker's check result.
        if let Some(cr) = &self.check_result {
            let dynamic_info = cr
                .handlers
                .get(name)
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
                    cr.type_at_node
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
    }

    fn dynamic_handler_info_from_expr(&self, expr: &Expr) -> Option<(Vec<String>, bool)> {
        let cr = self.check_result.as_ref()?;
        if let Some(ty) = cr.type_at_node.get(&expr.id)
            && let Some(effects) = self.dynamic_handler_info_from_type(ty)
        {
            return Some((effects, false));
        }

        if let ExprKind::Var { name } = &expr.kind
            && let Some(scheme) = cr.env.get(name)
            && let Some(effects) = self.dynamic_handler_info_from_type(&scheme.ty)
        {
            return Some((effects, false));
        }

        if let Some((func_name, _, args)) = collect_fun_call(expr)
            && let Some(scheme) = cr.env.get(func_name)
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
            ExprKind::Var { name } => Some(self.resolve_handler_name(name)),
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
