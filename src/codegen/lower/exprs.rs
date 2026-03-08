/// Expression-lowering helper methods on Lowerer.
/// These are the implementations for specific expression forms, split out of
/// mod.rs to keep file sizes manageable. Effects go in effects.rs, traits in
/// traits.rs, etc.
use crate::ast::{BinOp, CaseArm, Expr, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::pats::lower_pat;
use super::util::{binop_call, pat_binding_var};
use super::Lowerer;

/// Returns true if `expr` is a valid Core Erlang guard expression:
/// comparisons, arithmetic, boolean ops, unary minus, and literals/variables.
/// Any function application (user-defined or unknown BIF) returns false.
fn is_guard_safe(expr: &Expr) -> bool {
    match expr {
        Expr::Lit { .. } | Expr::Var { .. } => true,
        Expr::BinOp { left, right, .. } => is_guard_safe(left) && is_guard_safe(right),
        Expr::UnaryMinus { expr, .. } => is_guard_safe(expr),
        // No App, Constructor, Block, If, Case, etc. -- too complex for a guard
        _ => false,
    }
}

impl Lowerer {
    /// Lower a list of case arms, handling complex guards by desugaring them
    /// into conditional expressions inside the arm body.
    ///
    /// A "complex" guard (one containing a function call) can't be emitted
    /// directly in Core Erlang. Instead we transform:
    ///   `Pat if complex_guard -> body`
    /// into:
    ///   `Pat -> if complex_guard then body else case scrut_var of <remaining arms>`
    pub(super) fn lower_case_arms(&mut self, scrut_var: &str, arms: &[CaseArm]) -> Vec<CArm> {
        let mut result = Vec::new();

        for (i, arm) in arms.iter().enumerate() {
            let pat = lower_pat(&arm.pattern, &self.record_fields);

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
                    // Remaining arms become the fallthrough.
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
                            self.lower_case_arms(scrut_var, remaining),
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
                    // Remaining arms are consumed into the fallthrough above.
                    break;
                }
            }
        }

        result
    }

    /// Lower a saturated constructor call to the appropriate Core Erlang form.
    pub(super) fn lower_ctor(&mut self, name: &str, args: Vec<&Expr>) -> CExpr {
        match name {
            "Nil" => CExpr::Nil,
            "Cons" if args.len() == 2 => {
                let head_var = self.fresh();
                let tail_var = self.fresh();
                let head_ce = self.lower_expr(args[0]);
                let tail_ce = self.lower_expr(args[1]);
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
                    let val = self.lower_expr(arg);
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let mut elems = vec![CExpr::Lit(CLit::Atom(name.to_string()))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
        }
    }

    pub(super) fn lower_binop(&mut self, op: &BinOp, left: &Expr, right: &Expr) -> CExpr {
        match op {
            BinOp::And => return self.lower_short_circuit(left, right, true),
            BinOp::Or => return self.lower_short_circuit(left, right, false),
            _ => {}
        }

        let left_var = self.fresh();
        let right_var = self.fresh();
        let left_ce = self.lower_expr(left);
        let right_ce = self.lower_expr(right);
        let call = binop_call(op, &left_var, &right_var);

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
        let left_ce = self.lower_expr(left);
        let right_ce = self.lower_expr(right);
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

    pub(super) fn lower_block(&mut self, stmts: &[Stmt]) -> CExpr {
        match stmts {
            [] => CExpr::Tuple(vec![]), // unit
            [Stmt::Expr(e)] => self.lower_expr(e),
            [Stmt::Let { pattern, value, .. }] => {
                let var = pat_binding_var(pattern).unwrap_or_else(|| self.fresh());
                let val_ce = self.lower_expr(value);
                CExpr::Let(var.clone(), Box::new(val_ce), Box::new(CExpr::Var(var)))
            }
            [first, rest @ ..] => {
                let (var, val_ce) = match first {
                    Stmt::Let { pattern, value, .. } => {
                        let var = pat_binding_var(pattern).unwrap_or_else(|| self.fresh());
                        (var, self.lower_expr(value))
                    }
                    Stmt::Expr(e) => {
                        let var = self.fresh();
                        (var, self.lower_expr(e))
                    }
                };
                let rest_ce = self.lower_block(rest);
                CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
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
                pat: lower_pat(&arm.pattern, &self.record_fields),
                guard: arm.guard.as_ref().map(|g| self.lower_expr(g)),
                body: self.lower_expr(&arm.body),
            })
            .collect();

        // Build from the innermost binding outward.
        let mut inner = self.lower_expr(success);

        for (pat, expr) in bindings.iter().rev() {
            let scrut_var = self.fresh();
            let fail_var = self.fresh();
            let val_ce = self.lower_expr(expr);

            let case_expr = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat: lower_pat(pat, &self.record_fields),
                        guard: None,
                        body: inner,
                    },
                    CArm {
                        pat: CPat::Var(fail_var.clone()),
                        guard: None,
                        body: CExpr::Case(
                            Box::new(CExpr::Var(fail_var)),
                            else_arms_ce.clone(),
                        ),
                    },
                ],
            );
            inner = CExpr::Let(scrut_var, Box::new(val_ce), Box::new(case_expr));
        }

        inner
    }

    pub(super) fn lower_tuple_elems(&mut self, elems: &[Expr]) -> CExpr {
        let mut vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for elem in elems {
            let var = self.fresh();
            let val = self.lower_expr(elem);
            vars.push(var.clone());
            bindings.push((var, val));
        }
        let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
        bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }
}
