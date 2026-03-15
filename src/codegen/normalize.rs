//! A-normalization pass for effect calls.
//!
//! Effect calls in CPS-compiled code must appear at the top level of a block
//! statement so that `lower_block` can capture the continuation. When an effect
//! call is nested inside another expression (e.g. `1 + ask!()`), this pass
//! lifts it into its own `let` binding and replaces it with the bound variable.
//!
//! This runs on the dylang AST before lowering. The interpreter is unaffected.
//!
//! Subexpressions containing effect calls are evaluated left-to-right.

use crate::ast::*;

/// Counter for generating unique temporary variable names.
struct Normalizer {
    counter: usize,
}

impl Normalizer {
    fn new() -> Self {
        Self { counter: 0 }
    }

    fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__eff{}", n)
    }

    /// Normalize a block's statements: lift nested effect calls to their own
    /// `let` bindings so they appear at statement level.
    fn normalize_stmts(&mut self, stmts: &[Stmt]) -> Vec<Stmt> {
        let mut result = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::Let {
                    pattern,
                    annotation,
                    value,
                    assert,
                    span,
                } => {
                    let mut lifted = Vec::new();
                    // At statement level, effect calls are fine (lower_block handles them).
                    // We only need to lift effect calls nested *inside* the value.
                    let new_value = self.normalize_top(value, &mut lifted);
                    result.extend(lifted);
                    result.push(Stmt::Let {
                        pattern: pattern.clone(),
                        annotation: annotation.clone(),
                        value: new_value,
                        assert: *assert,
                        span: *span,
                    });
                }
                Stmt::LetFun {
                    name,
                    params,
                    guard,
                    body,
                    span,
                } => {
                    let new_body = self.normalize_expr(body);
                    let new_guard = guard.as_ref().map(|g| Box::new(self.normalize_expr(g)));
                    result.push(Stmt::LetFun {
                        name: name.clone(),
                        params: params.clone(),
                        guard: new_guard,
                        body: new_body,
                        span: *span,
                    });
                }
                Stmt::Expr(e) => {
                    let mut lifted = Vec::new();
                    let new_expr = self.normalize_top(e, &mut lifted);
                    result.extend(lifted);
                    result.push(Stmt::Expr(new_expr));
                }
            }
        }
        result
    }

    /// Normalize an expression at "statement level" -- effect calls here are
    /// left in place (lower_block handles them). Only nested effect calls
    /// inside sub-expressions are lifted.
    fn normalize_top(&mut self, expr: &Expr, lifted: &mut Vec<Stmt>) -> Expr {
        if is_effect_call(expr) {
            // Root-level effect call: leave it, but normalize its arguments.
            self.normalize_effect_args(expr, lifted)
        } else {
            // Not an effect call at root: walk sub-expressions, lifting any
            // nested effect calls.
            self.normalize_and_lift(expr, lifted)
        }
    }

    /// Normalize an expression, lifting any effect calls (including this one)
    /// into `lifted` as let-bindings. This is called for sub-expressions where
    /// effect calls must not remain nested.
    fn normalize_and_lift(&mut self, expr: &Expr, lifted: &mut Vec<Stmt>) -> Expr {
        if is_effect_call(expr) {
            // This effect call is nested inside another expression.
            // Normalize its args, then lift the whole thing.
            let normalized = self.normalize_effect_args(expr, lifted);
            self.lift_to_let(normalized, lifted)
        } else {
            self.walk_expr(expr, lifted)
        }
    }

    /// Normalize the arguments of an effect call (or App-chain around one),
    /// but keep the effect call itself in place.
    fn normalize_effect_args(&mut self, expr: &Expr, lifted: &mut Vec<Stmt>) -> Expr {
        match expr {
            Expr::EffectCall {
                name,
                qualifier,
                args,
                span,
            } => Expr::EffectCall {
                name: name.clone(),
                qualifier: qualifier.clone(),
                args: args
                    .iter()
                    .map(|a| self.normalize_and_lift(a, lifted))
                    .collect(),
                span: *span,
            },
            Expr::App { func, arg, span } => {
                let new_arg = self.normalize_and_lift(arg, lifted);
                let new_func = self.normalize_effect_args(func, lifted);
                Expr::App {
                    func: Box::new(new_func),
                    arg: Box::new(new_arg),
                    span: *span,
                }
            }
            _ => self.normalize_and_lift(expr, lifted),
        }
    }

    /// Lift an expression into a let-binding, returning a variable reference.
    fn lift_to_let(&mut self, expr: Expr, lifted: &mut Vec<Stmt>) -> Expr {
        let span = expr.span();
        let var_name = self.fresh();
        lifted.push(Stmt::Let {
            pattern: Pat::Var {
                name: var_name.clone(),
                span,
            },
            annotation: None,
            value: expr,
            assert: false,
            span,
        });
        Expr::Var {
            name: var_name,
            span,
        }
    }

    /// Walk an expression's sub-expressions, lifting any nested effect calls.
    /// The expression itself is NOT an effect call (that's handled by the caller).
    fn walk_expr(&mut self, expr: &Expr, lifted: &mut Vec<Stmt>) -> Expr {
        match expr {
            // Binary op: left-to-right normalization of operands.
            Expr::BinOp {
                op,
                left,
                right,
                span,
            } => {
                let new_left = self.normalize_and_lift(left, lifted);
                let new_right = self.normalize_and_lift(right, lifted);
                Expr::BinOp {
                    op: op.clone(),
                    left: Box::new(new_left),
                    right: Box::new(new_right),
                    span: *span,
                }
            }

            // Function application (non-effect): normalize func and arg.
            Expr::App { func, arg, span } => {
                let new_func = self.normalize_and_lift(func, lifted);
                let new_arg = self.normalize_and_lift(arg, lifted);
                Expr::App {
                    func: Box::new(new_func),
                    arg: Box::new(new_arg),
                    span: *span,
                }
            }

            // If: lift effect calls from condition; branches are their own scope.
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => {
                let new_cond = self.normalize_and_lift(cond, lifted);
                Expr::If {
                    cond: Box::new(new_cond),
                    then_branch: Box::new(self.normalize_expr(then_branch)),
                    else_branch: Box::new(self.normalize_expr(else_branch)),
                    span: *span,
                }
            }

            // Case: lift from scrutinee; arms are their own scope.
            Expr::Case {
                scrutinee,
                arms,
                span,
            } => {
                let new_scrut = self.normalize_and_lift(scrutinee, lifted);
                let new_arms = arms
                    .iter()
                    .map(|arm| CaseArm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.as_ref().map(|g| self.normalize_expr(g)),
                        body: self.normalize_expr(&arm.body),
                        span: arm.span,
                    })
                    .collect();
                Expr::Case {
                    scrutinee: Box::new(new_scrut),
                    arms: new_arms,
                    span: *span,
                }
            }

            // Block: recursively normalize the block's statements.
            Expr::Block { stmts, span } => {
                let new_stmts = self.normalize_stmts(stmts);
                Expr::Block {
                    stmts: new_stmts,
                    span: *span,
                }
            }

            // Tuple: normalize each element left-to-right.
            Expr::Tuple { elements, span } => {
                let new_elems = elements
                    .iter()
                    .map(|e| self.normalize_and_lift(e, lifted))
                    .collect();
                Expr::Tuple {
                    elements: new_elems,
                    span: *span,
                }
            }

            // UnaryMinus
            Expr::UnaryMinus { expr: inner, span } => {
                let new_inner = self.normalize_and_lift(inner, lifted);
                Expr::UnaryMinus {
                    expr: Box::new(new_inner),
                    span: *span,
                }
            }

            // Lambda: normalize body in its own scope.
            Expr::Lambda { params, body, span } => Expr::Lambda {
                params: params.clone(),
                body: Box::new(self.normalize_expr(body)),
                span: *span,
            },

            // With: normalize the inner expression in its own scope.
            Expr::With {
                expr: inner,
                handler,
                span,
            } => Expr::With {
                expr: Box::new(self.normalize_expr(inner)),
                handler: handler.clone(),
                span: *span,
            },

            // Resume: normalize the value.
            Expr::Resume { value, span } => {
                let new_val = self.normalize_and_lift(value, lifted);
                Expr::Resume {
                    value: Box::new(new_val),
                    span: *span,
                }
            }

            // FieldAccess: normalize the base expression.
            Expr::FieldAccess {
                expr: inner,
                field,
                span,
            } => {
                let new_inner = self.normalize_and_lift(inner, lifted);
                Expr::FieldAccess {
                    expr: Box::new(new_inner),
                    field: field.clone(),
                    span: *span,
                }
            }

            // RecordCreate: normalize field values.
            Expr::RecordCreate { name, fields, span } => {
                let new_fields = fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.normalize_and_lift(e, lifted)))
                    .collect();
                Expr::RecordCreate {
                    name: name.clone(),
                    fields: new_fields,
                    span: *span,
                }
            }

            // RecordUpdate: normalize record and field values.
            Expr::RecordUpdate {
                record,
                fields,
                span,
            } => {
                let new_record = self.normalize_and_lift(record, lifted);
                let new_fields = fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.normalize_and_lift(e, lifted)))
                    .collect();
                Expr::RecordUpdate {
                    record: Box::new(new_record),
                    fields: new_fields,
                    span: *span,
                }
            }

            // Do: normalize binding expressions and success in their own scopes.
            Expr::Do {
                bindings,
                success,
                else_arms,
                span,
            } => {
                let new_bindings = bindings
                    .iter()
                    .map(|(p, e)| (p.clone(), self.normalize_expr(e)))
                    .collect();
                Expr::Do {
                    bindings: new_bindings,
                    success: Box::new(self.normalize_expr(success)),
                    else_arms: else_arms
                        .iter()
                        .map(|arm| CaseArm {
                            pattern: arm.pattern.clone(),
                            guard: arm.guard.as_ref().map(|g| self.normalize_expr(g)),
                            body: self.normalize_expr(&arm.body),
                            span: arm.span,
                        })
                        .collect(),
                    span: *span,
                }
            }

            // Elaboration-only nodes
            Expr::DictMethodAccess {
                dict,
                method_index,
                span,
            } => {
                let new_dict = self.normalize_and_lift(dict, lifted);
                Expr::DictMethodAccess {
                    dict: Box::new(new_dict),
                    method_index: *method_index,
                    span: *span,
                }
            }

            Expr::ForeignCall {
                module,
                func,
                args,
                span,
            } => {
                let new_args = args
                    .iter()
                    .map(|a| self.normalize_and_lift(a, lifted))
                    .collect();
                Expr::ForeignCall {
                    module: module.clone(),
                    func: func.clone(),
                    args: new_args,
                    span: *span,
                }
            }

            // Effect calls should not reach here (handled by caller), but be safe.
            Expr::EffectCall { .. } => unreachable!("effect call should be handled by caller"),

            Expr::Receive {
                arms,
                after_clause,
                span,
            } => Expr::Receive {
                arms: arms
                    .iter()
                    .map(|arm| CaseArm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.as_ref().map(|g| self.normalize_expr(g)),
                        body: self.normalize_expr(&arm.body),
                        span: arm.span,
                    })
                    .collect(),
                after_clause: after_clause.as_ref().map(|(timeout, body)| {
                    (
                        Box::new(self.normalize_expr(timeout)),
                        Box::new(self.normalize_expr(body)),
                    )
                }),
                span: *span,
            },

            // Leaves: no sub-expressions to normalize.
            Expr::Lit { .. }
            | Expr::Var { .. }
            | Expr::Constructor { .. }
            | Expr::QualifiedName { .. }
            | Expr::DictRef { .. } => expr.clone(),
        }
    }

    /// Normalize an expression that starts its own scope (branches, lambda bodies, etc.).
    /// Effect calls nested here get lifted within their own block context, not the parent's.
    fn normalize_expr(&mut self, expr: &Expr) -> Expr {
        let mut lifted = Vec::new();
        let new_expr = self.normalize_top(expr, &mut lifted);
        if lifted.is_empty() {
            new_expr
        } else {
            // Wrap in a block with the lifted bindings.
            lifted.push(Stmt::Expr(new_expr));
            Expr::Block {
                stmts: lifted,
                span: expr.span(),
            }
        }
    }
}

/// Check if an expression is an effect call (bare or wrapped in App nodes).
fn is_effect_call(expr: &Expr) -> bool {
    match expr {
        Expr::EffectCall { .. } => true,
        Expr::App { func, .. } => is_effect_call(func),
        _ => false,
    }
}

/// Public entry point: normalize a program's declarations, lifting nested
/// effect calls in function bodies to block-level statements.
pub fn normalize_effects(program: &Program) -> Program {
    let mut normalizer = Normalizer::new();
    program
        .iter()
        .map(|decl| match decl {
            Decl::FunBinding {
                name,
                params,
                guard,
                body,
                span,
            } => Decl::FunBinding {
                name: name.clone(),
                params: params.clone(),
                guard: guard.clone(),
                body: normalizer.normalize_expr(body),
                span: *span,
            },
            Decl::HandlerDef {
                public,
                name,
                effects,
                needs,
                arms,
                return_clause,
                span,
            } => {
                let new_arms = arms
                    .iter()
                    .map(|arm| HandlerArm {
                        op_name: arm.op_name.clone(),
                        params: arm.params.clone(),
                        body: Box::new(normalizer.normalize_expr(&arm.body)),
                        span: arm.span,
                    })
                    .collect();
                let new_return = return_clause.as_ref().map(|rc| {
                    Box::new(HandlerArm {
                        op_name: rc.op_name.clone(),
                        params: rc.params.clone(),
                        body: Box::new(normalizer.normalize_expr(&rc.body)),
                        span: rc.span,
                    })
                });
                Decl::HandlerDef {
                    public: *public,
                    name: name.clone(),
                    effects: effects.clone(),
                    needs: needs.clone(),
                    arms: new_arms,
                    return_clause: new_return,
                    span: *span,
                }
            }
            other => other.clone(),
        })
        .collect()
}
