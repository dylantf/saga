//! A-normalization pass for effect calls.
//!
//! Effect calls in CPS-compiled code must appear at the top level of a block
//! statement so that `lower_block` can capture the continuation. When an effect
//! call is nested inside another expression (e.g. `1 + ask!()`), this pass
//! lifts it into its own `let` binding and replaces it with the bound variable.
//!
//! This runs on the saga AST before lowering. The interpreter is unaffected.
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
    fn normalize_stmts(&mut self, stmts: &[Annotated<Stmt>]) -> Vec<Annotated<Stmt>> {
        let mut result = Vec::new();
        for ann_stmt in stmts {
            match &ann_stmt.node {
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
                    result.extend(lifted.into_iter().map(Annotated::bare));
                    result.push(Annotated::bare(Stmt::Let {
                        pattern: pattern.clone(),
                        annotation: annotation.clone(),
                        value: new_value,
                        assert: *assert,
                        span: *span,
                    }));
                }
                Stmt::LetFun {
                    id,
                    name,
                    name_span,
                    params,
                    guard,
                    body,
                    span,
                } => {
                    let new_body = self.normalize_expr(body);
                    let new_guard = guard.as_ref().map(|g| Box::new(self.normalize_expr(g)));
                    result.push(Annotated::bare(Stmt::LetFun {
                        id: *id,
                        name: name.clone(),
                        name_span: *name_span,
                        params: params.clone(),
                        guard: new_guard,
                        body: new_body,
                        span: *span,
                    }));
                }
                Stmt::Expr(e) => {
                    let mut lifted = Vec::new();
                    let new_expr = self.normalize_top(e, &mut lifted);
                    result.extend(lifted.into_iter().map(Annotated::bare));
                    result.push(Annotated::bare(Stmt::Expr(new_expr)));
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
        match &expr.kind {
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => Expr::rebuild_like(
                expr,
                ExprKind::EffectCall {
                    name: name.clone(),
                    qualifier: qualifier.clone(),
                    args: args
                        .iter()
                        .map(|a| self.normalize_and_lift(a, lifted))
                        .collect(),
                },
            ),
            ExprKind::App { func, arg } => {
                let new_arg = self.normalize_and_lift(arg, lifted);
                let new_func = self.normalize_effect_args(func, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::App {
                        func: Box::new(new_func),
                        arg: Box::new(new_arg),
                    },
                )
            }
            _ => self.normalize_and_lift(expr, lifted),
        }
    }

    /// Lift an expression into a let-binding, returning a variable reference.
    fn lift_to_let(&mut self, expr: Expr, lifted: &mut Vec<Stmt>) -> Expr {
        let span = expr.span;
        let var_name = self.fresh();
        lifted.push(Stmt::Let {
            pattern: Pat::Var {
                id: NodeId::fresh(),
                name: var_name.clone(),
                span,
            },
            annotation: None,
            value: expr,
            assert: false,
            span,
        });
        Expr::synth(span, ExprKind::Var { name: var_name })
    }

    /// Walk an expression's sub-expressions, lifting any nested effect calls.
    /// The expression itself is NOT an effect call (that's handled by the caller).
    fn walk_expr(&mut self, expr: &Expr, lifted: &mut Vec<Stmt>) -> Expr {
        match &expr.kind {
            // Binary op: left-to-right normalization of operands.
            ExprKind::BinOp { op, left, right } => {
                let new_left = self.normalize_and_lift(left, lifted);
                let new_right = self.normalize_and_lift(right, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::BinOp {
                        op: op.clone(),
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                    },
                )
            }

            // Function application (non-effect): normalize func and arg.
            ExprKind::App { func, arg } => {
                let new_func = self.normalize_and_lift(func, lifted);
                let new_arg = self.normalize_and_lift(arg, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::App {
                        func: Box::new(new_func),
                        arg: Box::new(new_arg),
                    },
                )
            }

            // If: lift effect calls from condition; branches are their own scope.
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let new_cond = self.normalize_and_lift(cond, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::If {
                        cond: Box::new(new_cond),
                        then_branch: Box::new(self.normalize_expr(then_branch)),
                        else_branch: Box::new(self.normalize_expr(else_branch)),
                        multiline: false,
                    },
                )
            }

            // Case: lift from scrutinee; arms are their own scope.
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let new_scrut = self.normalize_and_lift(scrutinee, lifted);
                let new_arms = arms
                    .iter()
                    .map(|ann| {
                        Annotated::bare(CaseArm {
                            pattern: ann.node.pattern.clone(),
                            guard: ann.node.guard.as_ref().map(|g| self.normalize_expr(g)),
                            body: self.normalize_expr(&ann.node.body),
                            span: ann.node.span,
                        })
                    })
                    .collect();
                Expr::rebuild_like(
                    expr,
                    ExprKind::Case {
                        scrutinee: Box::new(new_scrut),
                        arms: new_arms,
                        dangling_trivia: vec![],
                    },
                )
            }

            // Block: recursively normalize the block's statements.
            ExprKind::Block { stmts, .. } => {
                let new_stmts = self.normalize_stmts(stmts);
                Expr::rebuild_like(
                    expr,
                    ExprKind::Block {
                        stmts: new_stmts,
                        dangling_trivia: vec![],
                    },
                )
            }

            // Tuple: normalize each element left-to-right.
            ExprKind::Tuple { elements } => {
                let new_elems = elements
                    .iter()
                    .map(|e| self.normalize_and_lift(e, lifted))
                    .collect();
                Expr::rebuild_like(
                    expr,
                    ExprKind::Tuple {
                        elements: new_elems,
                    },
                )
            }

            // UnaryMinus
            ExprKind::UnaryMinus { expr: inner } => {
                let new_inner = self.normalize_and_lift(inner, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::UnaryMinus {
                        expr: Box::new(new_inner),
                    },
                )
            }

            // Lambda: normalize body in its own scope.
            ExprKind::Lambda { params, body } => Expr::rebuild_like(
                expr,
                ExprKind::Lambda {
                    params: params.clone(),
                    body: Box::new(self.normalize_expr(body)),
                },
            ),

            // With: normalize the inner expression in its own scope.
            ExprKind::With {
                expr: inner,
                handler,
            } => Expr::rebuild_like(
                expr,
                ExprKind::With {
                    expr: Box::new(self.normalize_expr(inner)),
                    handler: handler.clone(),
                },
            ),

            // Resume: normalize the value.
            ExprKind::Resume { value } => {
                let new_val = self.normalize_and_lift(value, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::Resume {
                        value: Box::new(new_val),
                    },
                )
            }

            // FieldAccess: normalize the base expression.
            ExprKind::FieldAccess {
                expr: inner,
                field,
                record_name,
            } => {
                let new_inner = self.normalize_and_lift(inner, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::FieldAccess {
                        expr: Box::new(new_inner),
                        field: field.clone(),
                        record_name: record_name.clone(),
                    },
                )
            }

            // RecordCreate: normalize field values.
            ExprKind::RecordCreate { name, fields } => {
                let new_fields = fields
                    .iter()
                    .map(|(n, s, e)| (n.clone(), *s, self.normalize_and_lift(e, lifted)))
                    .collect();
                Expr::rebuild_like(
                    expr,
                    ExprKind::RecordCreate {
                        name: name.clone(),
                        fields: new_fields,
                    },
                )
            }

            // AnonRecordCreate: normalize field values.
            ExprKind::AnonRecordCreate { fields } => {
                let new_fields = fields
                    .iter()
                    .map(|(n, s, e)| (n.clone(), *s, self.normalize_and_lift(e, lifted)))
                    .collect();
                Expr::rebuild_like(expr, ExprKind::AnonRecordCreate { fields: new_fields })
            }

            // RecordUpdate: normalize record and field values.
            ExprKind::RecordUpdate {
                record,
                fields,
                record_name,
            } => {
                let new_record = self.normalize_and_lift(record, lifted);
                let new_fields = fields
                    .iter()
                    .map(|(n, s, e)| (n.clone(), *s, self.normalize_and_lift(e, lifted)))
                    .collect();
                Expr::rebuild_like(
                    expr,
                    ExprKind::RecordUpdate {
                        record: Box::new(new_record),
                        fields: new_fields,
                        record_name: record_name.clone(),
                    },
                )
            }

            // Do: normalize binding expressions and success in their own scopes.
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                let new_bindings = bindings
                    .iter()
                    .map(|(p, e)| (p.clone(), self.normalize_expr(e)))
                    .collect();
                Expr::rebuild_like(
                    expr,
                    ExprKind::Do {
                        bindings: new_bindings,
                        success: Box::new(self.normalize_expr(success)),
                        dangling_trivia: vec![],
                        else_arms: else_arms
                            .iter()
                            .map(|ann| {
                                Annotated::bare(CaseArm {
                                    pattern: ann.node.pattern.clone(),
                                    guard: ann.node.guard.as_ref().map(|g| self.normalize_expr(g)),
                                    body: self.normalize_expr(&ann.node.body),
                                    span: ann.node.span,
                                })
                            })
                            .collect(),
                    },
                )
            }

            // Elaboration-only nodes
            ExprKind::DictMethodAccess { dict, method_index } => {
                let new_dict = self.normalize_and_lift(dict, lifted);
                Expr::rebuild_like(
                    expr,
                    ExprKind::DictMethodAccess {
                        dict: Box::new(new_dict),
                        method_index: *method_index,
                    },
                )
            }

            ExprKind::ForeignCall { module, func, args } => {
                let new_args = args
                    .iter()
                    .map(|a| self.normalize_and_lift(a, lifted))
                    .collect();
                Expr::rebuild_like(
                    expr,
                    ExprKind::ForeignCall {
                        module: module.clone(),
                        func: func.clone(),
                        args: new_args,
                    },
                )
            }

            // Bare effect op references are values. Leave them in place.
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => Expr::rebuild_like(
                expr,
                ExprKind::EffectCall {
                    name: name.clone(),
                    qualifier: qualifier.clone(),
                    args: args.clone(),
                },
            ),

            ExprKind::Receive {
                arms, after_clause, ..
            } => Expr::rebuild_like(
                expr,
                ExprKind::Receive {
                    arms: arms
                        .iter()
                        .map(|ann| {
                            Annotated::bare(CaseArm {
                                pattern: ann.node.pattern.clone(),
                                guard: ann.node.guard.as_ref().map(|g| self.normalize_expr(g)),
                                body: self.normalize_expr(&ann.node.body),
                                span: ann.node.span,
                            })
                        })
                        .collect(),
                    dangling_trivia: vec![],
                    after_clause: after_clause.as_ref().map(|(timeout, body)| {
                        (
                            Box::new(self.normalize_expr(timeout)),
                            Box::new(self.normalize_expr(body)),
                        )
                    }),
                },
            ),

            // Handler expressions: clone as-is (arm bodies are normalized when lowered).
            ExprKind::HandlerExpr { .. } => expr.clone(),

            // BitString: normalize segment values and sizes.
            ExprKind::BitString { segments } => {
                let new_segs = segments
                    .iter()
                    .map(|seg| BitSegment {
                        value: self.normalize_and_lift(&seg.value, lifted),
                        size: seg
                            .size
                            .as_ref()
                            .map(|s| Box::new(self.normalize_and_lift(s, lifted))),
                        specs: seg.specs.clone(),
                        span: seg.span,
                    })
                    .collect();
                Expr::rebuild_like(expr, ExprKind::BitString { segments: new_segs })
            }

            // Leaves: no sub-expressions to normalize.
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => expr.clone(),
            ExprKind::Ascription { expr: inner, .. } => self.walk_expr(inner, lifted),

            ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {
                unreachable!("surface syntax should be desugared before normalization")
            }
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
            let mut stmts: Vec<Annotated<Stmt>> = lifted.into_iter().map(Annotated::bare).collect();
            stmts.push(Annotated::bare(Stmt::Expr(new_expr)));
            Expr::synth(
                expr.span,
                ExprKind::Block {
                    stmts,
                    dangling_trivia: vec![],
                },
            )
        }
    }
}

/// Check if an expression is an applied effect call.
/// Bare effect op references like `ping!` are values, not calls.
fn is_effect_call(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::App { func, .. } => is_effect_call_head(func),
        _ => false,
    }
}

/// Check if the head of an App chain is an `EffectCall` node.
/// Used by `is_effect_call` after we've already seen at least one App wrapper,
/// so an `EffectCall` here represents an applied op rather than a bare value.
fn is_effect_call_head(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::EffectCall { .. } => true,
        ExprKind::App { func, .. } => is_effect_call_head(func),
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
                id,
                name,
                name_span,
                params,
                guard,
                body,
                span,
            } => Decl::FunBinding {
                id: *id,
                name: name.clone(),
                name_span: *name_span,
                params: params.clone(),
                guard: guard.clone(),
                body: normalizer.normalize_expr(body),
                span: *span,
            },
            Decl::HandlerDef {
                id,
                doc,
                public,
                name,
                name_span,
                body,
                span,
                ..
            } => {
                let new_arms = body
                    .arms
                    .iter()
                    .map(|ann| {
                        Annotated::bare(HandlerArm {
                            id: ann.node.id,
                            op_name: ann.node.op_name.clone(),
                            qualifier: ann.node.qualifier.clone(),
                            params: ann.node.params.clone(),
                            body: Box::new(normalizer.normalize_expr(&ann.node.body)),
                            finally_block: ann
                                .node
                                .finally_block
                                .as_ref()
                                .map(|fb| Box::new(normalizer.normalize_expr(fb))),
                            span: ann.node.span,
                        })
                    })
                    .collect();
                let new_return = body.return_clause.as_ref().map(|rc| {
                    Box::new(HandlerArm {
                        id: rc.id,
                        op_name: rc.op_name.clone(),
                        qualifier: rc.qualifier.clone(),
                        params: rc.params.clone(),
                        body: Box::new(normalizer.normalize_expr(&rc.body)),
                        finally_block: None,
                        span: rc.span,
                    })
                });
                Decl::HandlerDef {
                    id: *id,
                    doc: doc.clone(),
                    public: *public,
                    name: name.clone(),
                    name_span: *name_span,
                    body: HandlerBody {
                        effects: body.effects.clone(),
                        needs: body.needs.clone(),
                        where_clause: body.where_clause.clone(),
                        arms: new_arms,
                        return_clause: new_return,
                    },
                    recovered_arms: vec![],
                    span: *span,
                    dangling_trivia: vec![],
                }
            }
            other => other.clone(),
        })
        .collect()
}
