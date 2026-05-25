//! Per-expression ANF rewrites. Separated from `mod.rs` for file-size
//! discipline.

use super::Anf;
use crate::ast::{
    Annotated, BitSegment, CaseArm, Expr, ExprKind, Handler, HandlerItem, Lit, NodeId, Pat, Stmt,
};
use crate::token::Span;

impl Anf {
    /// Lift complex sub-positions into `bindings`. The returned expression is
    /// a "complex form" whose sub-positions are atomic (or, if the input was
    /// already atomic, the atom itself). Block scrutinees are dissolved
    /// in-place: their stmts hoist into `bindings` and the tail is returned.
    pub(super) fn normalize_into(&mut self, e: Expr, bindings: &mut Vec<Annotated<Stmt>>) -> Expr {
        let id = e.id;
        let span = e.span;
        match e.kind {
            // --- Leaves / atoms ---
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. }
            | ExprKind::SymbolIntrinsic { .. } => Expr {
                id,
                span,
                kind: e.kind,
            },

            ExprKind::App { func, arg } => {
                // Saturated effect-call: the parser models `Stdio.print! arg0
                // arg1` as `App(App(EffectCall(print, qualifier, []), arg0),
                // arg1)`. The `EffectCall` itself isn't atomic, so the
                // ordinary `atomize_into` path on `func` would lift it to a
                // synthetic let-binding, splitting the call from its args. We
                // want the arguments to live **inside** the `EffectCall`'s
                // own `args` list so the downstream translator emits a single
                // `MExpr::Yield` with all args. Walk the spine, atomize each
                // arg, and rewrite as a flat `EffectCall(name, qualifier,
                // [atomized_args])`. The original `EffectCall` NodeId is
                // preserved so resolution lookups continue to hit.
                let mut current_func: Expr = *func;
                let mut current_arg: Expr = *arg;
                let mut args_rev: Vec<Expr> = vec![current_arg];
                while let ExprKind::App {
                    func: next_func,
                    arg: next_arg,
                } = current_func.kind
                {
                    current_func = *next_func;
                    current_arg = *next_arg;
                    args_rev.push(current_arg);
                }
                if let ExprKind::EffectCall {
                    name: eff_name,
                    qualifier,
                    args: existing_args,
                } = current_func.kind
                {
                    debug_assert!(
                        existing_args.is_empty(),
                        "parser emits EffectCall with empty args; args ride on enclosing Apps"
                    );
                    let collected_args: Vec<Expr> = args_rev
                        .into_iter()
                        .rev()
                        .map(|a| self.atomize_into(a, bindings))
                        .collect();
                    return Expr {
                        id: current_func.id,
                        span: current_func.span,
                        kind: ExprKind::EffectCall {
                            name: eff_name,
                            qualifier,
                            args: collected_args,
                        },
                    };
                }

                // Not an effect call — preserve the curried-App spine so a
                // saturated `f x y z` lowers as one call. Atomizing `func`
                // would lift each inner `App` to a synthetic let — turning
                // the saturated call into a chain of partial applications
                // that the lowerer then emits with the wrong argument count
                // under the uniform `(args..., _Evidence, _ReturnK)`
                // convention. Recursing via `normalize_into` keeps the spine
                // of `App` nodes intact while still atomizing each ARG. The
                // outer `atomize_into` (called on this whole App by its
                // parent context) will lift the saturated call once, as a
                // unit. Rebuild the spine here from the walk above.
                let mut rebuilt: Expr = Expr {
                    id: current_func.id,
                    span: current_func.span,
                    kind: current_func.kind,
                };
                rebuilt = if matches!(rebuilt.kind, ExprKind::App { .. }) {
                    self.normalize_into(rebuilt, bindings)
                } else {
                    self.atomize_into(rebuilt, bindings)
                };
                let args_in_order: Vec<Expr> = args_rev
                    .into_iter()
                    .rev()
                    .map(|a| self.atomize_into(a, bindings))
                    .collect();
                let mut acc = rebuilt;
                let total_args = args_in_order.len();
                let mut acc_span = acc.span;
                for (i, arg) in args_in_order.into_iter().enumerate() {
                    acc_span = acc_span.to(arg.span);
                    // Preserve the original `App`'s NodeId on the outermost
                    // node (the source-visible call site). Synthesize fresh
                    // IDs for any intermediate Apps from our re-spine.
                    let app_id = if i + 1 == total_args { id } else { NodeId::fresh() };
                    acc = Expr {
                        id: app_id,
                        span: acc_span,
                        kind: ExprKind::App {
                            func: Box::new(acc),
                            arg: Box::new(arg),
                        },
                    };
                }
                acc
            }
            ExprKind::BinOp { op, left, right } => {
                let left = self.atomize_into(*left, bindings);
                let right = self.atomize_into(*right, bindings);
                Expr {
                    id,
                    span,
                    kind: ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            ExprKind::UnaryMinus { expr } => {
                let expr = self.atomize_into(*expr, bindings);
                Expr {
                    id,
                    span,
                    kind: ExprKind::UnaryMinus {
                        expr: Box::new(expr),
                    },
                }
            }
            ExprKind::FieldAccess {
                expr,
                field,
                record_name,
            } => {
                let expr = self.atomize_into(*expr, bindings);
                Expr {
                    id,
                    span,
                    kind: ExprKind::FieldAccess {
                        expr: Box::new(expr),
                        field,
                        record_name,
                    },
                }
            }
            ExprKind::Tuple { elements } => {
                let elements = elements
                    .into_iter()
                    .map(|el| self.atomize_into(el, bindings))
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::Tuple { elements },
                }
            }
            ExprKind::RecordCreate { name, fields } => {
                let fields = fields
                    .into_iter()
                    .map(|(n, s, e)| (n, s, self.atomize_into(e, bindings)))
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::RecordCreate { name, fields },
                }
            }
            ExprKind::AnonRecordCreate { fields } => {
                let fields = fields
                    .into_iter()
                    .map(|(n, s, e)| (n, s, self.atomize_into(e, bindings)))
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::AnonRecordCreate { fields },
                }
            }
            ExprKind::RecordUpdate {
                record,
                fields,
                record_name,
            } => {
                let record = self.atomize_into(*record, bindings);
                let fields = fields
                    .into_iter()
                    .map(|(n, s, e)| (n, s, self.atomize_into(e, bindings)))
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::RecordUpdate {
                        record: Box::new(record),
                        fields,
                        record_name,
                    },
                }
            }
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => {
                let args = args
                    .into_iter()
                    .map(|a| self.atomize_into(a, bindings))
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::EffectCall {
                        name,
                        qualifier,
                        args,
                    },
                }
            }
            ExprKind::Resume { value } => {
                let value = self.atomize_into(*value, bindings);
                Expr {
                    id,
                    span,
                    kind: ExprKind::Resume {
                        value: Box::new(value),
                    },
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                multiline,
            } => {
                let cond = self.atomize_into(*cond, bindings);
                let then_branch = self.anf_expr(*then_branch);
                let else_branch = self.anf_expr(*else_branch);
                Expr {
                    id,
                    span,
                    kind: ExprKind::If {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                        multiline,
                    },
                }
            }
            ExprKind::Case {
                scrutinee,
                arms,
                dangling_trivia,
            } => {
                let scrutinee = self.atomize_into(*scrutinee, bindings);
                let arms = arms
                    .into_iter()
                    .map(|ann| {
                        let arm = self.norm_case_arm(ann.node);
                        Annotated {
                            node: arm,
                            leading_trivia: ann.leading_trivia,
                            trailing_comment: ann.trailing_comment,
                            trailing_trivia: ann.trailing_trivia,
                        }
                    })
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::Case {
                        scrutinee: Box::new(scrutinee),
                        arms,
                        dangling_trivia,
                    },
                }
            }
            ExprKind::Lambda { params, body } => {
                let body = self.anf_expr(*body);
                Expr {
                    id,
                    span,
                    kind: ExprKind::Lambda {
                        params,
                        body: Box::new(body),
                    },
                }
            }
            ExprKind::Block {
                stmts,
                dangling_trivia: _,
            } => self.flatten_block_into(stmts, bindings, span),
            ExprKind::With { expr, handler } => {
                let expr = self.anf_expr(*expr);
                let handler = self.norm_handler(*handler);
                Expr {
                    id,
                    span,
                    kind: ExprKind::With {
                        expr: Box::new(expr),
                        handler: Box::new(handler),
                    },
                }
            }
            ExprKind::Do {
                bindings: do_bindings,
                success,
                else_arms,
                dangling_trivia: _,
            } => {
                let lowered = lower_do(do_bindings, *success, else_arms, span);
                self.normalize_into(lowered, bindings)
            }
            ExprKind::Ascription { expr, type_expr } => {
                let expr = self.normalize_into(*expr, bindings);
                Expr {
                    id,
                    span,
                    kind: ExprKind::Ascription {
                        expr: Box::new(expr),
                        type_expr,
                    },
                }
            }
            ExprKind::HandlerExpr { body } => Expr {
                id,
                span,
                kind: ExprKind::HandlerExpr {
                    body: self.norm_handler_body(body),
                },
            },
            ExprKind::Receive {
                arms,
                after_clause,
                dangling_trivia,
            } => {
                let arms = arms
                    .into_iter()
                    .map(|ann| {
                        let arm = self.norm_case_arm(ann.node);
                        Annotated {
                            node: arm,
                            leading_trivia: ann.leading_trivia,
                            trailing_comment: ann.trailing_comment,
                            trailing_trivia: ann.trailing_trivia,
                        }
                    })
                    .collect();
                // Timeout must be atomic at the Receive site — the monadic IR's
                // `MExpr::Receive` carries it as `Atom`. Lift via `atomize_into`
                // into the outer `bindings`. The body stays in its own context
                // (arm-body discipline applies to the timeout body too).
                let after_clause = after_clause.map(|(t, b)| {
                    let t = self.atomize_into(*t, bindings);
                    let b = self.anf_expr(*b);
                    (Box::new(t), Box::new(b))
                });
                Expr {
                    id,
                    span,
                    kind: ExprKind::Receive {
                        arms,
                        after_clause,
                        dangling_trivia,
                    },
                }
            }
            ExprKind::BitString { segments } => {
                let segments = segments
                    .into_iter()
                    .map(|seg| BitSegment {
                        value: self.atomize_into(seg.value, bindings),
                        size: seg.size.map(|s| Box::new(self.atomize_into(*s, bindings))),
                        specs: seg.specs,
                        span: seg.span,
                    })
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::BitString { segments },
                }
            }
            ExprKind::DictMethodAccess {
                dict,
                trait_name,
                method_index,
            } => {
                let dict = self.atomize_into(*dict, bindings);
                Expr {
                    id,
                    span,
                    kind: ExprKind::DictMethodAccess {
                        dict: Box::new(dict),
                        trait_name,
                        method_index,
                    },
                }
            }
            ExprKind::ForeignCall { module, func, args } => {
                let args = args
                    .into_iter()
                    .map(|a| self.atomize_into(a, bindings))
                    .collect();
                Expr {
                    id,
                    span,
                    kind: ExprKind::ForeignCall { module, func, args },
                }
            }

            // Surface-syntax variants are desugared before reaching codegen.
            // Pass through unchanged.
            ExprKind::Pipe { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => Expr {
                id,
                span,
                kind: e.kind,
            },
        }
    }

    fn norm_case_arm(&mut self, arm: CaseArm) -> CaseArm {
        CaseArm {
            pattern: arm.pattern,
            guard: arm.guard.map(|g| self.anf_expr(g)),
            body: self.anf_expr(arm.body),
            span: arm.span,
        }
    }

    fn norm_handler(&mut self, h: Handler) -> Handler {
        match h {
            Handler::Named(r) => Handler::Named(r),
            Handler::Inline {
                items,
                dangling_trivia,
            } => {
                let items = items
                    .into_iter()
                    .map(|ann| {
                        let new_item = match ann.node {
                            HandlerItem::Named(r) => HandlerItem::Named(r),
                            HandlerItem::Arm(arm) => HandlerItem::Arm(self.norm_handler_arm(arm)),
                            HandlerItem::Return(arm) => {
                                HandlerItem::Return(self.norm_handler_arm(arm))
                            }
                        };
                        Annotated {
                            node: new_item,
                            leading_trivia: ann.leading_trivia,
                            trailing_comment: ann.trailing_comment,
                            trailing_trivia: ann.trailing_trivia,
                        }
                    })
                    .collect();
                Handler::Inline {
                    items,
                    dangling_trivia,
                }
            }
        }
    }

    /// Dissolve a `Block` into the surrounding `bindings` list, returning the
    /// block's tail expression. This is what keeps ANF flat: nested block
    /// values turn into flat let-sequences rather than nested wrappers.
    fn flatten_block_into(
        &mut self,
        stmts: Vec<Annotated<Stmt>>,
        bindings: &mut Vec<Annotated<Stmt>>,
        block_span: Span,
    ) -> Expr {
        let n = stmts.len();
        if n == 0 {
            return Expr::synth(block_span, ExprKind::Lit { value: Lit::Unit });
        }
        let mut tail: Option<Expr> = None;
        for (idx, ann) in stmts.into_iter().enumerate() {
            let is_last = idx + 1 == n;
            let Annotated {
                node,
                leading_trivia,
                trailing_comment,
                trailing_trivia,
            } = ann;
            match node {
                Stmt::Let {
                    pattern,
                    annotation,
                    value,
                    assert,
                    span,
                } => {
                    let value = self.normalize_into(value, bindings);
                    bindings.push(Annotated {
                        node: Stmt::Let {
                            pattern,
                            annotation,
                            value,
                            assert,
                            span,
                        },
                        leading_trivia,
                        trailing_comment,
                        trailing_trivia,
                    });
                    if is_last {
                        tail = Some(Expr::synth(span, ExprKind::Lit { value: Lit::Unit }));
                    }
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
                    let body = self.anf_expr(body);
                    let guard = guard.map(|g| Box::new(self.anf_expr(*g)));
                    bindings.push(Annotated {
                        node: Stmt::LetFun {
                            id,
                            name,
                            name_span,
                            params,
                            guard,
                            body,
                            span,
                        },
                        leading_trivia,
                        trailing_comment,
                        trailing_trivia,
                    });
                    if is_last {
                        tail = Some(Expr::synth(span, ExprKind::Lit { value: Lit::Unit }));
                    }
                }
                Stmt::Expr(e) => {
                    let normalized = self.normalize_into(e, bindings);
                    if is_last {
                        tail = Some(normalized);
                    } else {
                        let s = normalized.span;
                        bindings.push(Annotated::bare(Stmt::Let {
                            pattern: Pat::Wildcard {
                                id: NodeId::fresh(),
                                span: s,
                            },
                            annotation: None,
                            value: normalized,
                            assert: false,
                            span: s,
                        }));
                    }
                }
            }
        }
        tail.unwrap_or_else(|| Expr::synth(block_span, ExprKind::Lit { value: Lit::Unit }))
    }

    /// Like `normalize_into`, but lifts the result to an atom (`Var`) if not
    /// already atomic, appending a synthetic let to `bindings`. The lifted
    /// value retains its original `NodeId`; the wrapper let pattern and
    /// replacement `Var` use fresh IDs (`Expr::synth`).
    fn atomize_into(&mut self, e: Expr, bindings: &mut Vec<Annotated<Stmt>>) -> Expr {
        let normalized = self.normalize_into(e, bindings);
        if is_atom(&normalized) {
            return normalized;
        }
        let name = self.fresh.fresh("v");
        let span = normalized.span;
        bindings.push(Annotated::bare(Stmt::Let {
            pattern: Pat::Var {
                id: NodeId::fresh(),
                name: name.clone(),
                span,
            },
            annotation: None,
            value: normalized,
            assert: false,
            span,
        }));
        Expr::synth(span, ExprKind::Var { name })
    }
}

/// Wrap accumulated bindings around a tail expression. If there are no
/// bindings, returns the tail directly — atoms in tail position stay atomic.
pub(super) fn finish(bindings: Vec<Annotated<Stmt>>, tail: Expr) -> Expr {
    if bindings.is_empty() {
        return tail;
    }
    let span = tail.span;
    let mut stmts = bindings;
    stmts.push(Annotated::bare(Stmt::Expr(tail)));
    Expr::synth(
        span,
        ExprKind::Block {
            stmts,
            dangling_trivia: Vec::new(),
        },
    )
}

/// Whether an expression can appear in a sub-position without being lifted.
/// Tuples/records are atomic only if all their fields are atomic
/// (recursively); a lambda is atomic at its construction site regardless of
/// its body.
fn is_atom(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::Lambda { .. } => true,
        ExprKind::Tuple { elements } => elements.iter().all(is_atom),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            fields.iter().all(|(_, _, x)| is_atom(x))
        }
        _ => false,
    }
}

/// Lower `do { p1 <- e1; ...; pN <- eN; success } else { else_arms }` to a
/// nested `case` chain. Each binding `pi <- ei` becomes a `case ei { pi ->
/// next; ...else_arms }`. The else_arms are duplicated at every level so a
/// non-success result at any binding gets matched.
///
/// # Invariant: ANF may produce duplicate NodeIds in cloned subtrees
///
/// `else_arms.clone()` preserves the source NodeIds intentionally. Minting
/// fresh IDs for the duplicates would drop them from `ResolutionMap`
/// lookups (the map is keyed by source NodeId), breaking type lookups,
/// qualified-name resolution, and effect-row lookups inside the duplicated
/// arms — same hazard the agent guide warns about with misuse of
/// `Expr::synth` on relocated source expressions.
///
/// The cost is real but tolerable: post-ANF trees may contain duplicate
/// NodeIds in cloned subtrees. **Downstream consumers must not HashMap-key
/// on NodeId during tree walks** (treating IDs as a node identity for
/// dedup/visited-tracking). They *may* key on NodeId for `ResolutionMap`-
/// style lookups, where returning the same resolution for every duplicate
/// is exactly correct.
fn lower_do(
    do_bindings: Vec<(Pat, Expr)>,
    success: Expr,
    else_arms: Vec<Annotated<CaseArm>>,
    do_span: Span,
) -> Expr {
    let mut current = success;
    for (pat, value) in do_bindings.into_iter().rev() {
        let arm_span = value.span;
        let success_arm = CaseArm {
            pattern: pat,
            guard: None,
            body: current,
            span: arm_span,
        };
        let mut arms = vec![Annotated::bare(success_arm)];
        for ea in &else_arms {
            arms.push(ea.clone());
        }
        current = Expr::synth(
            do_span,
            ExprKind::Case {
                scrutinee: Box::new(value),
                arms,
                dangling_trivia: Vec::new(),
            },
        );
    }
    current
}
