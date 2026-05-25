//! Per-expression monadic translation.
//!
//! Atomic positions (ANF-guaranteed) collapse into `Atom`; complex positions
//! become structural `MExpr` variants. Every sequencing point is `Bind`.

use super::{Translator, fresh_node_id, wrap_binds};
use crate::ast::{self, Annotated, Expr, ExprKind, HandlerBody, Lit, NodeId, Pat, Stmt};
use crate::codegen::monadic::ir::{Atom, EffectOpRef, MArm, MBitSegment, MExpr, MHandler, MVar};

impl<'a> Translator<'a> {
    /// Translate an expression in tail position (its own computation context).
    pub(crate) fn translate_expr(&mut self, e: &Expr) -> MExpr {
        // Strip surface ascriptions transparently; they are erased post-typecheck.
        if let ExprKind::Ascription { expr, .. } = &e.kind {
            return self.translate_expr(expr);
        }

        // Atoms in tail position lift directly into Pure.
        if let Some(atom) = self.try_atom(e) {
            return MExpr::Pure(atom);
        }

        match &e.kind {
            // ----- Block: flat post-ANF let-sequence ending in a tail expr.
            ExprKind::Block { stmts, .. } => self.translate_block(stmts, e.span),

            // ----- Application (curried in AST, flat in MIR). -----
            ExprKind::App { .. } => self.translate_app(e),

            // ----- Effect call → Yield. -----
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => {
                let op = self.resolve_effect_op(e.id, name, qualifier.as_deref());
                let args = args.iter().map(|a| self.expect_atom(a)).collect();
                MExpr::Yield {
                    op,
                    args,
                    source: e.id,
                }
            }

            // ----- Resume. -----
            ExprKind::Resume { value } => MExpr::Resume {
                value: self.expect_atom(value),
                source: e.id,
            },

            // ----- Control flow. -----
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => MExpr::If {
                cond: self.expect_atom(cond),
                then_branch: Box::new(self.translate_expr(then_branch)),
                else_branch: Box::new(self.translate_expr(else_branch)),
                source: e.id,
            },

            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrutinee = self.expect_atom(scrutinee);
                let arms = arms
                    .iter()
                    .map(|a| self.translate_case_arm(&a.node))
                    .collect();
                MExpr::Case {
                    scrutinee,
                    arms,
                    source: e.id,
                }
            }

            // ----- With expression → handler classification. -----
            ExprKind::With { expr, handler } => {
                let handler = self.translate_handler(handler, e.span);
                MExpr::With {
                    handler,
                    body: Box::new(self.translate_expr(expr)),
                    source: e.id,
                }
            }

            // ----- Pure structural with atomic sub-positions. -----
            ExprKind::BinOp { op, left, right } => MExpr::BinOp {
                op: op.clone(),
                left: self.expect_atom(left),
                right: self.expect_atom(right),
                source: e.id,
            },

            ExprKind::UnaryMinus { expr } => MExpr::UnaryMinus {
                value: self.expect_atom(expr),
                source: e.id,
            },

            ExprKind::FieldAccess {
                expr,
                field,
                record_name,
            } => MExpr::FieldAccess {
                record: self.expect_atom(expr),
                field: field.clone(),
                record_name: record_name.clone(),
                source: e.id,
            },

            ExprKind::RecordUpdate {
                record,
                fields,
                record_name,
            } => MExpr::RecordUpdate {
                record: self.expect_atom(record),
                fields: fields
                    .iter()
                    .map(|(n, _, x)| (n.clone(), self.expect_atom(x)))
                    .collect(),
                record_name: record_name.clone(),
                source: e.id,
            },

            ExprKind::DictMethodAccess {
                dict,
                trait_name,
                method_index,
            } => MExpr::DictMethodAccess {
                dict: self.expect_atom(dict),
                trait_name: trait_name.clone(),
                method_index: *method_index,
                source: e.id,
            },

            ExprKind::ForeignCall { module, func, args } => MExpr::ForeignCall {
                module: module.clone(),
                func: func.clone(),
                args: args.iter().map(|a| self.expect_atom(a)).collect(),
                source: e.id,
            },

            ExprKind::BitString { segments } => MExpr::BitString {
                segments: segments
                    .iter()
                    .map(|seg| MBitSegment {
                        value: self.expect_atom(&seg.value),
                        size: seg.size.as_deref().map(|s| self.expect_atom(s)),
                        specs: seg.specs.clone(),
                        span: seg.span,
                    })
                    .collect(),
                source: e.id,
            },

            ExprKind::Receive {
                arms, after_clause, ..
            } => MExpr::Receive {
                arms: arms
                    .iter()
                    .map(|a| self.translate_case_arm(&a.node))
                    .collect(),
                after: after_clause
                    .as_ref()
                    .map(|(t, b)| (self.expect_atom(t), Box::new(self.translate_expr(b)))),
                source: e.id,
            },

            // ----- HandlerExpr at expression position (not under `with`).
            // The translator does not produce a standalone MExpr variant for
            // it (per spec). When used directly as a value, it would have
            // been hoisted into a let-binding by upstream passes; here we
            // emit `Pure(Atom::Lambda)` shaped as a dummy until a later step
            // wires this case. For now this is an unreachable shape post-ANF
            // outside of `with` and outside of `let h = handler ...`.
            //
            // If we hit this case in practice it indicates a flow we don't
            // yet handle — surface as a panic so the caller can investigate.
            ExprKind::HandlerExpr { .. } => {
                panic!(
                    "monadic::translate: `handler for E {{ ... }}` outside `with` or alias-let \
                     not yet supported (NodeId {:?})",
                    e.id
                );
            }

            // Surface-syntax variants must be desugared before codegen.
            ExprKind::Pipe { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {
                panic!(
                    "monadic::translate: surface-syntax {:?} should have been desugared before \
                     codegen",
                    std::mem::discriminant(&e.kind)
                );
            }

            // `Do` is lowered in ANF (step 2) before reaching the translator.
            ExprKind::Do { .. } => {
                panic!(
                    "monadic::translate: ExprKind::Do should have been lowered by ANF before \
                     translation"
                );
            }

            // Ascription handled at top; atoms (Lit/Var/Lambda/...) handled
            // by `try_atom`. Everything else is structural and matched above.
            _ => {
                // Exhaustive defensively — should be unreachable since
                // `try_atom` already returned for atomic kinds.
                unreachable!("translate_expr: unhandled atomic-looking kind: {:?}", e.id)
            }
        }
    }

    /// Try interpreting `e` as an `Atom`. Returns `None` for complex shapes.
    pub(crate) fn try_atom(&mut self, e: &Expr) -> Option<Atom> {
        match &e.kind {
            ExprKind::Lit { value } => Some(Atom::Lit {
                value: value.clone(),
                source: e.id,
            }),
            ExprKind::Var { name } => Some(Atom::Var {
                name: MVar {
                    name: name.clone(),
                    id: self.next_mvar_id(),
                },
                source: e.id,
            }),
            ExprKind::Constructor { name } => Some(Atom::Ctor {
                name: name.clone(),
                args: Vec::new(),
                source: e.id,
            }),
            ExprKind::QualifiedName { module, name, .. } => Some(Atom::QualifiedRef {
                module: module.clone(),
                name: name.clone(),
                source: e.id,
            }),
            ExprKind::DictRef { name } => Some(Atom::DictRef {
                name: name.clone(),
                source: e.id,
            }),
            ExprKind::SymbolIntrinsic { symbol } => Some(Atom::Symbol {
                symbol: symbol.clone(),
                source: e.id,
            }),
            ExprKind::Lambda { params, body } => Some(Atom::Lambda {
                params: params.clone(),
                body: Box::new(self.translate_expr(body)),
                source: e.id,
            }),
            ExprKind::Tuple { elements } => {
                let mut atoms = Vec::with_capacity(elements.len());
                for el in elements {
                    atoms.push(self.try_atom(el)?);
                }
                Some(Atom::Tuple {
                    elements: atoms,
                    source: e.id,
                })
            }
            ExprKind::RecordCreate { name, fields } => {
                let mut out = Vec::with_capacity(fields.len());
                for (fname, _, fexpr) in fields {
                    out.push((fname.clone(), self.try_atom(fexpr)?));
                }
                Some(Atom::Record {
                    name: name.clone(),
                    fields: out,
                    source: e.id,
                })
            }
            ExprKind::AnonRecordCreate { fields } => {
                let mut out = Vec::with_capacity(fields.len());
                for (fname, _, fexpr) in fields {
                    out.push((fname.clone(), self.try_atom(fexpr)?));
                }
                Some(Atom::AnonRecord {
                    fields: out,
                    source: e.id,
                })
            }
            // App-of-Constructor isn't atomic at the AST level; ANF will have
            // already lifted complex subterms. A literal constructor with
            // atomic args is observed as `App(... App(Constructor, a) ..., n)`
            // shape, which we treat as a normal App below.
            _ => None,
        }
    }

    /// Require an atomic expression here (ANF guarantees the invariant).
    /// Panics with a clear message if violated — that would be an ANF bug.
    pub(crate) fn expect_atom(&mut self, e: &Expr) -> Atom {
        match self.try_atom(e) {
            Some(a) => a,
            None => panic!(
                "monadic::translate: expected atom but found complex expr at NodeId {:?} \
                 (ANF should have lifted this)",
                e.id
            ),
        }
    }

    fn translate_case_arm(&mut self, arm: &ast::CaseArm) -> MArm {
        MArm {
            pattern: arm.pattern.clone(),
            guard: arm.guard.as_ref().map(|g| self.translate_expr(g)),
            body: self.translate_expr(&arm.body),
            span: arm.span,
        }
    }

    /// Translate a curried `App` chain into a flat `App { head, args }`.
    /// Source is the outermost App's NodeId — that's the id ResolutionMap
    /// uses if it keys on the call site (head reference resolution lives
    /// on the inner Var/QualifiedName node, which keeps its own NodeId on
    /// the Atom).
    fn translate_app(&mut self, e: &Expr) -> MExpr {
        let outer_id = e.id;
        // Walk the spine.
        let mut args_rev: Vec<&Expr> = Vec::new();
        let mut cur = e;
        while let ExprKind::App { func, arg } = &cur.kind {
            args_rev.push(arg);
            cur = func;
        }
        let head = self.expect_atom(cur);
        let args: Vec<Atom> = args_rev
            .into_iter()
            .rev()
            .map(|a| self.expect_atom(a))
            .collect();
        MExpr::App {
            head,
            args,
            source: outer_id,
        }
    }

    /// Translate a post-ANF block — a flat let-sequence ending in a tail
    /// expression — into nested `Bind`s. Tracks `let h = handler ...` aliases
    /// in the local scope so subsequent `with h` can resolve statically.
    fn translate_block(
        &mut self,
        stmts: &[Annotated<Stmt>],
        block_span: crate::token::Span,
    ) -> MExpr {
        // Save+restore scope so handler aliases don't leak across blocks.
        let saved = self.local_static_handlers.clone();

        let n = stmts.len();
        if n == 0 {
            return MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: fresh_node_id(),
            });
        }

        let mut bindings: Vec<(MVar, MExpr)> = Vec::new();
        let mut tail: Option<MExpr> = None;

        for (idx, ann) in stmts.iter().enumerate() {
            let is_last = idx + 1 == n;
            match &ann.node {
                Stmt::Let { pattern, value, .. } => {
                    // Record handler-alias info before translating the body.
                    if let Pat::Var { name, .. } = pattern {
                        self.record_handler_alias(name, value);
                    }
                    // `let h = handler for E { ... }` is bookkeeping: we
                    // recorded the alias above and the handler value itself
                    // has no representation outside a `with` site. Skip
                    // emitting a Bind for it. This matches the spec: a bare
                    // `HandlerExpr` has no standalone MExpr variant.
                    if super::match_handler_expr(value).is_some() {
                        if is_last {
                            tail = Some(MExpr::Pure(Atom::Lit {
                                value: Lit::Unit,
                                source: fresh_node_id(),
                            }));
                        }
                        continue;
                    }
                    let translated = self.translate_expr(value);
                    let var = self.binder_from_pat(pattern);
                    bindings.push((var, translated));
                    if is_last {
                        tail = Some(MExpr::Pure(Atom::Lit {
                            value: Lit::Unit,
                            source: fresh_node_id(),
                        }));
                    }
                }
                Stmt::LetFun {
                    id,
                    name,
                    params,
                    body,
                    ..
                } => {
                    // `let f x = body` inside a block. The body is its own
                    // computation context (lambda). We lift it as a Lambda
                    // atom under a Bind on the function name.
                    let lambda_body = self.translate_expr(body);
                    let atom = Atom::Lambda {
                        params: params.clone(),
                        body: Box::new(lambda_body),
                        source: *id,
                    };
                    let var = MVar {
                        name: name.clone(),
                        id: self.next_mvar_id(),
                    };
                    bindings.push((var, MExpr::Pure(atom)));
                    if is_last {
                        tail = Some(MExpr::Pure(Atom::Lit {
                            value: Lit::Unit,
                            source: fresh_node_id(),
                        }));
                    }
                }
                Stmt::Expr(expr) => {
                    let translated = self.translate_expr(expr);
                    if is_last {
                        tail = Some(translated);
                    } else {
                        // Non-tail expr stmt — sequence through a wildcard bind.
                        let var = MVar {
                            name: "_".to_string(),
                            id: self.next_mvar_id(),
                        };
                        bindings.push((var, translated));
                    }
                }
            }
        }

        let _ = block_span;
        let result = wrap_binds(
            bindings,
            tail.unwrap_or(MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: fresh_node_id(),
            })),
        );

        // Restore scope.
        self.local_static_handlers = saved;
        result
    }

    /// Choose an `MVar` for a `let` pattern binder. Non-`Var` patterns get a
    /// synthetic name; matching against the pattern itself is the lowerer's
    /// job (post-ANF most lets are `Var`).
    fn binder_from_pat(&mut self, pat: &Pat) -> MVar {
        match pat {
            Pat::Var { name, .. } => MVar {
                name: name.clone(),
                id: self.next_mvar_id(),
            },
            Pat::Wildcard { .. } => MVar {
                name: "_".to_string(),
                id: self.next_mvar_id(),
            },
            _ => MVar {
                name: "__pat".to_string(),
                id: self.next_mvar_id(),
            },
        }
    }

    /// If `value` is itself a handler (inline `HandlerExpr`, or a Var/Name
    /// that resolves to a static handler), record the alias so `with name`
    /// later in the block can be classified as `Static`.
    fn record_handler_alias(&mut self, name: &str, value: &Expr) {
        if let Some(body) = super::match_handler_expr(value) {
            self.local_static_handlers
                .insert(name.to_string(), Some(body.clone()));
            return;
        }
        if let ExprKind::Var { name: rhs } = &value.kind {
            if let Some(body) = self.handler_decls.get(rhs) {
                self.local_static_handlers
                    .insert(name.to_string(), Some(body.clone()));
                return;
            }
            if let Some(entry) = self.local_static_handlers.get(rhs).cloned() {
                self.local_static_handlers.insert(name.to_string(), entry);
            }
        }
    }

    /// Pre-resolve an `EffectCall` to its `EffectOpRef`. Uses
    /// `EffectInfo.effect_calls` (typechecker output) for the canonical
    /// effect/op pair; falls back to the source spelling if the call isn't
    /// in the map (defensive — should not happen post-typecheck).
    fn resolve_effect_op(
        &self,
        node_id: NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> EffectOpRef {
        if let Some(resolved) = self.effect_info.effect_calls.get(&node_id) {
            let op_index = self.op_index(&resolved.effect, &resolved.op);
            return EffectOpRef {
                effect: resolved.effect.clone(),
                op: resolved.op.clone(),
                op_index,
            };
        }
        // Fallback: the qualifier (if any) is the effect name in source.
        let effect = qualifier.unwrap_or("").to_string();
        let op_index = self.op_index(&effect, op_name);
        EffectOpRef {
            effect,
            op: op_name.to_string(),
            op_index,
        }
    }
}

// Suppress unused-import lints if any helpers prove unused as the file evolves.
#[allow(dead_code)]
fn _unused_marker(_: &HandlerBody, _: MHandler) {}
