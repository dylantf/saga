//! Per-expression monadic translation.
//!
//! Atomic positions (ANF-guaranteed) collapse into `Atom`; complex positions
//! become structural `MExpr` variants. Every sequencing point is `Bind`.

use super::{BindSpec, DestructureSpec, Translator, fresh_node_id, wrap_binds};
use crate::ast::{
    self, Annotated, Expr, ExprKind, Handler, HandlerBody, HandlerItem, Lit, NodeId, Pat, Stmt,
};
use crate::codegen::monadic::ir::{Atom, EffectOpRef, MArm, MBitSegment, MExpr, MHandler, MVar};
use crate::typechecker::{Type, canonicalize_type_name};

impl<'a> Translator<'a> {
    /// Translate an expression in tail position (its own computation context).
    pub(crate) fn translate_expr(&mut self, e: &Expr) -> MExpr {
        // Strip surface ascriptions transparently; they are erased post-typecheck.
        if let ExprKind::Ascription { expr, .. } = &e.kind {
            return self.translate_expr(expr);
        }

        // Dict-constructor reference at expression position: ANF lifted
        // these bare references into `let v = <ref> in v`. Under uniform
        // CPS the ref's value form is a fun reference, not a tuple, so we
        // emit a zero-arg `App` here — the surrounding `Bind` then binds
        // the materialized tuple to `v`. After this, every downstream
        // consumer of `v` sees `Atom::Var` of an already-materialized
        // dict tuple, restoring the original IR invariant.
        if let Some(app) = self.try_dict_ctor_materialization(e) {
            return app;
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
                if args.is_empty()
                    && let Some(lambda) = self.try_eta_reduced_effect_op_lambda(e, &op)
                {
                    return lambda;
                }
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
                if let Some(split) = self.translate_nested_with_block_handler_prefix(e) {
                    return split;
                }
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
                anon_fields,
            } => MExpr::FieldAccess {
                record: self.expect_atom(expr),
                field: field.clone(),
                record_name: record_name.clone(),
                anon_fields: anon_fields.clone(),
                source: e.id,
            },

            ExprKind::RecordUpdate {
                record,
                fields,
                record_name,
                anon_fields,
            } => MExpr::RecordUpdate {
                record: self.expect_atom(record),
                fields: fields
                    .iter()
                    .map(|(n, _, x)| (n.clone(), self.expect_atom(x)))
                    .collect(),
                record_name: record_name.clone(),
                anon_fields: anon_fields.clone(),
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

            ExprKind::HandlerExpr { body } => {
                let mut effects: Vec<String> = Vec::new();
                for effect_ref in &body.effects {
                    let ename = effect_ref.name.clone();
                    if !effects.contains(&ename) {
                        effects.push(ename);
                    }
                }
                let canonical_effects: Vec<String> = effects
                    .iter()
                    .map(|eff| self.canonical_effect_name(eff))
                    .collect();
                let arms = body
                    .arms
                    .iter()
                    .map(|a| self.translate_handler_arm(&a.node, &canonical_effects))
                    .collect();
                let return_clause = body
                    .return_clause
                    .as_ref()
                    .map(|a| Box::new(self.translate_handler_arm(a, &canonical_effects)));
                MExpr::HandlerValue {
                    effects: canonical_effects,
                    arms,
                    return_clause,
                    source: e.id,
                }
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
                name: self
                    .effect_info
                    .constructors
                    .get(&e.id)
                    .cloned()
                    .unwrap_or_else(|| name.clone()),
                args: Vec::new(),
                source: e.id,
            }),
            ExprKind::QualifiedName { module, name, .. } => {
                // A qualified name resolved to a constructor (e.g.
                // `Json.InvalidShape`) must become a `Ctor` atom — App-folding
                // then builds the tagged tuple. Otherwise it would lower as a
                // uniform-CPS call to a nonexistent `Module:Ctor/(n+2)`.
                if let Some(canonical) = self.effect_info.constructors.get(&e.id) {
                    Some(Atom::Ctor {
                        name: canonical.clone(),
                        args: Vec::new(),
                        source: e.id,
                    })
                } else {
                    Some(Atom::QualifiedRef {
                        module: module.clone(),
                        name: name.clone(),
                        source: e.id,
                    })
                }
            }
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

    /// Detect a bare dict-ctor reference at expression position (post-ANF
    /// lift) and emit a zero-arg `MExpr::App` whose head is the ref atom.
    /// The enclosing `Bind` binds the CPS-call result — the materialized
    /// dict tuple — to a fresh var.
    fn try_dict_ctor_materialization(&self, e: &Expr) -> Option<MExpr> {
        match &e.kind {
            ExprKind::DictRef { name } if self.is_dict_ctor_ref(e.id) => Some(MExpr::App {
                head: Atom::DictRef {
                    name: name.clone(),
                    source: e.id,
                },
                args: Vec::new(),
                source: e.id,
            }),
            ExprKind::QualifiedName { module, name, .. } if self.is_dict_ctor_ref(e.id) => {
                Some(MExpr::App {
                    head: Atom::QualifiedRef {
                        module: module.clone(),
                        name: name.clone(),
                        source: e.id,
                    },
                    args: Vec::new(),
                    source: e.id,
                })
            }
            _ => None,
        }
    }

    fn is_dict_ctor_ref(&self, id: NodeId) -> bool {
        match self.resolution.get(&id) {
            Some(sym) if sym.name.starts_with("__dict_") => matches!(
                sym.kind,
                crate::codegen::resolve::ResolvedCodegenKind::BeamFunction { .. }
                    | crate::codegen::resolve::ResolvedCodegenKind::ExternalFunction { .. }
            ),
            _ => false,
        }
    }

    fn try_eta_reduced_effect_op_lambda(&mut self, e: &Expr, op: &EffectOpRef) -> Option<MExpr> {
        let param_count = self
            .effect_op_param_counts
            .get(&(op.effect.clone(), op.op.clone()))
            .copied()
            .unwrap_or_else(|| {
                self.effect_info
                    .type_at_node
                    .get(&e.id)
                    .map(function_param_count)
                    .unwrap_or(0)
            });
        // The parser rejects 0-parameter effect ops at declaration time
        // (`fun beep : Int` errors; you must write `fun beep : Unit -> Int`),
        // and test fixtures use the same convention. param_count == 0 is
        // therefore unreachable from any valid source. If it ever fires, fall
        // back to a direct `Yield`: building a 0-param lambda here would
        // violate the no-zero-arg-functions invariant and crash the lowerer.
        if param_count == 0 {
            return None;
        }

        let mut params = Vec::with_capacity(param_count);
        let mut args = Vec::with_capacity(param_count);
        for idx in 0..param_count {
            let id = fresh_node_id();
            let name = format!("__eta_effect_arg{}", idx);
            params.push(Pat::Var {
                id,
                name: name.clone(),
                span: e.span,
            });
            args.push(Atom::Var {
                name: MVar {
                    name,
                    id: self.next_mvar_id(),
                },
                source: id,
            });
        }

        Some(MExpr::Pure(Atom::Lambda {
            params,
            body: Box::new(MExpr::Yield {
                op: op.clone(),
                args,
                source: e.id,
            }),
            source: e.id,
        }))
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
            pattern: self.canonicalize_pat_constructors(&arm.pattern),
            guard: arm.guard.as_ref().map(|g| self.translate_expr(g)),
            body: self.translate_expr(&arm.body),
            span: arm.span,
        }
    }

    pub(crate) fn canonicalize_pat_constructors(&self, pat: &ast::Pat) -> ast::Pat {
        use ast::Pat;

        match pat {
            Pat::Constructor {
                id,
                name,
                args,
                span,
            } => Pat::Constructor {
                id: *id,
                name: self
                    .effect_info
                    .constructors
                    .get(id)
                    .cloned()
                    .unwrap_or_else(|| name.clone()),
                args: args
                    .iter()
                    .map(|p| self.canonicalize_pat_constructors(p))
                    .collect(),
                span: *span,
            },
            Pat::Record {
                id,
                name,
                fields,
                rest,
                as_name,
                span,
            } => Pat::Record {
                id: *id,
                name: self
                    .effect_info
                    .constructors
                    .get(id)
                    .cloned()
                    .unwrap_or_else(|| name.clone()),
                fields: fields
                    .iter()
                    .map(|(field, pat)| {
                        (
                            field.clone(),
                            pat.as_ref().map(|p| self.canonicalize_pat_constructors(p)),
                        )
                    })
                    .collect(),
                rest: *rest,
                as_name: as_name.clone(),
                span: *span,
            },
            Pat::AnonRecord {
                id,
                fields,
                rest,
                span,
            } => Pat::AnonRecord {
                id: *id,
                fields: fields
                    .iter()
                    .map(|(field, pat)| {
                        (
                            field.clone(),
                            pat.as_ref().map(|p| self.canonicalize_pat_constructors(p)),
                        )
                    })
                    .collect(),
                rest: *rest,
                span: *span,
            },
            Pat::Tuple { id, elements, span } => Pat::Tuple {
                id: *id,
                elements: elements
                    .iter()
                    .map(|p| self.canonicalize_pat_constructors(p))
                    .collect(),
                span: *span,
            },
            Pat::StringPrefix {
                id,
                prefix,
                rest,
                span,
            } => Pat::StringPrefix {
                id: *id,
                prefix: prefix.clone(),
                rest: Box::new(self.canonicalize_pat_constructors(rest)),
                span: *span,
            },
            Pat::BitStringPat { id, segments, span } => Pat::BitStringPat {
                id: *id,
                segments: segments
                    .iter()
                    .map(|seg| crate::ast::BitSegment {
                        value: self.canonicalize_pat_constructors(&seg.value),
                        size: seg.size.clone(),
                        specs: seg.specs.clone(),
                        span: seg.span,
                    })
                    .collect(),
                span: *span,
            },
            Pat::ListPat { id, elements, span } => Pat::ListPat {
                id: *id,
                elements: elements
                    .iter()
                    .map(|p| self.canonicalize_pat_constructors(p))
                    .collect(),
                span: *span,
            },
            Pat::ConsPat {
                id,
                head,
                tail,
                span,
            } => Pat::ConsPat {
                id: *id,
                head: Box::new(self.canonicalize_pat_constructors(head)),
                tail: Box::new(self.canonicalize_pat_constructors(tail)),
                span: *span,
            },
            Pat::Or { id, patterns, span } => Pat::Or {
                id: *id,
                patterns: patterns
                    .iter()
                    .map(|p| self.canonicalize_pat_constructors(p))
                    .collect(),
                span: *span,
            },
            Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => pat.clone(),
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
        // App-of-Constructor: fold the args into the constructor's own
        // `args` list and yield a pure constructor atom. Without this, the
        // lowerer would emit `apply {'tag'}(arg0, arg1, _Ev, _RK)` —
        // treating the tagged-tuple constructor as a callable function —
        // and `erlc` rejects it with an unbound-variable / bad-function-
        // call error. This matches the old lowerer's `collect_ctor_call`
        // recognizer in `lower/exprs.rs` (which folds `App(...App(Ctor, a),
        // ..., n)` into a single `lower_ctor` call).
        if let Atom::Ctor {
            name,
            args: existing_args,
            source,
        } = head
        {
            debug_assert!(
                existing_args.is_empty(),
                "translate: nullary Constructor expression should produce empty Ctor args"
            );
            return MExpr::Pure(Atom::Ctor { name, args, source });
        }
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
        let saved_effects = self.local_handler_effects.clone();

        let n = stmts.len();
        if n == 0 {
            return MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: fresh_node_id(),
            });
        }

        // Each binding entry carries an optional destructuring pattern: if
        // the source `let` used a non-Var pattern (`let (a, b) = expr`), we
        // bind the value to a synthetic `__pat` var and emit a `case` that
        // matches the pattern at the binding's body position. The
        // destructure is applied right at the binding site so subsequent
        // stmts see the pattern's sub-vars in scope.
        let mut bindings: Vec<BindSpec> = Vec::new();
        let mut tail: Option<MExpr> = None;

        for (idx, ann) in stmts.iter().enumerate() {
            let is_last = idx + 1 == n;
            match &ann.node {
                Stmt::Let {
                    pattern,
                    value,
                    assert,
                    span,
                    ..
                } => {
                    // Record handler-alias info before translating the body.
                    if let Pat::Var { name, id, .. } = pattern {
                        self.record_handler_alias(name, *id, value);
                    }
                    let translated = self.translate_expr(value);
                    let var = self.binder_from_pat(pattern);
                    let destructure = if matches!(pattern, Pat::Var { .. } | Pat::Wildcard { .. }) {
                        None
                    } else {
                        Some(DestructureSpec {
                            pattern: pattern.clone(),
                            assert: *assert,
                            span: *span,
                        })
                    };
                    bindings.push(BindSpec {
                        var,
                        value: translated,
                        destructure,
                    });
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
                    // `let f x = body` inside a block. The name resolves to
                    // a local recursive function (BeamFunction with
                    // erlang_mod = None) — call sites emit `apply
                    // f/arity(args, _Ev, _RK)`, not closure-apply on a
                    // bound var. Emit a dedicated `MExpr::LetFun` so the
                    // lowerer can wrap the rest of the block in a
                    // `CExpr::LetRec` that actually defines `f/arity` for
                    // those calls to resolve against. The lambda body is a
                    // separate computation context.
                    let fun_body = self.translate_expr(body);
                    let rest_stmts = &stmts[idx + 1..];
                    let rest = if rest_stmts.is_empty() {
                        MExpr::Pure(Atom::Lit {
                            value: Lit::Unit,
                            source: fresh_node_id(),
                        })
                    } else {
                        self.translate_block(rest_stmts, block_span)
                    };
                    let letfun = MExpr::LetFun {
                        name: name.clone(),
                        params: params.clone(),
                        body: Box::new(fun_body),
                        rest: Box::new(rest),
                        source: *id,
                    };
                    self.local_static_handlers = saved;
                    self.local_handler_effects = saved_effects;
                    return wrap_binds(bindings, letfun);
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
                        bindings.push(BindSpec {
                            var,
                            value: translated,
                            destructure: None,
                        });
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
        self.local_handler_effects = saved_effects;
        result
    }

    /// Translate `{ let h = ...; body } with h` as
    /// `let h = ... in body with h`. Handler expressions are evaluated
    /// before the handled body, so a handler value produced by the block's
    /// leading bindings must be split out before evidence installation.
    ///
    /// Inline handler composition is desugared into nested `with`
    /// expressions before codegen (`body with pg with tx with console`), so
    /// this looks through the whole nested chain and floats the shared prefix
    /// once.
    fn translate_nested_with_block_handler_prefix(&mut self, expr: &Expr) -> Option<MExpr> {
        let mut handlers: Vec<(&Handler, NodeId, crate::token::Span)> = Vec::new();
        let mut cursor = expr;
        while let ExprKind::With { expr, handler } = &cursor.kind {
            handlers.push((handler.as_ref(), cursor.id, cursor.span));
            cursor = expr;
        }

        let ExprKind::Block { stmts, .. } = &cursor.kind else {
            return None;
        };

        let handler_names: Vec<String> = handlers
            .iter()
            .flat_map(|(handler, _, _)| self.handler_reference_names(handler))
            .collect();
        if handler_names.is_empty() {
            return None;
        }

        let split_idx = stmts
            .iter()
            .enumerate()
            .filter_map(|(idx, ann)| match &ann.node {
                Stmt::Let {
                    pattern: Pat::Var { name, .. },
                    ..
                } if handler_names
                    .iter()
                    .any(|handler_name| handler_name == name) =>
                {
                    Some(idx + 1)
                }
                _ => None,
            })
            .max()?;

        let saved = self.local_static_handlers.clone();
        let saved_effects = self.local_handler_effects.clone();
        let mut bindings: Vec<BindSpec> = Vec::new();

        for ann in &stmts[..split_idx] {
            let Stmt::Let {
                pattern,
                value,
                assert,
                span,
                ..
            } = &ann.node
            else {
                self.local_static_handlers = saved;
                self.local_handler_effects = saved_effects;
                return None;
            };
            if let Pat::Var { name, id, .. } = pattern {
                self.record_handler_alias(name, *id, value);
            }
            let translated = self.translate_expr(value);
            let var = self.binder_from_pat(pattern);
            let destructure = if matches!(pattern, Pat::Var { .. } | Pat::Wildcard { .. }) {
                None
            } else {
                Some(DestructureSpec {
                    pattern: pattern.clone(),
                    assert: *assert,
                    span: *span,
                })
            };
            bindings.push(BindSpec {
                var,
                value: translated,
                destructure,
            });
        }

        let handled_body = if split_idx < stmts.len() {
            self.translate_block(&stmts[split_idx..], cursor.span)
        } else {
            MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: fresh_node_id(),
            })
        };
        let nested =
            handlers
                .into_iter()
                .rev()
                .fold(handled_body, |acc, (handler, source, site_span)| {
                    MExpr::With {
                        handler: self.translate_handler(handler, site_span),
                        body: Box::new(acc),
                        source,
                    }
                });
        let result = wrap_binds(bindings, nested);

        self.local_static_handlers = saved;
        self.local_handler_effects = saved_effects;
        Some(result)
    }

    fn handler_reference_names(&self, handler: &Handler) -> Vec<String> {
        let mut names = Vec::new();
        match handler {
            Handler::Named(named) => names.push(named.name.clone()),
            Handler::Inline { items, .. } => {
                for ann in items {
                    if let HandlerItem::Named(named) = &ann.node {
                        names.push(named.name.clone());
                    }
                }
            }
        }
        names
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
    /// later in the block can be classified as `Static`. For dynamic handler
    /// bindings (conditionals, factory calls, record-field projections),
    /// extract the handled effects from either `let_handler_effects` or the
    /// RHS expression's inferred `Handler E` type so the lowerer can install
    /// evidence.
    fn record_handler_alias(&mut self, name: &str, pat_id: crate::ast::NodeId, value: &Expr) {
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
                return;
            }
        }
        // For dynamic handler bindings (conditionals, factory calls), look up
        // the typechecker's persistent handler info keyed by pattern NodeId.
        if let Some(effects) = self.effect_info.let_handler_effects.get(&pat_id) {
            let canonical: Vec<String> = effects
                .iter()
                .map(|e| self.canonical_effect_name(e))
                .collect();
            if !canonical.is_empty() {
                self.local_handler_effects
                    .insert(name.to_string(), canonical);
                return;
            }
        }

        let canonical = self
            .effect_info
            .type_at_node
            .get(&value.id)
            .or_else(|| self.effect_info.type_at_node.get(&pat_id))
            .map(|ty| self.handler_effects_from_type(ty))
            .or_else(|| self.handler_effects_from_record_field(value))
            .unwrap_or_default();
        if !canonical.is_empty() {
            self.local_handler_effects
                .insert(name.to_string(), canonical);
        }
    }

    pub(crate) fn handler_effects_from_type(&self, ty: &Type) -> Vec<String> {
        let Type::Con(name, args) = ty else {
            return Vec::new();
        };
        if name != canonicalize_type_name("Handler") && name != "Handler" {
            return Vec::new();
        }

        args.iter()
            .filter_map(|arg| match arg {
                Type::Con(effect, _) => Some(self.canonical_effect_name(effect)),
                _ => None,
            })
            .collect()
    }

    fn handler_effects_from_record_field(&self, value: &Expr) -> Option<Vec<String>> {
        let ExprKind::FieldAccess {
            field,
            record_name: Some(record_name),
            ..
        } = &value.kind
        else {
            return None;
        };

        self.effect_info
            .records
            .get(record_name)
            .and_then(|record| record.fields.iter().find(|(name, _)| name == field))
            .map(|(_, ty)| self.handler_effects_from_type(ty))
            .filter(|effects| !effects.is_empty())
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
        // Imported handler bodies can be re-ANF-normalized at the entry
        // module boundary, which may leave their effect-call NodeIds without
        // a matching entry in this module's resolution map. If the source op
        // name is globally unique in the visible effect table, recover the
        // canonical effect from that table instead of emitting the empty
        // sentinel tag that would become `find_evidence(_, '')`.
        let effect = qualifier
            .map(str::to_string)
            .or_else(|| self.unique_effect_for_op(op_name))
            .unwrap_or_default();
        let op_index = self.op_index(&effect, op_name);
        EffectOpRef {
            effect,
            op: op_name.to_string(),
            op_index,
        }
    }

    fn unique_effect_for_op(&self, op_name: &str) -> Option<String> {
        let mut matches: Vec<String> = self
            .effect_ops
            .iter()
            .filter_map(|(effect, ops)| {
                if effect.contains('.') && ops.iter().any(|op| op == op_name) {
                    Some(effect.clone())
                } else {
                    None
                }
            })
            .collect();
        matches.sort();
        matches.dedup();
        match matches.as_slice() {
            [effect] => Some(effect.clone()),
            _ => None,
        }
    }
}

fn function_param_count(ty: &Type) -> usize {
    let mut count = 0;
    let mut cur = ty;
    while let Type::Fun(_, ret, _) = cur {
        count += 1;
        cur = ret;
    }
    count
}

// Suppress unused-import lints if any helpers prove unused as the file evolves.
#[allow(dead_code)]
fn _unused_marker(_: &HandlerBody, _: MHandler) {}
