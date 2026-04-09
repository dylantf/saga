//! Desugaring pass: transforms surface syntax AST into core AST.
//!
//! Runs after parsing and derive expansion, before typechecking.
//! Transforms sugar-preserving AST nodes into the forms the typechecker expects:
//!
//! - `Pipe { segments: [a, b, c] }` -> `App(c, App(b, a))`
//! - `PipeBack { segments: [a, b, c] }` -> `App(App(a, b), c)`
//! - `ComposeForward { segments: [f, g] }` -> `fun _x -> g (f _x)`
//! - `Cons { head, tail }` -> `App(App(Constructor("Cons"), head), tail)`
//! - `ListLit { elements }` -> nested `Cons`/`Nil` chain
//! - `StringInterp { parts }` -> `show(expr) <> literal <> ...`
//! - `ListComprehension { body, qualifiers }` -> `flat_map`/`if`/`let`

use crate::ast::*;
use crate::token::{Span, StringKind};

const TEST_SUGAR_NAMES: &[&str] = &["test", "describe", "skip", "only"];

/// Wrap the body argument of test/describe/skip/only calls in a lambda.
/// The parser produces `App(App(Var("test"), Lit("name")), body)` with the raw
/// block; this function completes the desugaring to `... (fun () -> body)`.
fn wrap_test_body_in_lambda(func: &Expr, arg: &mut Expr) {
    // func must be App(Var("test"|...), Lit(String))
    let ExprKind::App {
        func: head,
        arg: name_arg,
    } = &func.kind
    else {
        return;
    };
    let ExprKind::Var { name } = &head.kind else {
        return;
    };
    if !TEST_SUGAR_NAMES.contains(&name.as_str()) {
        return;
    }
    let ExprKind::Lit {
        value: Lit::String(..),
    } = &name_arg.kind
    else {
        return;
    };
    // Don't double-wrap if already a lambda
    if matches!(&arg.kind, ExprKind::Lambda { .. }) {
        return;
    }
    let body_span = arg.span;
    let body = std::mem::replace(
        arg,
        Expr::synth(body_span, ExprKind::Lit { value: Lit::Unit }),
    );
    *arg = Expr {
        id: NodeId::fresh(),
        span: body_span,
        kind: ExprKind::Lambda {
            params: vec![Pat::Lit {
                id: NodeId::fresh(),
                value: Lit::Unit,
                span: body_span,
            }],
            body: Box::new(body),
        },
    };
}

/// Desugar all surface syntax in a program, in place.
#[allow(clippy::ptr_arg)]
pub fn desugar_program(program: &mut Vec<Decl>) {
    for decl in program.iter_mut() {
        desugar_decl(decl);
    }
}

fn desugar_decl(decl: &mut Decl) {
    match decl {
        Decl::FunBinding {
            params,
            body,
            guard,
            ..
        } => {
            for p in params {
                desugar_pat(p);
            }
            desugar_expr(body);
            if let Some(g) = guard {
                desugar_expr(g);
            }
        }
        Decl::Let { value, .. } | Decl::Val { value, .. } => {
            desugar_expr(value);
        }
        Decl::HandlerDef {
            body,
            recovered_arms,
            ..
        } => {
            for ann_arm in body.arms.iter_mut().chain(recovered_arms.iter_mut()) {
                desugar_expr(&mut ann_arm.node.body);
                if let Some(fb) = &mut ann_arm.node.finally_block {
                    desugar_expr(fb);
                }
            }
            if let Some(rc) = &mut body.return_clause {
                desugar_expr(&mut rc.body);
            }
        }
        Decl::ImplDef { methods, .. } => {
            for ann_method in methods.iter_mut() {
                for p in &mut ann_method.node.params {
                    desugar_pat(p);
                }
                desugar_expr(&mut ann_method.node.body);
            }
        }
        Decl::TopExpr { value, span, .. } => {
            desugar_expr(value);
            // Convert to Let { name: "_" } so the rest of the pipeline sees a normal decl
            let value = std::mem::replace(
                value,
                Expr::synth(*span, ExprKind::Lit { value: Lit::Unit }),
            );
            let s = *span;
            *decl = Decl::Let {
                id: NodeId::fresh(),
                name: "_".to_string(),
                name_span: s,
                annotation: None,
                value,
                span: s,
            };
        }
        // Declarations without expression bodies
        Decl::FunSignature { .. }
        | Decl::TypeDef { .. }
        | Decl::RecordDef { .. }
        | Decl::EffectDef { .. }
        | Decl::TraitDef { .. }
        | Decl::Import { .. }
        | Decl::ModuleDecl { .. }
        | Decl::DictConstructor { .. } => {}
    }
}

fn desugar_expr(expr: &mut Expr) {
    // First, recurse into sub-expressions (bottom-up)
    match &mut expr.kind {
        ExprKind::App { func, arg } => {
            desugar_expr(func);
            desugar_expr(arg);
            // Complete test/describe/skip/only sugar: wrap body in lambda.
            // Parser leaves the body as a raw block; we add fun () -> body here.
            wrap_test_body_in_lambda(func, arg);
        }
        ExprKind::BinOp { left, right, .. } => {
            desugar_expr(left);
            desugar_expr(right);
        }
        ExprKind::UnaryMinus { expr: inner } => desugar_expr(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            desugar_expr(cond);
            desugar_expr(then_branch);
            desugar_expr(else_branch);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            desugar_expr(scrutinee);
            expand_or_patterns(arms);
            for ann_arm in arms {
                desugar_pat(&mut ann_arm.node.pattern);
                if let Some(g) = &mut ann_arm.node.guard {
                    desugar_expr(g);
                }
                desugar_expr(&mut ann_arm.node.body);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for ann_stmt in stmts {
                desugar_stmt(&mut ann_stmt.node);
            }
        }
        ExprKind::Lambda { params, body } => {
            for p in params {
                desugar_pat(p);
            }
            desugar_expr(body);
        }
        ExprKind::FieldAccess { expr: inner, .. } => desugar_expr(inner),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, val) in fields {
                desugar_expr(val);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            desugar_expr(record);
            for (_, _, val) in fields {
                desugar_expr(val);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                desugar_expr(arg);
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            desugar_expr(inner);
            desugar_handler(handler);
            if let Handler::Inline { items, .. } = handler.as_ref()
                && inline_handler_needs_layer_desugaring(items)
            {
                let inner_expr = std::mem::replace(
                    inner,
                    Box::new(Expr::synth(expr.span, ExprKind::Lit { value: Lit::Unit })),
                );
                let handler =
                    std::mem::replace(handler, Box::new(Handler::Named(String::new(), expr.span)));
                *expr = desugar_with_items(expr.id, expr.span, *inner_expr, *handler);
            }
        }
        ExprKind::Resume { value } => desugar_expr(value),
        ExprKind::HandlerExpr { body } => {
            for arm in &mut body.arms {
                desugar_expr(&mut arm.node.body);
                if let Some(fb) = &mut arm.node.finally_block {
                    desugar_expr(fb);
                }
            }
            if let Some(rc) = &mut body.return_clause {
                desugar_expr(&mut rc.body);
            }
        }
        ExprKind::Tuple { elements } => {
            for e in elements {
                desugar_expr(e);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (p, e) in bindings {
                desugar_pat(p);
                desugar_expr(e);
            }
            desugar_expr(success);
            expand_or_patterns(else_arms);
            for ann_arm in else_arms {
                desugar_pat(&mut ann_arm.node.pattern);
                if let Some(g) = &mut ann_arm.node.guard {
                    desugar_expr(g);
                }
                desugar_expr(&mut ann_arm.node.body);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            expand_or_patterns(arms);
            for ann_arm in arms {
                desugar_pat(&mut ann_arm.node.pattern);
                if let Some(g) = &mut ann_arm.node.guard {
                    desugar_expr(g);
                }
                desugar_expr(&mut ann_arm.node.body);
            }
            if let Some((timeout, body)) = after_clause {
                desugar_expr(timeout);
                desugar_expr(body);
            }
        }
        ExprKind::Ascription { expr: inner, .. } => desugar_expr(inner),
        ExprKind::BitString { segments } => {
            for seg in segments {
                desugar_expr(&mut seg.value);
                if let Some(size) = &mut seg.size {
                    desugar_expr(size);
                }
            }
        }

        // Sugar nodes: recurse into children before transforming
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                desugar_expr(&mut seg.node);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                desugar_expr(&mut seg.node);
            }
        }
        ExprKind::Cons { head, tail } => {
            desugar_expr(head);
            desugar_expr(tail);
        }
        ExprKind::ListLit { elements } => {
            for e in elements {
                desugar_expr(e);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    desugar_expr(e);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            desugar_expr(body);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e) | ComprehensionQualifier::Let(_, e) => {
                        desugar_expr(e)
                    }
                    ComprehensionQualifier::Guard(e) => desugar_expr(e),
                }
            }
        }

        // Leaves
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictMethodAccess { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::ForeignCall { .. } => {}
    }

    // Now transform the current node if it's a sugar form
    let span = expr.span;
    match &mut expr.kind {
        ExprKind::Pipe { .. } => {
            // [a, b, c] -> App(c, App(b, a))
            let ExprKind::Pipe { segments, .. } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            let mut iter = segments.into_iter();
            let mut acc = iter.next().unwrap().node;
            for seg in iter {
                let func = seg.node;
                let app_span = acc.span.to(func.span);
                acc = Expr {
                    id: NodeId::fresh(),
                    span: app_span,
                    kind: ExprKind::App {
                        func: Box::new(func),
                        arg: Box::new(acc),
                    },
                };
            }
            *expr = acc;
        }
        ExprKind::BinOpChain { .. } => {
            // [a, b, c] with ops [+, -] -> BinOp(-, BinOp(+, a, b), c)
            let ExprKind::BinOpChain { segments, ops, .. } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            let mut iter = segments.into_iter();
            let mut acc = iter.next().unwrap().node;
            for (seg, op) in iter.zip(ops) {
                let right = seg.node;
                let binop_span = acc.span.to(right.span);
                acc = Expr::synth(
                    binop_span,
                    ExprKind::BinOp {
                        op,
                        left: Box::new(acc),
                        right: Box::new(right),
                    },
                );
            }
            *expr = acc;
        }
        ExprKind::PipeBack { .. } => {
            // [a, b, c] from a <| b <| c -> App(App(a, b), c)
            let ExprKind::PipeBack { segments } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            let mut iter = segments.into_iter();
            let mut acc = iter.next().unwrap().node;
            for seg in iter {
                let arg = seg.node;
                let app_span = acc.span.to(arg.span);
                acc = Expr {
                    id: NodeId::fresh(),
                    span: app_span,
                    kind: ExprKind::App {
                        func: Box::new(acc),
                        arg: Box::new(arg),
                    },
                };
            }
            *expr = acc;
        }
        ExprKind::ComposeForward { .. } => {
            // [f, g, h] from f >> g >> h -> fold left: acc >> next = fun _x -> next(acc(_x))
            let ExprKind::ComposeForward { segments } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            let mut iter = segments.into_iter();
            let mut acc = iter.next().unwrap().node;
            for seg in iter {
                let next = seg.node;
                acc = Expr::synth(span, desugar_compose(acc, next, span));
            }
            *expr = acc;
        }
        ExprKind::Cons { .. } => {
            // x :: xs  ->  App(App(Cons, x), xs)
            let ExprKind::Cons { head, tail } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            let cons = Expr::synth(
                span,
                ExprKind::Constructor {
                    name: "Cons".into(),
                },
            );
            let app1 = Expr::synth(
                span,
                ExprKind::App {
                    func: Box::new(cons),
                    arg: head,
                },
            );
            expr.kind = ExprKind::App {
                func: Box::new(app1),
                arg: tail,
            };
        }
        ExprKind::ListLit { .. } => {
            let ExprKind::ListLit { elements } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            if elements.is_empty() {
                expr.kind = ExprKind::Constructor { name: "Nil".into() };
            } else {
                // Build from right to left: Nil, then wrap each element
                let mut result = Expr::synth(span, ExprKind::Constructor { name: "Nil".into() });
                for elem in elements.into_iter().rev() {
                    let elem_span = elem.span;
                    let cons = Expr::synth(
                        elem_span,
                        ExprKind::Constructor {
                            name: "Cons".into(),
                        },
                    );
                    let app1 = Expr::synth(
                        elem_span,
                        ExprKind::App {
                            func: Box::new(cons),
                            arg: Box::new(elem),
                        },
                    );
                    result = Expr::synth(
                        elem_span.to(span),
                        ExprKind::App {
                            func: Box::new(app1),
                            arg: Box::new(result),
                        },
                    );
                }
                *expr = result;
            }
        }
        ExprKind::StringInterp { .. } => {
            let ExprKind::StringInterp { parts, .. } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            let mut segments: Vec<Expr> = Vec::new();
            for part in parts {
                match part {
                    StringPart::Lit(s) => {
                        if !s.is_empty() {
                            segments.push(Expr::synth(
                                span,
                                ExprKind::Lit {
                                    value: Lit::String(s, StringKind::Normal),
                                },
                            ));
                        }
                    }
                    StringPart::Expr(hole_expr) => {
                        // Wrap in show(expr)
                        let show = Expr::synth(
                            span,
                            ExprKind::Var {
                                name: "show".into(),
                            },
                        );
                        segments.push(Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(show),
                                arg: Box::new(hole_expr),
                            },
                        ));
                    }
                }
            }
            // Fold into left-associative <> chain
            let result = segments.into_iter().reduce(|left, right| {
                Expr::synth(
                    span,
                    ExprKind::BinOp {
                        op: BinOp::Concat,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                )
            });
            expr.kind = result.map(|e| e.kind).unwrap_or(ExprKind::Lit {
                value: Lit::String(String::new(), StringKind::Normal),
            });
        }
        ExprKind::ListComprehension { .. } => {
            let ExprKind::ListComprehension { body, qualifiers } =
                std::mem::replace(&mut expr.kind, ExprKind::Lit { value: Lit::Unit })
            else {
                unreachable!()
            };
            *expr = desugar_comprehension(*body, &qualifiers, span);
        }
        _ => {}
    }
}

fn inline_handler_needs_layer_desugaring(items: &[Annotated<HandlerItem>]) -> bool {
    items
        .iter()
        .any(|ann| matches!(ann.node, HandlerItem::Named(_)))
}

fn desugar_with_items(root_id: NodeId, span: Span, inner: Expr, handler: Handler) -> Expr {
    let Handler::Inline { items, .. } = handler else {
        return Expr {
            id: root_id,
            span,
            kind: ExprKind::With {
                expr: Box::new(inner),
                handler: Box::new(handler),
            },
        };
    };

    let layers = handler_items_to_layers(items);
    let mut acc = inner;
    for layer in layers {
        acc = Expr::synth(
            span,
            ExprKind::With {
                expr: Box::new(acc),
                handler: Box::new(layer),
            },
        );
    }
    acc.id = root_id;
    acc.span = span;
    acc
}

fn handler_items_to_layers(items: Vec<Annotated<HandlerItem>>) -> Vec<Handler> {
    let mut layers = Vec::new();
    let mut inline_items = Vec::new();

    for item in items {
        match item.node {
            HandlerItem::Named(named_ref) => {
                if !inline_items.is_empty() {
                    layers.push(Handler::Inline {
                        items: std::mem::take(&mut inline_items),
                        dangling_trivia: vec![],
                    });
                }
                layers.push(Handler::Named(named_ref.name, named_ref.span));
            }
            HandlerItem::Arm(_) | HandlerItem::Return(_) => inline_items.push(item),
        }
    }

    if !inline_items.is_empty() {
        layers.push(Handler::Inline {
            items: inline_items,
            dangling_trivia: vec![],
        });
    }

    layers
}

fn desugar_stmt(stmt: &mut Stmt) {
    match stmt {
        Stmt::Let { pattern, value, .. } => {
            desugar_pat(pattern);
            desugar_expr(value);
        }
        Stmt::LetFun {
            params,
            body,
            guard,
            ..
        } => {
            for p in params {
                desugar_pat(p);
            }
            desugar_expr(body);
            if let Some(g) = guard {
                desugar_expr(g);
            }
        }

        Stmt::Expr(e) => desugar_expr(e),
    }
}

/// Expand or-patterns in a list of case arms.
/// `A | B when g -> body` becomes `A when g -> body`, `B when g -> body`.
fn expand_or_patterns(arms: &mut Vec<Annotated<CaseArm>>) {
    let mut i = 0;
    while i < arms.len() {
        if let Pat::Or { patterns, .. } = &arms[i].node.pattern {
            let count = patterns.len();
            let patterns = patterns.clone();
            let original = arms.remove(i);
            for (j, pat) in patterns.into_iter().enumerate() {
                let mut arm = original.clone();
                arm.node.pattern = pat;
                arms.insert(i + j, arm);
            }
            i += count;
        } else {
            i += 1;
        }
    }
}

fn desugar_pat(pat: &mut Pat) {
    // Recurse first (bottom-up)
    match pat {
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => {}
        Pat::Constructor { args, .. } => {
            for a in args {
                desugar_pat(a);
            }
        }
        Pat::Record { fields, .. } => {
            for (_, alias) in fields {
                if let Some(p) = alias {
                    desugar_pat(p);
                }
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (_, alias) in fields {
                if let Some(p) = alias {
                    desugar_pat(p);
                }
            }
        }
        Pat::Tuple { elements, .. } => {
            for e in elements {
                desugar_pat(e);
            }
        }
        Pat::StringPrefix { rest, .. } => desugar_pat(rest),
        Pat::BitStringPat { segments, .. } => {
            for seg in segments {
                desugar_pat(&mut seg.value);
            }
        }
        Pat::ListPat { elements, .. } => {
            for e in elements {
                desugar_pat(e);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            desugar_pat(head);
            desugar_pat(tail);
        }
        Pat::Or { patterns, .. } => {
            for p in patterns {
                desugar_pat(p);
            }
        }
    }

    // Transform
    match pat {
        Pat::ListPat { .. } => {
            let Pat::ListPat { elements, span, .. } = std::mem::replace(
                pat,
                Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: Span { start: 0, end: 0 },
                },
            ) else {
                unreachable!()
            };
            // Build from right to left: Nil, then wrap each element in Cons
            let mut result = Pat::Constructor {
                id: NodeId::fresh(),
                name: "Nil".to_string(),
                args: vec![],
                span,
            };
            for elem in elements.into_iter().rev() {
                result = Pat::Constructor {
                    id: NodeId::fresh(),
                    name: "Cons".to_string(),
                    args: vec![elem, result],
                    span,
                };
            }
            *pat = result;
        }
        Pat::ConsPat { .. } => {
            let Pat::ConsPat {
                head, tail, span, ..
            } = std::mem::replace(
                pat,
                Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: Span { start: 0, end: 0 },
                },
            )
            else {
                unreachable!()
            };
            *pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: "Cons".to_string(),
                args: vec![*head, *tail],
                span,
            };
        }
        _ => {}
    }
}

fn desugar_handler(handler: &mut Handler) {
    match handler {
        Handler::Named(..) => {}
        Handler::Inline { items, .. } => {
            for ann_item in items {
                match &mut ann_item.node {
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        desugar_expr(&mut arm.body);
                        if let Some(fb) = &mut arm.finally_block {
                            desugar_expr(fb);
                        }
                    }
                    HandlerItem::Named(_) => {}
                }
            }
        }
    }
}

// --- Desugaring helpers ---

/// `first >> second` -> `fun _x -> second (first _x)`
fn desugar_compose(first: Expr, second: Expr, span: Span) -> ExprKind {
    let param = Pat::Var {
        id: NodeId::fresh(),
        name: "_x".into(),
        span,
    };
    let arg = Expr::synth(span, ExprKind::Var { name: "_x".into() });
    let inner = Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(first),
            arg: Box::new(arg),
        },
    );
    let body = Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(second),
            arg: Box::new(inner),
        },
    );
    ExprKind::Lambda {
        params: vec![param],
        body: Box::new(body),
    }
}

/// Build Cons(elem, Nil) -- a singleton list.
fn make_singleton_list(elem: Expr, span: Span) -> Expr {
    let nil = Expr::synth(span, ExprKind::Constructor { name: "Nil".into() });
    let cons = Expr::synth(
        span,
        ExprKind::Constructor {
            name: "Cons".into(),
        },
    );
    let app1 = Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(cons),
            arg: Box::new(elem),
        },
    );
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(app1),
            arg: Box::new(nil),
        },
    )
}

/// Recursively desugar list comprehension qualifiers.
fn desugar_comprehension(body: Expr, qualifiers: &[ComprehensionQualifier], span: Span) -> Expr {
    if qualifiers.is_empty() {
        // Base case: [e] ==> Cons(e, Nil)
        return make_singleton_list(body, span);
    }

    match &qualifiers[0] {
        ComprehensionQualifier::Generator(pat, source) => {
            // [e | p <- l, Q] ==> flat_map (fun p -> [e | Q]) l
            let inner = desugar_comprehension(body, &qualifiers[1..], span);
            let lambda = Expr::synth(
                span,
                ExprKind::Lambda {
                    params: vec![pat.clone()],
                    body: Box::new(inner),
                },
            );
            let flat_map = Expr::synth(
                span,
                ExprKind::QualifiedName {
                    module: "List".into(),
                    name: "flat_map".into(),
                    canonical_module: None,
                },
            );
            let app1 = Expr::synth(
                span,
                ExprKind::App {
                    func: Box::new(flat_map),
                    arg: Box::new(lambda),
                },
            );
            Expr::synth(
                span,
                ExprKind::App {
                    func: Box::new(app1),
                    arg: Box::new(source.clone()),
                },
            )
        }
        ComprehensionQualifier::Guard(guard) => {
            // [e | g, Q] ==> if g then [e | Q] else []
            let then_branch = desugar_comprehension(body, &qualifiers[1..], span);
            let else_branch = Expr::synth(span, ExprKind::Constructor { name: "Nil".into() });
            Expr::synth(
                span,
                ExprKind::If {
                    cond: Box::new(guard.clone()),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                    multiline: false,
                },
            )
        }
        ComprehensionQualifier::Let(pat, value) => {
            // [e | let p = v, Q] ==> { let p = v; [e | Q] }
            let inner = desugar_comprehension(body, &qualifiers[1..], span);
            Expr::synth(
                span,
                ExprKind::Block {
                    dangling_trivia: vec![],
                    stmts: vec![
                        Annotated::bare(Stmt::Let {
                            pattern: pat.clone(),
                            annotation: None,
                            value: value.clone(),
                            assert: false,
                            span,
                        }),
                        Annotated::bare(Stmt::Expr(inner)),
                    ],
                },
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn parse_and_desugar(source: &str) -> Expr {
        let tokens = Lexer::new(source).lex().unwrap();
        let mut expr = Parser::new(tokens).parse_expr(0).unwrap();
        desugar_expr(&mut expr);
        expr
    }

    /// Helper: unwrap one With layer, returning (inner_expr, handler).
    fn unwrap_with(expr: &Expr) -> (&Expr, &Handler) {
        match &expr.kind {
            ExprKind::With { expr, handler } => (expr, handler),
            _ => panic!("expected With, got {:?}", expr.kind),
        }
    }

    #[test]
    fn single_named_desugars_to_named_handler() {
        let expr = parse_and_desugar("run () with {console_log}");
        let (_, handler) = unwrap_with(&expr);
        assert!(matches!(handler, Handler::Named(name, _) if name == "console_log"));
    }

    #[test]
    fn single_inline_arm_stays_inline() {
        let expr = parse_and_desugar("run () with { fail msg = 0 }");
        let (_, handler) = unwrap_with(&expr);
        match handler {
            Handler::Inline { items, .. } => {
                assert_eq!(items.len(), 1);
                assert!(matches!(&items[0].node, HandlerItem::Arm(a) if a.op_name == "fail"));
            }
            _ => panic!("expected Inline handler"),
        }
    }

    #[test]
    fn named_plus_inline_splits_into_nested_with() {
        // with {console_log, fail msg = 0, return value = Ok value}
        // => (expr with console_log) with { fail msg = 0, return value = Ok value }
        let expr =
            parse_and_desugar("run () with {console_log, fail msg = 0, return value = Ok value}");

        let (inner, outer_handler) = unwrap_with(&expr);
        // Outer: inline block with fail arm + return
        match outer_handler {
            Handler::Inline { items, .. } => {
                assert_eq!(items.len(), 2);
                assert!(matches!(&items[0].node, HandlerItem::Arm(a) if a.op_name == "fail"));
                assert!(matches!(&items[1].node, HandlerItem::Return(_)));
            }
            _ => panic!("expected Inline handler"),
        }

        // Inner: named handler
        let (_, inner_handler) = unwrap_with(inner);
        assert!(matches!(inner_handler, Handler::Named(name, _) if name == "console_log"));
    }

    #[test]
    fn named_between_inline_groups_creates_three_layers() {
        // with {fail msg = 0, return v = Ok v, console_log, log msg = resume ()}
        // => ((expr with {fail, return}) with console_log) with {log}
        let expr = parse_and_desugar(
            "run () with {fail msg = 0, return value = Ok value, console_log, log msg = resume ()}",
        );

        let (mid, outer_handler) = unwrap_with(&expr);
        match outer_handler {
            Handler::Inline { items, .. } => {
                assert_eq!(items.len(), 1);
                assert!(matches!(&items[0].node, HandlerItem::Arm(a) if a.op_name == "log"));
            }
            _ => panic!("expected outer Inline"),
        }

        let (inner, mid_handler) = unwrap_with(mid);
        assert!(matches!(mid_handler, Handler::Named(name, _) if name == "console_log"));

        let (_, inner_handler) = unwrap_with(inner);
        match inner_handler {
            Handler::Inline { items, .. } => {
                assert_eq!(items.len(), 2);
                assert!(matches!(&items[0].node, HandlerItem::Arm(a) if a.op_name == "fail"));
                assert!(matches!(&items[1].node, HandlerItem::Return(_)));
            }
            _ => panic!("expected inner Inline"),
        }
    }

    #[test]
    fn all_inline_items_no_desugaring() {
        // No named refs => no splitting, just one Inline layer
        let expr = parse_and_desugar("run () with { fail msg = 0, return value = Ok value }");
        let (_, handler) = unwrap_with(&expr);
        match handler {
            Handler::Inline { items, .. } => {
                assert_eq!(items.len(), 2);
                assert!(matches!(&items[0].node, HandlerItem::Arm(_)));
                assert!(matches!(&items[1].node, HandlerItem::Return(_)));
            }
            _ => panic!("expected Inline handler"),
        }
    }
}
