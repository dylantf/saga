//! Handler-arm syntactic analysis.
//!
//! Classifies each handler-arm body by how it uses `resume`, so effect
//! optimization can decide which rewrites are eligible.
//!
//! Stage 8.5 of the uniform-effect-translation refactor. Purely syntactic;
//! runs on elaborated `ast::Program` before ANF / monadic translation.
//!
//! See `docs/planning/uniform-effect-translation/` for the architectural
//! contract this file participates in. In particular:
//!   - Translator is dumb-and-uniform (`Bind` everywhere).
//!   - Effect optimization is smart-and-safe; consults the verdicts here.
//!   - A false `TailResumptive` is a miscompile; we err toward `Multishot`.

use std::collections::HashMap;

use crate::ast::{
    CaseArm, ComprehensionQualifier, Decl, Expr, ExprKind, Handler, HandlerArm, HandlerBody,
    HandlerItem, NodeId, Program, Stmt, StringPart,
};

/// How a handler arm uses `resume`. Conservative: when in doubt, `Multishot`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResumptionKind {
    /// Every tail position of the arm body is `resume`, and there are no
    /// non-tail `resume`s. Eligible for the direct-call rewrite.
    TailResumptive,
    /// All `resume`s are in tail position (so at most one fires per execution
    /// path), but some tail paths do not resume (abort cases). Eligible for
    /// bind-collapse across the resume.
    OneShot,
    /// Anything else (resume in non-tail position, inside a lambda, etc.).
    /// Forces the full handler machinery.
    Multishot,
}

/// Output of stage 8.5. Keyed by the `HandlerArm.id` of each arm we saw.
#[derive(Debug, Clone, Default)]
pub struct HandlerAnalysis {
    pub resumption: HashMap<NodeId, ResumptionKind>,
    // NOTE: The planning doc reserves a `catalog: HashMap<NodeId, HandlerMeta>`
    // field for adjacent metadata (parent handler, effect/op names, ...). We
    // omit it until a real consumer needs it; adding empty plumbing now would
    // violate the "fields with a named consumer" rule in the agent guide.
}

/// Classify every handler arm reachable from `p`.
pub fn analyze(p: &Program) -> HandlerAnalysis {
    let mut out = HandlerAnalysis::default();
    for decl in p {
        visit_decl(decl, &mut out);
    }
    out
}

// ---------------------------------------------------------------------------
// Traversal: locate every handler arm in the program.
// ---------------------------------------------------------------------------

fn visit_decl(decl: &Decl, out: &mut HandlerAnalysis) {
    match decl {
        Decl::FunBinding { body, guard, .. } => {
            visit_expr_for_arms(body, out);
            if let Some(g) = guard {
                visit_expr_for_arms(g, out);
            }
        }
        Decl::Let { value, .. } | Decl::Val { value, .. } => visit_expr_for_arms(value, out),
        Decl::HandlerDef { body, .. } => visit_handler_body(body, out),
        Decl::DictConstructor { methods, .. } => {
            for m in methods {
                visit_expr_for_arms(m, out);
            }
        }
        // No expression bodies to descend into.
        Decl::FunSignature { .. }
        | Decl::TypeDef { .. }
        | Decl::TypeAlias { .. }
        | Decl::RecordDef { .. }
        | Decl::EffectDef { .. }
        | Decl::TraitDef { .. }
        | Decl::ImplDef { .. }
        | Decl::Import { .. }
        | Decl::ModuleDecl { .. } => {}
    }
}

fn visit_handler_body(body: &HandlerBody, out: &mut HandlerAnalysis) {
    for arm in &body.arms {
        classify_arm(&arm.node, out);
    }
    if let Some(ret) = &body.return_clause {
        // Return clauses don't `resume` — but classify so callers find them.
        classify_arm(ret, out);
    }
}

fn classify_arm(arm: &HandlerArm, out: &mut HandlerAnalysis) {
    let kind = classify_body(&arm.body);
    out.resumption.insert(arm.id, kind);
    // Recurse: arm bodies can themselves contain `with`, `handler`, etc.
    visit_expr_for_arms(&arm.body, out);
    if let Some(fin) = &arm.finally_block {
        visit_expr_for_arms(fin, out);
    }
}

/// Walk an expression looking for nested handler arms (HandlerExpr / With /
/// arm bodies). Does *not* itself perform classification — that's
/// `classify_arm`'s job.
fn visit_expr_for_arms(e: &Expr, out: &mut HandlerAnalysis) {
    match &e.kind {
        ExprKind::HandlerExpr { body } => visit_handler_body(body, out),
        ExprKind::With { expr, handler } => {
            visit_expr_for_arms(expr, out);
            match handler.as_ref() {
                Handler::Named(_) => {}
                Handler::Inline { items, .. } => {
                    for ann in items {
                        match &ann.node {
                            HandlerItem::Named(_) => {}
                            HandlerItem::Arm(a) | HandlerItem::Return(a) => classify_arm(a, out),
                        }
                    }
                }
            }
        }

        // Recurse into every sub-expression that might house handler arms.
        ExprKind::App { func, arg, .. } => {
            visit_expr_for_arms(func, out);
            visit_expr_for_arms(arg, out);
        }
        ExprKind::BinOp { left, right, .. } => {
            visit_expr_for_arms(left, out);
            visit_expr_for_arms(right, out);
        }
        ExprKind::UnaryMinus { expr } | ExprKind::Ascription { expr, .. } => {
            visit_expr_for_arms(expr, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            visit_expr_for_arms(cond, out);
            visit_expr_for_arms(then_branch, out);
            visit_expr_for_arms(else_branch, out);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            visit_expr_for_arms(scrutinee, out);
            for a in arms {
                visit_case_arm(&a.node, out);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for s in stmts {
                visit_stmt_for_arms(&s.node, out);
            }
        }
        ExprKind::Lambda { body, .. } => visit_expr_for_arms(body, out),
        ExprKind::FieldAccess { expr, .. } => visit_expr_for_arms(expr, out),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            for (_, _, e) in fields {
                visit_expr_for_arms(e, out);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            visit_expr_for_arms(record, out);
            for (_, _, e) in fields {
                visit_expr_for_arms(e, out);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for a in args {
                visit_expr_for_arms(a, out);
            }
        }
        ExprKind::Resume { value } => visit_expr_for_arms(value, out),
        ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
            for e in elements {
                visit_expr_for_arms(e, out);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, e) in bindings {
                visit_expr_for_arms(e, out);
            }
            visit_expr_for_arms(success, out);
            for a in else_arms {
                visit_case_arm(&a.node, out);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for a in arms {
                visit_case_arm(&a.node, out);
            }
            if let Some((t, b)) = after_clause {
                visit_expr_for_arms(t, out);
                visit_expr_for_arms(b, out);
            }
        }
        ExprKind::BitString { segments } => {
            for seg in segments {
                visit_expr_for_arms(&seg.value, out);
                if let Some(sz) = &seg.size {
                    visit_expr_for_arms(sz, out);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for s in segments {
                visit_expr_for_arms(&s.node, out);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for s in segments {
                visit_expr_for_arms(&s.node, out);
            }
        }
        ExprKind::Cons { head, tail } => {
            visit_expr_for_arms(head, out);
            visit_expr_for_arms(tail, out);
        }
        ExprKind::StringInterp { parts, .. } => {
            for p in parts {
                if let StringPart::Expr(e) = p {
                    visit_expr_for_arms(e, out);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            visit_expr_for_arms(body, out);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Let(_, e)
                    | ComprehensionQualifier::Guard(e) => visit_expr_for_arms(e, out),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for a in args {
                visit_expr_for_arms(a, out);
            }
        }
        ExprKind::DictMethodAccess { dict, .. } => visit_expr_for_arms(dict, out),

        // Leaves — nothing to visit.
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}
    }
}

fn visit_case_arm(arm: &CaseArm, out: &mut HandlerAnalysis) {
    if let Some(g) = &arm.guard {
        visit_expr_for_arms(g, out);
    }
    visit_expr_for_arms(&arm.body, out);
}

fn visit_stmt_for_arms(s: &Stmt, out: &mut HandlerAnalysis) {
    match s {
        Stmt::Let { value, .. } => visit_expr_for_arms(value, out),
        Stmt::LetFun { body, guard, .. } => {
            visit_expr_for_arms(body, out);
            if let Some(g) = guard {
                visit_expr_for_arms(g, out);
            }
        }
        Stmt::Expr(e) => visit_expr_for_arms(e, out),
    }
}

// ---------------------------------------------------------------------------
// Per-arm classification.
// ---------------------------------------------------------------------------

fn classify_body(body: &Expr) -> ResumptionKind {
    let mut tails: Vec<&Expr> = Vec::new();
    collect_tail_positions(body, &mut tails);

    let total_resumes = count_resumes_anywhere(body);
    let tail_resumes = tails
        .iter()
        .filter(|e| matches!(e.kind, ExprKind::Resume { .. }))
        .count();
    let tail_count = tails.len();

    // If any `resume` appears outside a tail position — including inside a
    // lambda body (captured continuation) — we cannot prove single-use.
    if tail_resumes < total_resumes {
        return ResumptionKind::Multishot;
    }

    // All resumes are tail. Are *all* tail positions resume?
    if tail_count > 0 && tail_resumes == tail_count {
        ResumptionKind::TailResumptive
    } else {
        // Either no resumes (arm always aborts) or a mix of resume/non-resume
        // tail arms (some paths abort). Both are single-shot upper-bounded.
        ResumptionKind::OneShot
    }
}

/// Push the tail-position sub-expressions of `e` into `out`.
///
/// Recursion shape (from the planning doc): descend through `if`-branches,
/// `case`-arms, block tails, `do` success/else-arms. Do **not** descend into
/// lambda bodies (those are inner computations) or into the *scrutinee*,
/// *bindings*, or `cond` parts of compound forms.
fn collect_tail_positions<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &e.kind {
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_tail_positions(then_branch, out);
            collect_tail_positions(else_branch, out);
        }
        ExprKind::Case { arms, .. } => {
            for a in arms {
                collect_tail_positions(&a.node.body, out);
            }
        }
        ExprKind::Block { stmts, .. } => match stmts.last() {
            Some(last) => match &last.node {
                Stmt::Expr(tail) => collect_tail_positions(tail, out),
                // Block ending in a `let` / `let fun` has no value-producing
                // tail expression — treat the block itself as its own opaque
                // tail. This is conservative; such blocks are rare.
                Stmt::Let { .. } | Stmt::LetFun { .. } => out.push(e),
            },
            None => out.push(e),
        },
        ExprKind::Do {
            success, else_arms, ..
        } => {
            collect_tail_positions(success, out);
            for a in else_arms {
                collect_tail_positions(&a.node.body, out);
            }
        }
        ExprKind::Ascription { expr, .. } => collect_tail_positions(expr, out),

        // Every other shape is its own tail position. Crucially this includes
        // `Lambda` (its body is *not* in our tail context) and `Resume`
        // (which is what we're looking for).
        _ => out.push(e),
    }
}

/// Count every `resume` in `e`, descending through *all* sub-expressions
/// including lambda bodies. A `resume` inside a lambda is a captured
/// continuation and disqualifies tail-resumptive / one-shot classification.
fn count_resumes_anywhere(e: &Expr) -> usize {
    let mut n = 0;
    walk_count(e, &mut n);
    n
}

fn walk_count(e: &Expr, n: &mut usize) {
    match &e.kind {
        ExprKind::Resume { value } => {
            *n += 1;
            walk_count(value, n);
        }

        ExprKind::App { func, arg, .. } => {
            walk_count(func, n);
            walk_count(arg, n);
        }
        ExprKind::BinOp { left, right, .. } => {
            walk_count(left, n);
            walk_count(right, n);
        }
        ExprKind::UnaryMinus { expr } | ExprKind::Ascription { expr, .. } => walk_count(expr, n),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            walk_count(cond, n);
            walk_count(then_branch, n);
            walk_count(else_branch, n);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            walk_count(scrutinee, n);
            for a in arms {
                if let Some(g) = &a.node.guard {
                    walk_count(g, n);
                }
                walk_count(&a.node.body, n);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for s in stmts {
                match &s.node {
                    Stmt::Let { value, .. } => walk_count(value, n),
                    Stmt::LetFun { body, guard, .. } => {
                        walk_count(body, n);
                        if let Some(g) = guard {
                            walk_count(g, n);
                        }
                    }
                    Stmt::Expr(e) => walk_count(e, n),
                }
            }
        }
        // Resumes inside a lambda body are *captured into a closure value*.
        // We still count them, so they contribute to `total_resumes` while
        // never contributing to `tail_resumes` (the lambda itself is the
        // tail position, not its body). This forces Multishot, which is the
        // correctness-preserving direction. Same rationale for `LetFun`
        // below.
        ExprKind::Lambda { body, .. } => walk_count(body, n),
        ExprKind::FieldAccess { expr, .. } => walk_count(expr, n),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            for (_, _, e) in fields {
                walk_count(e, n);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            walk_count(record, n);
            for (_, _, e) in fields {
                walk_count(e, n);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for a in args {
                walk_count(a, n);
            }
        }
        // `With`: we count resumes in the with-body (they belong to the
        // *enclosing* arm's continuation), but NOT inside the inline handler
        // arm bodies — those have their own resume context.
        ExprKind::With { expr, handler } => {
            walk_count(expr, n);
            // Mirror `Expr::contains_resume`: don't look through arm bodies.
            let _ = handler;
        }
        // Same logic: a `handler { ... }` expression value introduces a new
        // resume context for each arm; those don't count for the outer.
        ExprKind::HandlerExpr { .. } => {}
        ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
            for e in elements {
                walk_count(e, n);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, e) in bindings {
                walk_count(e, n);
            }
            walk_count(success, n);
            for a in else_arms {
                if let Some(g) = &a.node.guard {
                    walk_count(g, n);
                }
                walk_count(&a.node.body, n);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for a in arms {
                if let Some(g) = &a.node.guard {
                    walk_count(g, n);
                }
                walk_count(&a.node.body, n);
            }
            if let Some((t, b)) = after_clause {
                walk_count(t, n);
                walk_count(b, n);
            }
        }
        ExprKind::BitString { segments } => {
            for seg in segments {
                walk_count(&seg.value, n);
                if let Some(sz) = &seg.size {
                    walk_count(sz, n);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for s in segments {
                walk_count(&s.node, n);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for s in segments {
                walk_count(&s.node, n);
            }
        }
        ExprKind::Cons { head, tail } => {
            walk_count(head, n);
            walk_count(tail, n);
        }
        ExprKind::StringInterp { parts, .. } => {
            for p in parts {
                if let StringPart::Expr(e) = p {
                    walk_count(e, n);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            walk_count(body, n);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Let(_, e)
                    | ComprehensionQualifier::Guard(e) => walk_count(e, n),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for a in args {
                walk_count(a, n);
            }
        }
        ExprKind::DictMethodAccess { dict, .. } => walk_count(dict, n),

        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Annotated, BinOp, Lit, Pat};
    use crate::token::Span;

    fn sp() -> Span {
        Span { start: 0, end: 0 }
    }
    fn ev(k: ExprKind) -> Expr {
        Expr::synth(sp(), k)
    }
    fn lit_int(n: i64) -> Expr {
        ev(ExprKind::Lit {
            value: Lit::Int(n.to_string(), n),
        })
    }
    fn var(name: &str) -> Expr {
        ev(ExprKind::Var {
            name: name.into(),
        })
    }
    fn resume(v: Expr) -> Expr {
        ev(ExprKind::Resume { value: Box::new(v) })
    }
    fn iff(c: Expr, t: Expr, e: Expr) -> Expr {
        ev(ExprKind::If {
            cond: Box::new(c),
            then_branch: Box::new(t),
            else_branch: Box::new(e),
            multiline: false,
        })
    }
    fn lam(param: &str, body: Expr) -> Expr {
        ev(ExprKind::Lambda {
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: param.into(),
                span: sp(),
            }],
            body: Box::new(body),
        })
    }
    fn block(stmts: Vec<Stmt>) -> Expr {
        ev(ExprKind::Block {
            stmts: stmts.into_iter().map(Annotated::bare).collect(),
            dangling_trivia: vec![],
        })
    }
    fn arm(body: Expr) -> HandlerArm {
        HandlerArm {
            id: NodeId::fresh(),
            op_name: "op".into(),
            qualifier: None,
            params: vec![],
            body: Box::new(body),
            finally_block: None,
            span: sp(),
        }
    }

    #[test]
    fn tail_resumptive_simple() {
        // body: `resume x`
        let a = arm(resume(var("x")));
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::TailResumptive);
    }

    #[test]
    fn tail_resumptive_both_branches() {
        // if c then resume 1 else resume 2
        let body = iff(var("c"), resume(lit_int(1)), resume(lit_int(2)));
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::TailResumptive);
    }

    #[test]
    fn one_shot_abort_branch() {
        // if c then resume 1 else 0
        let body = iff(var("c"), resume(lit_int(1)), lit_int(0));
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::OneShot);
    }

    #[test]
    fn one_shot_no_resume_is_abort() {
        // body: `0` (handler always aborts the continuation)
        let a = arm(lit_int(0));
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::OneShot);
    }

    #[test]
    fn multishot_resume_in_non_tail_position() {
        // body: `(resume x) + 1`  — resume is not in tail position.
        let body = ev(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(resume(var("x"))),
            right: Box::new(lit_int(1)),
        });
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::Multishot);
    }

    #[test]
    fn multishot_resume_captured_in_lambda() {
        // body: `fun k -> resume k` — resume captured in lambda body.
        // The lambda itself is the tail, not the inner resume.
        let body = lam("k", resume(var("k")));
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::Multishot);
    }

    #[test]
    fn tail_recursion_does_not_descend_into_lambda_body() {
        // body: `fun x -> resume x`. Tail positions should be just [Lambda],
        // and the lambda itself is not a Resume — so tail_resumes = 0.
        // (Combined with all_resumes = 1 from the inner walk, this triggers
        // Multishot.)
        let body = lam("x", resume(var("x")));
        let mut tails: Vec<&Expr> = vec![];
        collect_tail_positions(&body, &mut tails);
        assert_eq!(tails.len(), 1);
        assert!(matches!(tails[0].kind, ExprKind::Lambda { .. }));
    }

    #[test]
    fn block_tail_is_last_expr() {
        // { let _ = x; resume y }
        let body = block(vec![
            Stmt::Let {
                pattern: Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: sp(),
                },
                annotation: None,
                value: var("x"),
                assert: false,
                span: sp(),
            },
            Stmt::Expr(resume(var("y"))),
        ]);
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::TailResumptive);
    }

    #[test]
    fn multishot_resume_inside_recursive_letfun() {
        // arm body:
        //   { let rec loop xs = case xs of
        //         []   -> resume done
        //       | h::t -> loop t
        //     loop my_list }
        //
        // Operationally `resume` fires at most once, but syntactically it's
        // captured inside `loop`'s closure body. The arm's tail position is
        // `loop my_list`, not `resume done`. Must NOT be TailResumptive.
        let loop_body = ev(ExprKind::Case {
            scrutinee: Box::new(var("xs")),
            arms: vec![
                Annotated::bare(CaseArm {
                    pattern: Pat::Wildcard {
                        id: NodeId::fresh(),
                        span: sp(),
                    },
                    guard: None,
                    body: resume(var("done")),
                    span: sp(),
                }),
                Annotated::bare(CaseArm {
                    pattern: Pat::Wildcard {
                        id: NodeId::fresh(),
                        span: sp(),
                    },
                    guard: None,
                    body: ev(ExprKind::App {
                        func: Box::new(var("loop")),
                        arg: Box::new(var("t")),
                    }),
                    span: sp(),
                }),
            ],
            dangling_trivia: vec![],
        });
        let body = block(vec![
            Stmt::LetFun {
                id: NodeId::fresh(),
                name: "loop".into(),
                name_span: sp(),
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: "xs".into(),
                    span: sp(),
                }],
                guard: None,
                body: loop_body,
                span: sp(),
            },
            Stmt::Expr(ev(ExprKind::App {
                func: Box::new(var("loop")),
                arg: Box::new(var("my_list")),
            })),
        ]);
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::Multishot);
    }

    #[test]
    fn multishot_resume_inside_block_let_value() {
        // { let _ = resume x; 0 }  — resume in stmt value (non-tail).
        let body = block(vec![
            Stmt::Let {
                pattern: Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: sp(),
                },
                annotation: None,
                value: resume(var("x")),
                assert: false,
                span: sp(),
            },
            Stmt::Expr(lit_int(0)),
        ]);
        let a = arm(body);
        let mut out = HandlerAnalysis::default();
        classify_arm(&a, &mut out);
        assert_eq!(out.resumption[&a.id], ResumptionKind::Multishot);
    }
}
