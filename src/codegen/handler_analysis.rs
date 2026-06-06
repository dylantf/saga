//! Handler-arm syntactic analysis for optimizer facts.
//!
//! This pass classifies how each handler arm uses `resume`. It is intentionally
//! conservative: a false `TailResumptive` can miscompile, while a missed
//! optimization only leaves the normal evidence/CPS path in place.

use std::collections::HashMap;

use crate::ast::{
    CaseArm, ComprehensionQualifier, Decl, Expr, ExprKind, Handler, HandlerArm, HandlerBody,
    HandlerItem, NodeId, Program, Stmt, StringPart,
};

/// How a handler arm uses `resume`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResumptionKind {
    /// Every tail position of the arm body is `resume`, and no `resume`
    /// appears outside tail position.
    TailResumptive,
    /// All `resume`s are in tail position, but some tail paths do not resume.
    /// This covers abort-only arms too.
    OneShot,
    /// A `resume` appears in a non-tail position, in a nested closure, or in
    /// another shape that cannot prove single tail resumption.
    Multishot,
}

/// Handler-arm analysis keyed by `HandlerArm.id`.
#[derive(Debug, Clone, Default)]
pub struct HandlerAnalysis {
    pub resumption: HashMap<NodeId, ResumptionKind>,
}

pub fn analyze(program: &Program) -> HandlerAnalysis {
    let mut out = HandlerAnalysis::default();
    for decl in program {
        visit_decl(decl, &mut out);
    }
    out
}

fn visit_decl(decl: &Decl, out: &mut HandlerAnalysis) {
    match decl {
        Decl::FunBinding { body, guard, .. } => {
            visit_expr_for_arms(body, out);
            if let Some(guard) = guard {
                visit_expr_for_arms(guard, out);
            }
        }
        Decl::Let { value, .. } => visit_expr_for_arms(value, out),
        Decl::HandlerDef { body, .. } => visit_handler_body(body, out),
        Decl::DictConstructor { methods, .. } => {
            for method in methods {
                visit_expr_for_arms(method, out);
            }
        }
        Decl::ModuleDecl { .. }
        | Decl::Import { .. }
        | Decl::TypeDef { .. }
        | Decl::TypeAlias { .. }
        | Decl::RecordDef { .. }
        | Decl::EffectDef { .. }
        | Decl::FunSignature { .. }
        | Decl::TraitDef { .. }
        | Decl::ImplDef { .. } => {}
    }
}

fn visit_handler_body(body: &HandlerBody, out: &mut HandlerAnalysis) {
    for arm in &body.arms {
        classify_arm(&arm.node, out);
    }
    if let Some(return_clause) = &body.return_clause {
        classify_arm(return_clause, out);
    }
}

fn classify_arm(arm: &HandlerArm, out: &mut HandlerAnalysis) {
    out.resumption.insert(arm.id, classify_body(&arm.body));
    visit_expr_for_arms(&arm.body, out);
    if let Some(finally_block) = &arm.finally_block {
        visit_expr_for_arms(finally_block, out);
    }
}

fn visit_expr_for_arms(expr: &Expr, out: &mut HandlerAnalysis) {
    match &expr.kind {
        ExprKind::HandlerExpr { body } => visit_handler_body(body, out),
        ExprKind::With { expr, handler } => {
            visit_expr_for_arms(expr, out);
            match handler.as_ref() {
                Handler::Named(_) => {}
                Handler::Inline { items, .. } => {
                    for item in items {
                        match &item.node {
                            HandlerItem::Named(_) => {}
                            HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                                classify_arm(arm, out);
                            }
                        }
                    }
                }
            }
        }
        ExprKind::App { func, arg } => {
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
            for arm in arms {
                visit_case_arm(&arm.node, out);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                visit_stmt_for_arms(&stmt.node, out);
            }
        }
        ExprKind::Lambda { body, .. } => visit_expr_for_arms(body, out),
        ExprKind::FieldAccess { expr, .. } => visit_expr_for_arms(expr, out),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            for (_, _, field_expr) in fields {
                visit_expr_for_arms(field_expr, out);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            visit_expr_for_arms(record, out);
            for (_, _, field_expr) in fields {
                visit_expr_for_arms(field_expr, out);
            }
        }
        ExprKind::EffectCall { args, .. }
        | ExprKind::Tuple { elements: args }
        | ExprKind::ListLit { elements: args } => {
            for arg in args {
                visit_expr_for_arms(arg, out);
            }
        }
        ExprKind::Resume { value } => visit_expr_for_arms(value, out),
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, value) in bindings {
                visit_expr_for_arms(value, out);
            }
            visit_expr_for_arms(success, out);
            for arm in else_arms {
                visit_case_arm(&arm.node, out);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                visit_case_arm(&arm.node, out);
            }
            if let Some((timeout, body)) = after_clause {
                visit_expr_for_arms(timeout, out);
                visit_expr_for_arms(body, out);
            }
        }
        ExprKind::BitString { segments } => {
            for segment in segments {
                visit_expr_for_arms(&segment.value, out);
                if let Some(size) = &segment.size {
                    visit_expr_for_arms(size, out);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for segment in segments {
                visit_expr_for_arms(&segment.node, out);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for segment in segments {
                visit_expr_for_arms(&segment.node, out);
            }
        }
        ExprKind::Cons { head, tail } => {
            visit_expr_for_arms(head, out);
            visit_expr_for_arms(tail, out);
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(expr) = part {
                    visit_expr_for_arms(expr, out);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            visit_expr_for_arms(body, out);
            for qualifier in qualifiers {
                match qualifier {
                    ComprehensionQualifier::Generator(_, expr)
                    | ComprehensionQualifier::Let(_, expr)
                    | ComprehensionQualifier::Guard(expr) => visit_expr_for_arms(expr, out),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                visit_expr_for_arms(arg, out);
            }
        }
        ExprKind::DictMethodAccess { dict, .. } => visit_expr_for_arms(dict, out),
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}
    }
}

fn visit_case_arm(arm: &CaseArm, out: &mut HandlerAnalysis) {
    if let Some(guard) = &arm.guard {
        visit_expr_for_arms(guard, out);
    }
    visit_expr_for_arms(&arm.body, out);
}

fn visit_stmt_for_arms(stmt: &Stmt, out: &mut HandlerAnalysis) {
    match stmt {
        Stmt::Let { value, .. } => visit_expr_for_arms(value, out),
        Stmt::LetFun { body, guard, .. } => {
            visit_expr_for_arms(body, out);
            if let Some(guard) = guard {
                visit_expr_for_arms(guard, out);
            }
        }
        Stmt::Expr(expr) => visit_expr_for_arms(expr, out),
    }
}

fn classify_body(body: &Expr) -> ResumptionKind {
    let mut tails = Vec::new();
    collect_tail_positions(body, &mut tails);

    let total_resumes = count_resumes_anywhere(body);
    let tail_resumes = tails
        .iter()
        .filter(|expr| matches!(expr.kind, ExprKind::Resume { .. }))
        .count();

    if tail_resumes < total_resumes {
        return ResumptionKind::Multishot;
    }

    if !tails.is_empty() && tail_resumes == tails.len() {
        ResumptionKind::TailResumptive
    } else {
        ResumptionKind::OneShot
    }
}

fn collect_tail_positions<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &expr.kind {
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_tail_positions(then_branch, out);
            collect_tail_positions(else_branch, out);
        }
        ExprKind::Case { arms, .. } => {
            for arm in arms {
                collect_tail_positions(&arm.node.body, out);
            }
        }
        ExprKind::Block { stmts, .. } => match stmts.last() {
            Some(last) => match &last.node {
                Stmt::Expr(tail) => collect_tail_positions(tail, out),
                Stmt::Let { .. } | Stmt::LetFun { .. } => out.push(expr),
            },
            None => out.push(expr),
        },
        ExprKind::Do {
            success, else_arms, ..
        } => {
            collect_tail_positions(success, out);
            for arm in else_arms {
                collect_tail_positions(&arm.node.body, out);
            }
        }
        ExprKind::Ascription { expr, .. } => collect_tail_positions(expr, out),
        _ => out.push(expr),
    }
}

fn count_resumes_anywhere(expr: &Expr) -> usize {
    let mut count = 0;
    walk_count(expr, &mut count);
    count
}

fn walk_count(expr: &Expr, count: &mut usize) {
    match &expr.kind {
        ExprKind::Resume { value } => {
            *count += 1;
            walk_count(value, count);
        }
        ExprKind::App { func, arg } => {
            walk_count(func, count);
            walk_count(arg, count);
        }
        ExprKind::BinOp { left, right, .. } => {
            walk_count(left, count);
            walk_count(right, count);
        }
        ExprKind::UnaryMinus { expr } | ExprKind::Ascription { expr, .. } => {
            walk_count(expr, count);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            walk_count(cond, count);
            walk_count(then_branch, count);
            walk_count(else_branch, count);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            walk_count(scrutinee, count);
            for arm in arms {
                if let Some(guard) = &arm.node.guard {
                    walk_count(guard, count);
                }
                walk_count(&arm.node.body, count);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                match &stmt.node {
                    Stmt::Let { value, .. } => walk_count(value, count),
                    Stmt::LetFun { body, guard, .. } => {
                        walk_count(body, count);
                        if let Some(guard) = guard {
                            walk_count(guard, count);
                        }
                    }
                    Stmt::Expr(expr) => walk_count(expr, count),
                }
            }
        }
        ExprKind::Lambda { body, .. } => walk_count(body, count),
        ExprKind::FieldAccess { expr, .. } => walk_count(expr, count),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            for (_, _, field_expr) in fields {
                walk_count(field_expr, count);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            walk_count(record, count);
            for (_, _, field_expr) in fields {
                walk_count(field_expr, count);
            }
        }
        ExprKind::EffectCall { args, .. }
        | ExprKind::Tuple { elements: args }
        | ExprKind::ListLit { elements: args } => {
            for arg in args {
                walk_count(arg, count);
            }
        }
        ExprKind::With { expr, .. } => walk_count(expr, count),
        ExprKind::HandlerExpr { .. } => {}
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, expr) in bindings {
                walk_count(expr, count);
            }
            walk_count(success, count);
            for arm in else_arms {
                if let Some(guard) = &arm.node.guard {
                    walk_count(guard, count);
                }
                walk_count(&arm.node.body, count);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                if let Some(guard) = &arm.node.guard {
                    walk_count(guard, count);
                }
                walk_count(&arm.node.body, count);
            }
            if let Some((timeout, body)) = after_clause {
                walk_count(timeout, count);
                walk_count(body, count);
            }
        }
        ExprKind::BitString { segments } => {
            for segment in segments {
                walk_count(&segment.value, count);
                if let Some(size) = &segment.size {
                    walk_count(size, count);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for segment in segments {
                walk_count(&segment.node, count);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for segment in segments {
                walk_count(&segment.node, count);
            }
        }
        ExprKind::Cons { head, tail } => {
            walk_count(head, count);
            walk_count(tail, count);
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(expr) = part {
                    walk_count(expr, count);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            walk_count(body, count);
            for qualifier in qualifiers {
                match qualifier {
                    ComprehensionQualifier::Generator(_, expr)
                    | ComprehensionQualifier::Let(_, expr)
                    | ComprehensionQualifier::Guard(expr) => walk_count(expr, count),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                walk_count(arg, count);
            }
        }
        ExprKind::DictMethodAccess { dict, .. } => walk_count(dict, count),
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Annotated, BinOp, Lit, Pat};
    use crate::token::Span;

    fn sp() -> Span {
        Span { start: 0, end: 0 }
    }

    fn expr(kind: ExprKind) -> Expr {
        Expr::synth(sp(), kind)
    }

    fn lit_int(n: i64) -> Expr {
        expr(ExprKind::Lit {
            value: Lit::Int(n.to_string(), n),
        })
    }

    fn var(name: &str) -> Expr {
        expr(ExprKind::Var {
            name: name.to_string(),
        })
    }

    fn resume(value: Expr) -> Expr {
        expr(ExprKind::Resume {
            value: Box::new(value),
        })
    }

    fn lambda(param: &str, body: Expr) -> Expr {
        expr(ExprKind::Lambda {
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: param.to_string(),
                span: sp(),
            }],
            body: Box::new(body),
        })
    }

    fn if_expr(cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr {
        expr(ExprKind::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
            multiline: false,
        })
    }

    fn block(stmts: Vec<Stmt>) -> Expr {
        expr(ExprKind::Block {
            stmts: stmts.into_iter().map(Annotated::bare).collect(),
            dangling_trivia: Vec::new(),
        })
    }

    fn arm(body: Expr) -> HandlerArm {
        HandlerArm {
            id: NodeId::fresh(),
            op_name: "get".to_string(),
            qualifier: None,
            params: Vec::new(),
            body: Box::new(body),
            finally_block: None,
            span: sp(),
        }
    }

    fn classify(body: Expr) -> ResumptionKind {
        let arm = arm(body);
        let mut analysis = HandlerAnalysis::default();
        classify_arm(&arm, &mut analysis);
        analysis.resumption[&arm.id]
    }

    #[test]
    fn tail_resumptive_simple() {
        assert_eq!(
            classify(resume(var("value"))),
            ResumptionKind::TailResumptive
        );
    }

    #[test]
    fn tail_resumptive_all_branches_resume() {
        assert_eq!(
            classify(if_expr(var("cond"), resume(lit_int(1)), resume(lit_int(2)))),
            ResumptionKind::TailResumptive
        );
    }

    #[test]
    fn one_shot_when_some_tail_paths_abort() {
        assert_eq!(
            classify(if_expr(var("cond"), resume(lit_int(1)), lit_int(0))),
            ResumptionKind::OneShot
        );
    }

    #[test]
    fn one_shot_when_arm_never_resumes() {
        assert_eq!(classify(lit_int(0)), ResumptionKind::OneShot);
    }

    #[test]
    fn multishot_when_resume_is_not_tail() {
        let body = expr(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(resume(var("value"))),
            right: Box::new(lit_int(1)),
        });
        assert_eq!(classify(body), ResumptionKind::Multishot);
    }

    #[test]
    fn multishot_when_resume_is_captured_in_lambda() {
        assert_eq!(
            classify(lambda("x", resume(var("x")))),
            ResumptionKind::Multishot
        );
    }

    #[test]
    fn block_tail_uses_last_expression() {
        let body = block(vec![
            Stmt::Let {
                pattern: Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: sp(),
                },
                annotation: None,
                value: var("ignored"),
                assert: false,
                span: sp(),
            },
            Stmt::Expr(resume(var("value"))),
        ]);
        assert_eq!(classify(body), ResumptionKind::TailResumptive);
    }

    #[test]
    fn multishot_when_resume_is_in_block_let_value() {
        let body = block(vec![
            Stmt::Let {
                pattern: Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: sp(),
                },
                annotation: None,
                value: resume(var("value")),
                assert: false,
                span: sp(),
            },
            Stmt::Expr(lit_int(0)),
        ]);
        assert_eq!(classify(body), ResumptionKind::Multishot);
    }
}
