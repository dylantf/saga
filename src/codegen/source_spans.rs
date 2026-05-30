use std::collections::HashMap;

use crate::ast;
use crate::token::Span;

pub fn for_program(
    program: &ast::Program,
    checked_spans: &HashMap<ast::NodeId, Span>,
) -> HashMap<ast::NodeId, Span> {
    let mut spans = checked_spans.clone();
    for decl in program {
        collect_decl(decl, &mut spans);
    }
    spans
}

fn collect_decl(decl: &ast::Decl, spans: &mut HashMap<ast::NodeId, Span>) {
    match decl {
        ast::Decl::FunBinding {
            guard,
            body,
            id,
            span,
            ..
        } => {
            spans.insert(*id, *span);
            if let Some(guard) = guard {
                collect_expr(guard, spans);
            }
            collect_expr(body, spans);
        }
        ast::Decl::Let {
            id, value, span, ..
        }
        | ast::Decl::Val {
            id, value, span, ..
        } => {
            spans.insert(*id, *span);
            collect_expr(value, spans);
        }
        ast::Decl::HandlerDef { id, body, span, .. } => {
            spans.insert(*id, *span);
            collect_handler_body(body, spans);
        }
        ast::Decl::ImplDef {
            id, methods, span, ..
        } => {
            spans.insert(*id, *span);
            for method in methods {
                collect_expr(&method.node.body, spans);
            }
        }
        ast::Decl::DictConstructor {
            id, methods, span, ..
        } => {
            spans.insert(*id, *span);
            for method in methods {
                collect_expr(method, spans);
            }
        }
        _ => {}
    }
}

fn collect_expr(expr: &ast::Expr, spans: &mut HashMap<ast::NodeId, Span>) {
    spans.insert(expr.id, expr.span);
    match &expr.kind {
        ast::ExprKind::App { func, arg } => {
            collect_expr(func, spans);
            collect_expr(arg, spans);
        }
        ast::ExprKind::BinOp { left, right, .. } => {
            collect_expr(left, spans);
            collect_expr(right, spans);
        }
        ast::ExprKind::UnaryMinus { expr } | ast::ExprKind::Ascription { expr, .. } => {
            collect_expr(expr, spans);
        }
        ast::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr(cond, spans);
            collect_expr(then_branch, spans);
            collect_expr(else_branch, spans);
        }
        ast::ExprKind::Case {
            scrutinee, arms, ..
        } => {
            collect_expr(scrutinee, spans);
            for arm in arms {
                if let Some(guard) = &arm.node.guard {
                    collect_expr(guard, spans);
                }
                collect_expr(&arm.node.body, spans);
            }
        }
        ast::ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                collect_stmt(&stmt.node, spans);
            }
        }
        ast::ExprKind::Lambda { body, .. } => collect_expr(body, spans),
        ast::ExprKind::FieldAccess { expr, .. } => collect_expr(expr, spans),
        ast::ExprKind::RecordCreate { fields, .. } | ast::ExprKind::AnonRecordCreate { fields } => {
            for (_, _, value) in fields {
                collect_expr(value, spans);
            }
        }
        ast::ExprKind::RecordUpdate { record, fields, .. } => {
            collect_expr(record, spans);
            for (_, _, value) in fields {
                collect_expr(value, spans);
            }
        }
        ast::ExprKind::EffectCall { args, .. } => {
            for arg in args {
                collect_expr(arg, spans);
            }
        }
        ast::ExprKind::With { expr, handler } => {
            collect_expr(expr, spans);
            collect_handler(handler, spans);
        }
        ast::ExprKind::Resume { value } => collect_expr(value, spans),
        ast::ExprKind::Tuple { elements } | ast::ExprKind::ListLit { elements } => {
            for element in elements {
                collect_expr(element, spans);
            }
        }
        ast::ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, value) in bindings {
                collect_expr(value, spans);
            }
            collect_expr(success, spans);
            for arm in else_arms {
                if let Some(guard) = &arm.node.guard {
                    collect_expr(guard, spans);
                }
                collect_expr(&arm.node.body, spans);
            }
        }
        ast::ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                if let Some(guard) = &arm.node.guard {
                    collect_expr(guard, spans);
                }
                collect_expr(&arm.node.body, spans);
            }
            if let Some((timeout, body)) = after_clause {
                collect_expr(timeout, spans);
                collect_expr(body, spans);
            }
        }
        ast::ExprKind::BitString { segments } => {
            for segment in segments {
                collect_expr(&segment.value, spans);
                if let Some(size) = &segment.size {
                    collect_expr(size, spans);
                }
            }
        }
        ast::ExprKind::HandlerExpr { body } => collect_handler_body(body, spans),
        ast::ExprKind::Pipe { segments, .. } | ast::ExprKind::BinOpChain { segments, .. } => {
            for segment in segments {
                collect_expr(&segment.node, spans);
            }
        }
        ast::ExprKind::PipeBack { segments } | ast::ExprKind::ComposeForward { segments } => {
            for segment in segments {
                collect_expr(&segment.node, spans);
            }
        }
        ast::ExprKind::Cons { head, tail } => {
            collect_expr(head, spans);
            collect_expr(tail, spans);
        }
        ast::ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(expr) = part {
                    collect_expr(expr, spans);
                }
            }
        }
        ast::ExprKind::ListComprehension { body, qualifiers } => {
            collect_expr(body, spans);
            for qualifier in qualifiers {
                match qualifier {
                    ast::ComprehensionQualifier::Generator(_, expr)
                    | ast::ComprehensionQualifier::Guard(expr)
                    | ast::ComprehensionQualifier::Let(_, expr) => collect_expr(expr, spans),
                }
            }
        }
        ast::ExprKind::DictMethodAccess { dict, .. } => collect_expr(dict, spans),
        ast::ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                collect_expr(arg, spans);
            }
        }
        ast::ExprKind::Lit { .. }
        | ast::ExprKind::Var { .. }
        | ast::ExprKind::Constructor { .. }
        | ast::ExprKind::QualifiedName { .. }
        | ast::ExprKind::DictRef { .. }
        | ast::ExprKind::SymbolIntrinsic { .. } => {}
    }
}

fn collect_stmt(stmt: &ast::Stmt, spans: &mut HashMap<ast::NodeId, Span>) {
    match stmt {
        ast::Stmt::Let { value, .. } | ast::Stmt::Expr(value) => collect_expr(value, spans),
        ast::Stmt::LetFun {
            id,
            guard,
            body,
            span,
            ..
        } => {
            spans.insert(*id, *span);
            if let Some(guard) = guard {
                collect_expr(guard, spans);
            }
            collect_expr(body, spans);
        }
    }
}

fn collect_handler(handler: &ast::Handler, spans: &mut HashMap<ast::NodeId, Span>) {
    match handler {
        ast::Handler::Named(named) => {
            spans.insert(named.id, named.span);
        }
        ast::Handler::Inline { items, .. } => {
            for item in items {
                match &item.node {
                    ast::HandlerItem::Named(named) => {
                        spans.insert(named.id, named.span);
                    }
                    ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                        collect_handler_arm(arm, spans);
                    }
                }
            }
        }
    }
}

fn collect_handler_body(body: &ast::HandlerBody, spans: &mut HashMap<ast::NodeId, Span>) {
    for arm in &body.arms {
        collect_handler_arm(&arm.node, spans);
    }
    if let Some(return_clause) = &body.return_clause {
        collect_handler_arm(return_clause, spans);
    }
}

fn collect_handler_arm(arm: &ast::HandlerArm, spans: &mut HashMap<ast::NodeId, Span>) {
    spans.insert(arm.id, arm.span);
    collect_expr(&arm.body, spans);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr(finally_block, spans);
    }
}
