use crate::ast::*;
use crate::token::Span;
use crate::token::StringKind;

pub(crate) fn var_expr(name: &str, span: Span) -> Expr {
    Expr::synth(span, ExprKind::Var { name: name.into() })
}


pub(crate) fn value_expr(name: &str, span: Span) -> Expr {
    if let Some((module, name)) = name.rsplit_once('.') {
        Expr::synth(
            span,
            ExprKind::QualifiedName {
                module: module.to_string(),
                name: name.to_string(),
                canonical_module: Some(module.to_string()),
            },
        )
    } else {
        var_expr(name, span)
    }
}


pub(crate) fn ctor_expr(name: &str, span: Span) -> Expr {
    Expr::synth(span, ExprKind::Constructor { name: name.into() })
}


pub(crate) fn app_expr(func: Expr, arg: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(func),
            arg: Box::new(arg),
        },
    )
}


pub(crate) fn type_named(name: &str) -> TypeExpr {
    TypeExpr::Named {
        id: NodeId::fresh(),
        name: generic_name(name),
        span: Span { start: 0, end: 0 },
    }
}


pub(crate) fn generic_name(name: &str) -> String {
    format!("Std.Generic.{name}")
}


pub(crate) fn type_app(func: TypeExpr, arg: TypeExpr) -> TypeExpr {
    TypeExpr::App {
        id: NodeId::fresh(),
        func: Box::new(func),
        arg: Box::new(arg),
        span: Span { start: 0, end: 0 },
    }
}


/// Build a type-level symbol literal `TypeExpr::Symbol`. Used by the Generic
/// synthesizer to put constructor/field names at the type level rather than
/// carrying them as value-level strings.
pub(crate) fn type_symbol(name: &str) -> TypeExpr {
    TypeExpr::Symbol {
        id: NodeId::fresh(),
        name: name.to_string(),
        span: Span { start: 0, end: 0 },
    }
}


pub(crate) fn apply_ctor(name: &str, arg: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(Expr::synth(
                span,
                ExprKind::Constructor { name: name.into() },
            )),
            arg: Box::new(arg),
        },
    )
}


pub(crate) fn apply2(func: &str, a: Expr, b: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(Expr::synth(
                span,
                ExprKind::App {
                    func: Box::new(Expr::synth(
                        span,
                        ExprKind::Constructor { name: func.into() },
                    )),
                    arg: Box::new(a),
                },
            )),
            arg: Box::new(b),
        },
    )
}


pub(crate) fn string_lit(s: &str, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::Lit {
            value: Lit::String(s.into(), StringKind::Normal),
        },
    )
}

