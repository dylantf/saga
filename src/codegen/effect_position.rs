//! Where an expression that performs effects may appear.
//!
//! One table (`children`) gives, for every expression kind, its
//! sub-expressions in evaluation order and the position each one is in.
//! Everything else here is derived from that table:
//!
//! - `is_effectful`: an expression performs effects when it is a performing
//!   leaf (decided by the caller: a call the plan classified CPS, an applied
//!   operation, ...) or has a sub-expression that does, not looking into
//!   bodies that run later (lambdas, handler arms, local functions).
//! - `check_body`: in a body, an expression that performs effects must be
//!   the value of a block-level `let`/statement or in tail position. One
//!   found as an operand of something else is a violation.
//!
//! The rule is about position in the tree only. How a body is lowered
//! (with a continuation or as a plain value) does not enter into it.

use crate::ast::{
    CaseArm, ComprehensionQualifier, Expr, ExprKind, Handler, HandlerArm, HandlerItem, Stmt,
    StringPart,
};
use crate::token::Span;

/// The position of a sub-expression relative to its parent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Position {
    /// Evaluated to a value the parent then uses: a call argument, an
    /// operator operand, a condition, a scrutinee, a field value.
    Operand,
    /// Evaluated with a continuation the parent supplies: a branch (its
    /// continuation is the parent's), or a block statement, a `let` value
    /// or a `do` binding (its continuation is the rest of the block).
    Tail,
    /// A body of its own, run later or delimited: a lambda or local function
    /// body, a handler arm, the computation a `with` handles, a guard. It is
    /// a tail context, and what it performs is not performed by the parent.
    Body,
}

fn arm_children<'a>(arm: &'a CaseArm, out: &mut Vec<(Position, &'a Expr)>) {
    if let Some(guard) = &arm.guard {
        out.push((Position::Body, guard));
    }
    out.push((Position::Tail, &arm.body));
}

fn handler_arm_children<'a>(arm: &'a HandlerArm, out: &mut Vec<(Position, &'a Expr)>) {
    out.push((Position::Body, &arm.body));
    if let Some(finally) = &arm.finally_block {
        out.push((Position::Body, finally));
    }
}

/// The head of an application chain and its `App` nodes, innermost first.
fn app_spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut spine = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, .. } = &current.kind {
        spine.push(current);
        current = func;
    }
    spine.reverse();
    (current, spine)
}

/// Sub-expressions of `expr` in evaluation order, with their positions.
///
/// An application chain `h a b` is one unit: its children are the head and
/// the arguments, never a partial application of its own spine.
///
/// The match is exhaustive on purpose: a new expression kind has to be
/// placed here before the compiler builds.
pub(crate) fn children(expr: &Expr) -> Vec<(Position, &Expr)> {
    use Position::{Body, Operand, Tail};
    let mut out = Vec::new();
    match &expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. } => {}

        ExprKind::App { .. } => {
            let (head, spine) = app_spine(expr);
            // The operation of an applied operation is not an operand: it
            // is not evaluated on its own.
            match &head.kind {
                ExprKind::EffectCall { args, .. } => out.extend(args.iter().map(|e| (Operand, e))),
                _ => out.push((Operand, head)),
            }
            for app in spine {
                if let ExprKind::App { arg, .. } = &app.kind {
                    out.push((Operand, arg.as_ref()));
                }
            }
        }

        // The right operand of `&&`/`||` is an operand too: one that
        // performs effects makes the operator an `if` (see normalize).
        ExprKind::BinOp { left, right, .. } => {
            out.push((Operand, left.as_ref()));
            out.push((Operand, right.as_ref()));
        }
        ExprKind::UnaryMinus { expr: inner }
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::DictMethodAccess { dict: inner, .. }
        | ExprKind::DictSuperAccess { dict: inner, .. }
        | ExprKind::Resume { value: inner } => out.push((Operand, inner.as_ref())),

        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            out.push((Operand, cond.as_ref()));
            out.push((Tail, then_branch.as_ref()));
            out.push((Tail, else_branch.as_ref()));
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            out.push((Operand, scrutinee.as_ref()));
            for arm in arms {
                arm_children(&arm.node, &mut out);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                match &stmt.node {
                    Stmt::Let { value, .. } => out.push((Tail, value)),
                    Stmt::Expr(e) => out.push((Tail, e)),
                    Stmt::LetFun { guard, body, .. } => {
                        if let Some(guard) = guard {
                            out.push((Body, guard.as_ref()));
                        }
                        out.push((Body, body));
                    }
                }
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, value) in bindings {
                out.push((Tail, value));
            }
            out.push((Tail, success.as_ref()));
            for arm in else_arms {
                arm_children(&arm.node, &mut out);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            if let Some((timeout, _)) = after_clause {
                out.push((Operand, timeout.as_ref()));
            }
            for arm in arms {
                arm_children(&arm.node, &mut out);
            }
            if let Some((_, body)) = after_clause {
                out.push((Tail, body.as_ref()));
            }
        }

        ExprKind::Lambda { body, .. } => out.push((Body, body.as_ref())),
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            out.push((Body, inner.as_ref()));
            if let Handler::Inline { items, .. } = handler.as_ref() {
                for item in items {
                    match &item.node {
                        HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                            handler_arm_children(arm, &mut out)
                        }
                        HandlerItem::Named(_) => {}
                    }
                }
            }
        }
        ExprKind::HandlerExpr { body } => {
            for arm in &body.arms {
                handler_arm_children(&arm.node, &mut out);
            }
            if let Some(ret) = &body.return_clause {
                handler_arm_children(ret, &mut out);
            }
        }

        ExprKind::Tuple { elements } => out.extend(elements.iter().map(|e| (Operand, e))),
        ExprKind::RecordCreate { fields, .. }
        | ExprKind::AnonRecordCreate { fields }
        | ExprKind::RecordBuild { fields, .. } => {
            out.extend(fields.iter().map(|(_, _, e)| (Operand, e)))
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            out.push((Operand, record.as_ref()));
            out.extend(fields.iter().map(|(_, _, e)| (Operand, e)));
        }
        ExprKind::EffectCall { args, .. } | ExprKind::ForeignCall { args, .. } => {
            out.extend(args.iter().map(|e| (Operand, e)))
        }
        ExprKind::BitString { segments } => {
            for seg in segments {
                out.push((Operand, &seg.value));
                if let Some(size) = &seg.size {
                    out.push((Operand, size.as_ref()));
                }
            }
        }
        // An ascription is its inner expression.
        ExprKind::Ascription { expr: inner, .. } => out.push((Tail, inner.as_ref())),

        // Surface syntax, desugared before codegen.
        ExprKind::Pipe { segments, .. }
        | ExprKind::BinOpChain { segments, .. }
        | ExprKind::PipeBack { segments }
        | ExprKind::ComposeForward { segments } => {
            out.extend(segments.iter().map(|s| (Operand, &s.node)))
        }
        ExprKind::Cons { head, tail } => {
            out.push((Operand, head.as_ref()));
            out.push((Operand, tail.as_ref()));
        }
        ExprKind::ListLit { elements, .. } => {
            out.extend(elements.iter().map(|e| (Operand, &e.node)))
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    out.push((Operand, e));
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            for qualifier in qualifiers {
                match qualifier {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Guard(e)
                    | ComprehensionQualifier::Let(_, e) => out.push((Operand, e)),
                }
            }
            out.push((Operand, body.as_ref()));
        }
    }
    out
}

/// Whether `expr` itself has to be in `let`/tail position: it is a
/// performing leaf, or a branch or statement inside it performs effects.
/// Its operands are not looked at; those are positions of their own.
///
/// For an application chain the leaf question is asked of every `App` node
/// of the spine: a chain is one unit, whichever of its nodes the plan marks.
pub(crate) fn needs_continuation(expr: &Expr, leaf: &dyn Fn(&Expr) -> bool) -> bool {
    let is_leaf = match &expr.kind {
        ExprKind::App { .. } => app_spine(expr).1.into_iter().any(leaf),
        _ => leaf(expr),
    };
    is_leaf
        || children(expr)
            .into_iter()
            .any(|(position, child)| position == Position::Tail && is_effectful(child, leaf))
}

/// Whether evaluating `expr` can perform an effect, given which nodes
/// perform one themselves (`leaf`). Compositional: bodies that run later do
/// not count.
pub(crate) fn is_effectful(expr: &Expr, leaf: &dyn Fn(&Expr) -> bool) -> bool {
    let is_leaf = match &expr.kind {
        ExprKind::App { .. } => app_spine(expr).1.into_iter().any(leaf),
        _ => leaf(expr),
    };
    is_leaf
        || children(expr)
            .into_iter()
            .any(|(position, child)| position != Position::Body && is_effectful(child, leaf))
}

/// An expression that performs effects found as an operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Violation {
    /// The construct that performs effects.
    pub construct: &'static str,
    /// The construct it is an operand of.
    pub operand_of: &'static str,
    pub span: Span,
}

/// Check a body (an expression in tail position): every expression that
/// performs effects must be in `let`/statement or tail position.
pub(crate) fn check_body(body: &Expr, leaf: &dyn Fn(&Expr) -> bool, out: &mut Vec<Violation>) {
    for (position, child) in children(body) {
        if position == Position::Operand && needs_continuation(child, leaf) {
            out.push(Violation {
                construct: construct_name(child, leaf),
                operand_of: construct_name(body, leaf),
                span: child.span,
            });
        }
        // Whatever position `child` is in, the positions inside it are
        // judged the same way: once it is lifted into a `let`, its own
        // branches are tails and its operands are still operands.
        check_body(child, leaf, out);
    }
}

/// A short name for a construct, for reports and internal errors.
pub(crate) fn construct_name(expr: &Expr, leaf: &dyn Fn(&Expr) -> bool) -> &'static str {
    match &expr.kind {
        ExprKind::App { .. } => {
            let (head, spine) = app_spine(expr);
            if matches!(head.kind, ExprKind::EffectCall { .. }) {
                "operation call"
            } else if spine.into_iter().any(leaf) {
                "effectful call"
            } else if matches!(head.kind, ExprKind::Constructor { .. }) {
                "constructor application"
            } else {
                "pure call"
            }
        }
        ExprKind::BinOp {
            op: crate::ast::BinOp::And | crate::ast::BinOp::Or,
            ..
        } => "`&&`/`||`",
        ExprKind::BinOp { .. } => "binary operator",
        ExprKind::UnaryMinus { .. } => "unary minus",
        ExprKind::If { .. } => "if",
        ExprKind::Case { .. } => "case",
        ExprKind::Block { .. } => "block",
        ExprKind::Do { .. } => "do",
        ExprKind::Receive { .. } => "receive",
        ExprKind::With { .. } => "with",
        ExprKind::Resume { .. } => "resume",
        ExprKind::Lambda { .. } => "lambda",
        ExprKind::HandlerExpr { .. } => "handler value",
        ExprKind::Tuple { .. } => "tuple",
        ExprKind::RecordCreate { .. }
        | ExprKind::AnonRecordCreate { .. }
        | ExprKind::RecordBuild { .. } => "record literal",
        ExprKind::RecordUpdate { .. } => "record update",
        ExprKind::FieldAccess { .. } => "field access",
        ExprKind::BitString { .. } => "bit string",
        ExprKind::EffectCall { .. } => "operation reference",
        ExprKind::ForeignCall { .. } => "foreign call",
        ExprKind::DictMethodAccess { .. } | ExprKind::DictSuperAccess { .. } => "dictionary access",
        ExprKind::Ascription { .. } => "ascription",
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. } => "name or literal",
        ExprKind::Pipe { .. }
        | ExprKind::BinOpChain { .. }
        | ExprKind::PipeBack { .. }
        | ExprKind::ComposeForward { .. }
        | ExprKind::Cons { .. }
        | ExprKind::ListLit { .. }
        | ExprKind::StringInterp { .. }
        | ExprKind::ListComprehension { .. } => "surface syntax",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Decl;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    /// The body of `f` in `source`.
    fn body(source: &str) -> Expr {
        let tokens = Lexer::new(source).lex().expect("lex");
        let program = Parser::new(tokens).parse_program().expect("parse");
        program
            .into_iter()
            .find_map(|decl| match decl {
                Decl::FunBinding { name, body, .. } if name == "f" => Some(body),
                _ => None,
            })
            .expect("function f")
    }

    /// Leaves for the tests: an applied operation, or a call to `eff`.
    fn leaf(expr: &Expr) -> bool {
        let ExprKind::App { .. } = &expr.kind else {
            return false;
        };
        let (head, _) = app_spine(expr);
        matches!(&head.kind, ExprKind::EffectCall { .. })
            || matches!(&head.kind, ExprKind::Var { name } if name == "eff")
    }

    fn violations(source: &str) -> Vec<(&'static str, &'static str)> {
        let mut out = Vec::new();
        check_body(&body(source), &leaf, &mut out);
        out.into_iter()
            .map(|v| (v.construct, v.operand_of))
            .collect()
    }

    #[test]
    fn effectfulness_stops_at_bodies_that_run_later() {
        assert!(is_effectful(&body("f x = (eff x, 1)"), &leaf));
        assert!(is_effectful(&body("f x = if x then eff 1 else 2"), &leaf));
        assert!(!is_effectful(&body("f x = fun y -> eff y"), &leaf));
        assert!(!is_effectful(
            &body("f x = {\n  let g y = eff y\n  1\n}"),
            &leaf
        ));
        assert!(!is_effectful(&body("f x = g x 1"), &leaf));
    }

    #[test]
    fn let_values_and_tails_are_allowed() {
        assert_eq!(violations("f x = eff x"), vec![]);
        assert_eq!(
            violations("f x = {\n  let y = eff x\n  log! y\n  if y then eff 1 else 2\n}"),
            vec![]
        );
        assert_eq!(
            violations("f x = {\n  let y = if x then eff 1 else 2\n  y\n}"),
            vec![]
        );
        assert_eq!(violations("f x = fun y -> eff y"), vec![]);
    }

    #[test]
    fn operands_are_reported_with_their_parent() {
        assert_eq!(
            violations("f x = (eff x, 1)"),
            vec![("effectful call", "tuple")]
        );
        assert_eq!(
            violations("f x = g (log! x)"),
            vec![("operation call", "pure call")]
        );
        assert_eq!(
            violations("f x = if eff x then 1 else 2"),
            vec![("effectful call", "if")]
        );
        assert_eq!(
            violations("f x = eff (if x then eff 1 else 2)"),
            vec![("if", "effectful call")]
        );
        // The operand inside a body that runs later is still an operand.
        assert_eq!(
            violations("f x = fun y -> (eff y, 1)"),
            vec![("effectful call", "tuple")]
        );
    }

    #[test]
    fn a_chain_of_applications_is_one_unit() {
        // `eff x y` is one call: its inner `eff x` is not an operand.
        assert_eq!(violations("f x y = eff x y"), vec![]);
        assert_eq!(
            violations("f x y = eff (eff x) y"),
            vec![("effectful call", "effectful call")]
        );
    }
}
