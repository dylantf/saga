use super::Doc;
use super::decl::is_block_like;
use super::helpers::{
    docs_from_vec, escape_string, format_binop, format_braced_body, format_handler_arm,
    format_trailing, format_trivia,
};
use super::pat::format_pat;
use super::type_expr::format_type_expr;
use crate::ast::*;
use crate::docs;
use crate::token::Span;
use crate::token::StringKind;

/// Return the precedence level of a binary operator, matching the parser.
fn binop_precedence(op: &BinOp) -> u8 {
    match op {
        BinOp::Or => 2,
        BinOp::And => 3,
        BinOp::Eq | BinOp::NotEq => 4,
        BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => 5,
        BinOp::Add | BinOp::Sub | BinOp::Concat => 6,
        BinOp::Mul | BinOp::FloatDiv | BinOp::IntDiv | BinOp::Mod | BinOp::FloatMod => 7,
    }
}

/// Format a BinOp operand, wrapping in parens if its precedence is lower than
/// the outer operator (i.e. parens are needed to preserve meaning).
fn format_binop_operand(operand: &Expr, outer_prec: u8) -> Doc {
    if matches!(operand.kind, ExprKind::With { .. }) {
        return docs![Doc::text("("), format_expr(operand), Doc::text(")")];
    }
    if let ExprKind::BinOp { op: inner_op, .. } = &operand.kind
        && binop_precedence(inner_op) < outer_prec
    {
        return docs![Doc::text("("), format_expr(operand), Doc::text(")")];
    }
    format_expr(operand)
}

/// Flatten a left-nested BinOp chain of the same operator.
/// `(a + b) + c` with op=Add -> ([a, b, c], Add)
/// Stops flattening when the operator changes (respects precedence).
fn flatten_binop<'a>(expr: &'a Expr, op: &'a BinOp) -> (Vec<&'a Expr>, &'a BinOp) {
    let mut operands = Vec::new();
    let mut current = expr;
    while let ExprKind::BinOp {
        op: ref curr_op,
        ref left,
        ref right,
    } = current.kind
    {
        if curr_op == op {
            operands.push(right.as_ref());
            current = left.as_ref();
        } else {
            break;
        }
    }
    operands.push(current);
    operands.reverse();
    (operands, op)
}

/// Flatten a left-nested App chain into (func, [arg1, arg2, ...]).
pub fn flatten_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}

/// Expressions whose internal line breaks can change parsing if they appear on
/// the same source line as `=`, `->`, etc. If these break, their caller should
/// break before the whole expression first so continuation indentation is safe.
pub fn is_layout_sensitive_app(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::App { .. } => true,
        ExprKind::With { expr, .. } => is_layout_sensitive_app(expr),
        _ => false,
    }
}

fn format_block_contents(stmts: &[Annotated<Stmt>], dangling_trivia: &[Trivia]) -> Doc {
    let mut parts = Vec::new();
    for (i, ann) in stmts.iter().enumerate() {
        if i > 0 {
            parts.push(Doc::hardline());
        }
        parts.push(format_trivia(&ann.leading_trivia));
        parts.push(format_stmt(&ann.node));
        parts.push(format_trailing(&ann.trailing_comment));
    }
    let dangling: Vec<Trivia> = dangling_trivia
        .iter()
        .filter(|item| !matches!(item, Trivia::BlankLines(_)))
        .cloned()
        .collect();
    if !dangling.is_empty() {
        if !stmts.is_empty() {
            parts.push(Doc::hardline());
        }
        parts.push(format_trivia(&dangling));
    }
    docs_from_vec(parts)
}

pub(super) fn single_expr_block(expr: &Expr) -> Option<&Expr> {
    let ExprKind::Block {
        stmts,
        dangling_trivia,
    } = &expr.kind
    else {
        return None;
    };
    if !dangling_trivia.is_empty() || stmts.len() != 1 {
        return None;
    }
    let ann = &stmts[0];
    if !ann.leading_trivia.is_empty()
        || ann.trailing_comment.is_some()
        || !ann.trailing_trivia.is_empty()
    {
        return None;
    }
    match &ann.node {
        Stmt::Expr(inner) => Some(inner),
        _ => None,
    }
}

fn has_layout_root(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Block { .. } => single_expr_block(expr).is_none(),
        ExprKind::With { expr, .. } => has_layout_root(expr),
        _ => false,
    }
}

pub(super) fn requires_layout_body(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Block { .. } => single_expr_block(expr).is_none(),
        ExprKind::Case { .. }
        | ExprKind::Do { .. }
        | ExprKind::Receive { .. }
        | ExprKind::HandlerExpr { .. } => true,
        ExprKind::If { multiline, .. } => *multiline,
        ExprKind::With { expr, .. } => has_layout_root(expr),
        _ => false,
    }
}

/// Format a body after a syntactic introducer such as `=`, `->`, or
/// `finally`. Layout-rooted bodies are indented, while a trailing `with` is
/// emitted back at the introducer's indentation so it handles the whole body.
pub(super) fn format_body_after(prefix: Doc, body: &Expr) -> Doc {
    if let Some(inner) = single_expr_block(body) {
        return format_body_after(prefix, inner);
    }
    match &body.kind {
        ExprKind::Block {
            stmts,
            dangling_trivia,
        } => docs![
            prefix,
            Doc::nest(
                2,
                docs![
                    Doc::hardline(),
                    format_block_contents(stmts, dangling_trivia)
                ]
            )
        ],
        ExprKind::With { expr, handler } if has_layout_root(expr) => docs![
            format_body_after(prefix, expr),
            Doc::hardline(),
            format_with_suffix(handler)
        ],
        _ if requires_layout_body(body) => docs![
            prefix,
            Doc::nest(2, docs![Doc::hardline(), format_expr(body)])
        ],
        _ => Doc::group(docs![
            prefix,
            Doc::nest(2, docs![Doc::line(), format_expr(body)])
        ]),
    }
}

fn format_binary_chain(segments: &[Annotated<Expr>], op: &str) -> Doc {
    let mut parts: Vec<Doc> = Vec::new();
    for (i, seg) in segments.iter().enumerate() {
        if i > 0 {
            parts.push(Doc::text(op));
        }
        parts.push(format_expr(&seg.node));
    }
    docs_from_vec(parts)
}

pub fn format_expr(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { value } => super::helpers::format_lit(value),
        ExprKind::Var { name } => Doc::text(name),
        ExprKind::Constructor { name } => Doc::text(name),
        ExprKind::QualifiedName { module, name, .. } => Doc::text(format!("{}.{}", module, name)),

        ExprKind::App { .. } => {
            // Flatten nested App chain: App(App(App(f, a), b), c) -> [f, a, b, c]
            let (func, args) = flatten_app(expr);
            // Wrap the function in parens if it's a compound expression
            // (e.g. `(resume x) y` must keep parens to avoid becoming `resume x y`)
            let func_doc = match &func.kind {
                ExprKind::Var { .. }
                | ExprKind::Constructor { .. }
                | ExprKind::QualifiedName { .. }
                | ExprKind::FieldAccess { .. }
                | ExprKind::EffectCall { .. } => format_expr(func),
                _ => format_expr_atom(func),
            };

            // Check if the last arg is a lambda with a block-like body.
            // If so, treat it as a "trailing lambda": keep `(fun params -> {`
            // on the same line as the call, with the block body indented from
            // the call site, not nested inside the arg list.
            // Check if any arg is a lambda with a block body ("trailing lambda").
            // Keep `(fun params -> {` on the same line as the call.
            if let Some(lambda_idx) = args.iter().position(
                |a| matches!(&a.kind, ExprKind::Lambda { body, .. } if is_block_like(body)),
            ) {
                let ExprKind::Lambda { params, body } = &args[lambda_idx].kind else {
                    unreachable!()
                };
                let before = &args[..lambda_idx];
                let after = &args[lambda_idx + 1..];

                // `before` args are rendered flat: the trailing lambda body
                // sits on the same line, so when fit-measuring any group inside
                // a before-arg (e.g. a list literal), `fits` would walk past
                // the group into the body's flat form and break the arg even
                // though it's short. Flattening the arg structurally pins it
                // to one line; if the arg itself is huge it overflows, which
                // matches how non-trailing-lambda applications already behave
                // (applications never break across lines).
                let mut prefix = func_doc;
                for a in before {
                    prefix = prefix
                        .append(Doc::text(" "))
                        .append(Doc::flat(format_expr_atom(a)));
                }
                let mut lhs = Doc::text("(fun ");
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        lhs = lhs.append(Doc::text(" "));
                    }
                    lhs = lhs.append(format_pat(p));
                }
                lhs = lhs.append(Doc::text(" ->"));

                let mut suffix = Doc::text(")");
                for a in after {
                    suffix = suffix.append(Doc::text(" ")).append(format_expr_atom(a));
                }

                if has_layout_root(body) {
                    return docs![
                        prefix,
                        Doc::text(" "),
                        format_body_after(lhs, body),
                        Doc::hardline(),
                        suffix
                    ];
                }
                let body_doc = format_expr(body);
                return docs![
                    prefix,
                    Doc::text(" "),
                    lhs,
                    Doc::text(" "),
                    body_doc,
                    suffix
                ];
            }

            let mut d = func_doc;
            for a in &args {
                d = d.append(Doc::line()).append(format_expr_atom(a));
            }
            Doc::group(Doc::nest(2, d))
        }

        ExprKind::BinOp { op, .. } => {
            // Flatten same-operator chains: (a + b) + c -> [a, b, c]
            // Break before operator: keeps operators aligned on the left.
            let (operands, chain_op) = flatten_binop(expr, op);
            let op_str = format_binop(chain_op);
            let outer_prec = binop_precedence(chain_op);

            let first = format_binop_operand(operands[0], outer_prec);
            let mut tail = Doc::Nil;
            for operand in &operands[1..] {
                tail = tail
                    .append(Doc::line())
                    .append(Doc::text(format!("{} ", op_str)))
                    .append(format_binop_operand(operand, outer_prec));
            }
            Doc::group(docs![first, Doc::nest(2, tail)])
        }

        ExprKind::UnaryMinus { expr } => {
            docs![Doc::text("-"), format_expr(expr)]
        }

        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            multiline,
        } => {
            let mut chains: Vec<(&Expr, &Expr)> = vec![(cond, then_branch)];
            let mut force_multiline = *multiline;
            let mut final_else = else_branch.as_ref();
            while let ExprKind::If {
                cond: c,
                then_branch: t,
                else_branch: e,
                multiline: ml,
            } = &final_else.kind
            {
                if *ml {
                    force_multiline = true;
                }
                chains.push((c, t));
                final_else = e;
            }
            force_multiline = force_multiline
                || chains.iter().any(|(_, body)| is_block_like(body))
                || is_block_like(final_else);

            if !force_multiline {
                let mut result = Doc::Nil;
                for (i, (c, t)) in chains.iter().enumerate() {
                    if i > 0 {
                        result = result.append(Doc::line());
                    }
                    result = result
                        .append(Doc::text(if i == 0 { "if " } else { "else if " }))
                        .append(Doc::flat(format_expr(c)))
                        .append(Doc::text(" then"))
                        .append(Doc::nest(2, docs![Doc::line(), Doc::flat(format_expr(t))]));
                }
                Doc::group(docs![
                    result,
                    Doc::line(),
                    Doc::text("else"),
                    Doc::nest(2, docs![Doc::line(), Doc::flat(format_expr(final_else))])
                ])
            } else {
                let mut result = Doc::Nil;
                for (i, (condition, body)) in chains.iter().enumerate() {
                    if i > 0 {
                        result = result.append(Doc::hardline());
                    }
                    let head = docs![
                        Doc::text(if i == 0 { "if " } else { "else if " }),
                        Doc::flat(format_expr(condition)),
                        Doc::text(" then")
                    ];
                    result = result.append(format_body_after(head, body));
                }
                result
                    .append(Doc::hardline())
                    .append(format_body_after(Doc::text("else"), final_else))
            }
        }

        ExprKind::Case {
            scrutinee,
            arms,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for (i, ann) in arms.iter().enumerate() {
                if i > 0 {
                    body_items.push(Doc::hardline());
                }
                body_items.push(format_trivia(&ann.leading_trivia));
                body_items.push(format_case_arm_doc(&ann.node));
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("case "),
                Doc::flat(format_expr(scrutinee)),
                Doc::text(" of"),
                Doc::nest(2, docs![Doc::hardline(), body])
            ]
        }

        ExprKind::Block {
            stmts,
            dangling_trivia,
        } => single_expr_block(expr)
            .map(format_expr)
            .unwrap_or_else(|| format_block_contents(stmts, dangling_trivia)),

        ExprKind::Lambda { params, body } => {
            let mut lhs = Doc::text("fun ");
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    lhs = lhs.append(Doc::text(" "));
                }
                lhs = lhs.append(format_pat(p));
            }
            lhs = lhs.append(Doc::text(" ->"));
            format_body_after(lhs, body)
        }

        ExprKind::FieldAccess { expr, field, .. } => {
            // Field access binds tighter than application, so the target must be
            // an atom: `(users_query ()).sql`, not `users_query ().sql` (which
            // reparses as `users_query (().sql)`). format_expr_atom parenthesizes
            // App/etc. while leaving Var/FieldAccess/Tuple/Block bare.
            docs![format_expr_atom(expr), Doc::text(format!(".{}", field))]
        }

        ExprKind::RecordCreate { name, fields, .. } => format_record_create(Some(name), fields),
        ExprKind::AnonRecordCreate { fields } => format_record_create(None, fields),
        ExprKind::RecordBuild {
            context,
            record,
            fields,
            ..
        } => format_record_build(context, record.as_ref(), fields),

        ExprKind::RecordUpdate { record, fields, .. } => {
            let field_docs: Vec<Doc> = fields
                .iter()
                .map(|(name, _, val)| docs![Doc::text(format!("{}: ", name)), format_expr(val)])
                .collect();
            // flat: { u | age: 31, name: "New" }
            // broken: { u |\n  age: 31,\n  name: "New"\n}
            let opener = docs![Doc::text("{ "), format_expr(record), Doc::text(" |")];
            format_comma_list_spaced(opener, "}", field_docs)
        }

        ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            let mut d = if let Some(q) = qualifier {
                Doc::text(format!("{}.{}!", q, name))
            } else {
                Doc::text(format!("{}!", name))
            };
            for arg in args {
                d = d.append(Doc::text(" ")).append(format_expr_atom(arg));
            }
            d
        }

        ExprKind::With { expr, handler } => {
            if has_layout_root(expr) {
                docs![
                    format_expr(expr),
                    Doc::hardline(),
                    format_with_suffix(handler)
                ]
            } else {
                let effective_expr = single_expr_block(expr).unwrap_or(expr);
                let expr_doc = if matches!(effective_expr.kind, ExprKind::With { .. }) {
                    docs![Doc::text("("), format_expr(effective_expr), Doc::text(")")]
                } else {
                    format_expr(effective_expr)
                };
                match handler.as_ref() {
                    Handler::Named(named) => {
                        docs![expr_doc, Doc::text(" with "), Doc::text(&named.name)]
                    }
                    Handler::Inline { .. } => {
                        docs![expr_doc, Doc::text(" "), format_with_suffix(handler)]
                    }
                }
            }
        }

        ExprKind::Resume { value } => {
            docs![Doc::text("resume "), format_expr(value)]
        }

        ExprKind::Tuple { elements } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_expr).collect();
            format_comma_list(Doc::text("("), ")", elem_docs)
        }

        ExprKind::Do {
            bindings,
            success,
            else_arms,
            dangling_trivia,
        } => {
            let mut do_body = Doc::Nil;
            for (i, (pat, expr)) in bindings.iter().enumerate() {
                if i > 0 {
                    do_body = do_body.append(Doc::hardline());
                }
                do_body = do_body.append(format_pat(pat));
                do_body = do_body.append(Doc::text(" <- "));
                do_body = do_body.append(format_expr(expr));
            }
            if !bindings.is_empty() {
                do_body = do_body.append(Doc::hardline());
            }
            do_body = do_body.append(format_expr(success));

            let mut else_items = Vec::new();
            for (i, ann) in else_arms.iter().enumerate() {
                if i > 0 {
                    else_items.push(Doc::hardline());
                }
                else_items.push(format_trivia(&ann.leading_trivia));
                else_items.push(format_case_arm_doc(&ann.node));
                else_items.push(format_trailing(&ann.trailing_comment));
            }
            let else_body = format_braced_body(&else_items, dangling_trivia);

            docs![
                Doc::text("do"),
                Doc::nest(2, docs![Doc::hardline(), do_body]),
                Doc::hardline(),
                Doc::text("else"),
                Doc::nest(2, docs![Doc::hardline(), else_body])
            ]
        }

        ExprKind::Receive {
            arms,
            after_clause,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for (i, ann) in arms.iter().enumerate() {
                if i > 0 {
                    body_items.push(Doc::hardline());
                }
                body_items.push(format_trivia(&ann.leading_trivia));
                body_items.push(format_case_arm_doc(&ann.node));
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            if let Some((timeout, timeout_body)) = after_clause {
                if !arms.is_empty() {
                    body_items.push(Doc::hardline());
                }
                body_items.push(format_body_after(
                    docs![Doc::text("after "), format_expr(timeout), Doc::text(" ->")],
                    timeout_body,
                ));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("receive"),
                Doc::nest(2, docs![Doc::hardline(), body])
            ]
        }

        ExprKind::Ascription { expr, type_expr } => {
            docs![
                Doc::text("("),
                format_expr(expr),
                Doc::text(" : "),
                format_type_expr(type_expr),
                Doc::text(")")
            ]
        }

        // --- Surface syntax sugar ---
        ExprKind::Pipe {
            segments,
            multiline,
        } => {
            let force_multiline = *multiline
                || segments.iter().any(|s| {
                    s.trailing_comment.is_some()
                        || !s.leading_trivia.is_empty()
                        || !s.trailing_trivia.is_empty()
                });
            // Head segment
            let mut head = format_expr(&segments[0].node);
            head = head.append(format_trailing(&segments[0].trailing_comment));

            // Tail segments - same indent level as head (no extra nest)
            let mut tail = Doc::Nil;
            for seg in &segments[1..] {
                if force_multiline {
                    tail = tail.append(Doc::hardline());
                } else {
                    tail = tail.append(Doc::line());
                }
                if !seg.leading_trivia.is_empty() {
                    tail = tail.append(format_trivia(&seg.leading_trivia));
                }
                tail = tail.append(docs![Doc::text("|> "), format_expr(&seg.node)]);
                tail = tail.append(format_trailing(&seg.trailing_comment));
                // Trailing trivia (own-line comments after last segment)
                if !seg.trailing_trivia.is_empty() {
                    tail = tail.append(Doc::hardline());
                    tail = tail.append(format_trivia(&seg.trailing_trivia));
                }
            }

            let result = docs![head, tail];
            if force_multiline {
                result
            } else {
                Doc::group(result)
            }
        }
        ExprKind::BinOpChain {
            segments,
            ops,
            multiline,
        } => {
            let force_multiline = *multiline
                || segments.iter().any(|s| {
                    s.trailing_comment.is_some()
                        || !s.leading_trivia.is_empty()
                        || !s.trailing_trivia.is_empty()
                });

            // All ops in a chain share the same precedence level
            let chain_prec = binop_precedence(&ops[0]);

            // Head segment
            let mut head = format_binop_operand(&segments[0].node, chain_prec);
            head = head.append(format_trailing(&segments[0].trailing_comment));

            // Tail segments: `+ operand` pairs, indented when broken
            let mut tail = Doc::Nil;
            for (i, seg) in segments[1..].iter().enumerate() {
                if force_multiline {
                    tail = tail.append(Doc::hardline());
                } else {
                    tail = tail.append(Doc::line());
                }
                if !seg.leading_trivia.is_empty() {
                    tail = tail.append(format_trivia(&seg.leading_trivia));
                }
                let op_str = format_binop(&ops[i]);
                tail = tail.append(Doc::text(format!("{} ", op_str)));
                tail = tail.append(format_binop_operand(&seg.node, chain_prec));
                tail = tail.append(format_trailing(&seg.trailing_comment));
                if !seg.trailing_trivia.is_empty() {
                    tail = tail.append(Doc::hardline());
                    tail = tail.append(format_trivia(&seg.trailing_trivia));
                }
            }

            let result = docs![head, Doc::nest(2, tail)];
            if force_multiline {
                result
            } else {
                Doc::group(result)
            }
        }
        ExprKind::PipeBack { segments } => format_binary_chain(segments, " <| "),
        ExprKind::ComposeForward { segments } => format_binary_chain(segments, " >> "),
        ExprKind::Cons { head, tail } => {
            docs![format_expr(head), Doc::text(" :: "), format_expr(tail)]
        }
        ExprKind::ListLit {
            elements,
            dangling_trivia,
        } => {
            let has_trivia = !dangling_trivia.is_empty()
                || elements.iter().any(|element| {
                    !element.leading_trivia.is_empty() || element.trailing_comment.is_some()
                });
            if elements.is_empty() && !has_trivia {
                Doc::text("[]")
            } else if has_trivia {
                let mut body_items = Vec::new();
                for element in elements {
                    body_items.push(Doc::hardline());
                    body_items.push(format_trivia(&element.leading_trivia));
                    body_items.push(format_expr(&element.node));
                    body_items.push(Doc::text(","));
                    body_items.push(format_trailing(&element.trailing_comment));
                }
                let body = format_braced_body(&body_items, dangling_trivia);
                docs![
                    Doc::text("["),
                    Doc::nest(2, body),
                    Doc::hardline(),
                    Doc::text("]")
                ]
            } else {
                let elem_docs: Vec<Doc> = elements
                    .iter()
                    .map(|element| format_expr(&element.node))
                    .collect();
                format_comma_list(Doc::text("["), "]", elem_docs)
            }
        }
        ExprKind::StringInterp { parts, kind } => format_interp_string(parts, *kind),
        ExprKind::ListComprehension { body, qualifiers } => {
            let mut parts = vec![Doc::text("["), format_expr(body), Doc::text(" | ")];
            let qual_docs: Vec<Doc> = qualifiers
                .iter()
                .map(|q| match q {
                    ComprehensionQualifier::Generator(pat, expr) => {
                        docs![format_pat(pat), Doc::text(" <- "), format_expr(expr)]
                    }
                    ComprehensionQualifier::Guard(expr) => format_expr(expr),
                    ComprehensionQualifier::Let(pat, expr) => {
                        docs![
                            Doc::text("let "),
                            format_pat(pat),
                            Doc::text(" = "),
                            format_expr(expr)
                        ]
                    }
                })
                .collect();
            parts.push(Doc::join(Doc::text(", "), qual_docs));
            parts.push(Doc::text("]"));
            docs_from_vec(parts)
        }

        ExprKind::HandlerExpr { body } => {
            let header = format_handler_expr_header(body);
            let arms = format_handler_expr_body(body);
            docs![header, Doc::nest(2, docs![Doc::hardline(), arms])]
        }

        ExprKind::BitString { segments } => {
            if segments.is_empty() {
                Doc::text("<<>>")
            } else {
                let seg_docs: Vec<Doc> = segments
                    .iter()
                    .map(|seg| {
                        let mut d = format_expr(&seg.value);
                        if let Some(size) = &seg.size {
                            d = d.append(Doc::text(":")).append(format_expr(size));
                        }
                        if !seg.specs.is_empty() {
                            d = d
                                .append(Doc::text("/"))
                                .append(Doc::text(super::pat::format_bit_specs(&seg.specs)));
                        }
                        d
                    })
                    .collect();
                docs![
                    Doc::text("<<"),
                    Doc::join(Doc::text(", "), seg_docs),
                    Doc::text(">>")
                ]
            }
        }

        // Elaboration-only
        ExprKind::DictMethodAccess { .. }
        | ExprKind::DictSuperAccess { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::ForeignCall { .. } => Doc::text("<elaboration-only>"),
    }
}

/// Format a case arm: `pattern [when guard] -> body`.
/// Block-like bodies stay on the arrow line; other bodies break after `->` when too wide.
fn format_case_arm_doc(arm: &CaseArm) -> Doc {
    let mut lhs = format_pat(&arm.pattern);
    if let Some(g) = &arm.guard {
        lhs = lhs.append(Doc::text(" when ")).append(format_expr(g));
    }
    format_body_after(docs![lhs, Doc::text(" ->")], &arm.body)
}

/// Format an expression in "atom" position (parenthesize if complex).
pub fn format_expr_atom(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::FieldAccess { .. }
        | ExprKind::Tuple { .. }
        | ExprKind::Block { .. }
        | ExprKind::RecordBuild { .. }
        | ExprKind::StringInterp { .. }
        | ExprKind::ListLit { .. }
        | ExprKind::Ascription { .. }
        | ExprKind::BitString { .. } => format_expr(expr),
        _ => docs![Doc::text("("), format_expr(expr), Doc::text(")")],
    }
}

fn format_record_create(name: Option<&String>, fields: &[(String, Span, Expr)]) -> Doc {
    let field_docs: Vec<Doc> = fields
        .iter()
        .map(|(fname, _, val)| docs![Doc::text(format!("{}: ", fname)), format_expr(val)])
        .collect();
    let opener = match name {
        Some(n) => Doc::text(format!("{} {{", n)),
        None => Doc::text("{"),
    };
    // flat: Name { a: 1, b: 2 }
    // broken: Name {\n  a: 1,\n  b: 2,\n}
    format_comma_list_spaced(opener, "}", field_docs)
}

fn format_record_build(
    context: &str,
    record: Option<&String>,
    fields: &[(String, Span, Expr)],
) -> Doc {
    let field_docs: Vec<Doc> = fields
        .iter()
        .map(|(fname, _, val)| docs![Doc::text(format!("{}: ", fname)), format_expr(val)])
        .collect();
    let opener = match record {
        Some(record) => Doc::text(format!("build {} {} {{", context, record)),
        None => Doc::text(format!("build {} {{", context)),
    };
    format_comma_list_spaced(opener, "}", field_docs)
}

/// Format a delimited, comma-separated list with group/break.
/// Flat: `open item1, item2 close`
/// Broken: `open\n  item1,\n  item2,\nclose`
/// Format a delimited, comma-separated list with group/break.
/// When `spaced` is true (records): flat has spaces inside: `{ a, b }`
/// When `spaced` is false (lists, tuples): flat has no spaces: `[a, b]`
fn format_comma_list(open: Doc, close: &str, items: Vec<Doc>) -> Doc {
    format_comma_list_inner(open, close, items, false)
}

fn format_comma_list_spaced(open: Doc, close: &str, items: Vec<Doc>) -> Doc {
    format_comma_list_inner(open, close, items, true)
}

fn format_comma_list_inner(open: Doc, close: &str, items: Vec<Doc>, spaced: bool) -> Doc {
    if items.is_empty() {
        return docs![open, Doc::text(close)];
    }
    let fields_joined = Doc::join(docs![Doc::text(","), Doc::line()], items);
    let trailing_comma = Doc::if_break(Doc::text(","), Doc::Nil);
    // Spaced (records): `{ a, b }` flat, `{\n  a,\n  b,\n}` broken
    // Unspaced (lists, tuples): `[a, b]` flat, `[\n  a,\n  b,\n]` broken
    let pad = if spaced { Doc::line() } else { Doc::softline() };
    Doc::group(docs![
        open,
        Doc::nest(2, docs![pad.clone(), fields_joined, trailing_comma]),
        pad,
        Doc::text(close)
    ])
}

fn format_with_suffix(handler: &Handler) -> Doc {
    match handler {
        Handler::Named(named) => Doc::text(format!("with {}", named.name)),
        Handler::Inline {
            items,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for (i, ann) in items.iter().enumerate() {
                if i > 0 {
                    body_items.push(Doc::hardline());
                }
                body_items.push(format_trivia(&ann.leading_trivia));
                match &ann.node {
                    HandlerItem::Named(r) => {
                        body_items.push(Doc::text(format!("{},", r.name)));
                    }
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        body_items.push(format_handler_arm(arm));
                    }
                }
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("with"),
                Doc::nest(2, docs![Doc::hardline(), body])
            ]
        }
    }
}

pub fn format_stmt(stmt: &Stmt) -> Doc {
    match stmt {
        Stmt::Let {
            pattern,
            annotation,
            value,
            assert,
            ..
        } => {
            let kw = if *assert { "let! " } else { "let " };
            let mut lhs = Doc::text(kw).append(format_pat(pattern));
            if let Some(ty) = annotation {
                lhs = lhs.append(Doc::text(": ")).append(format_type_expr(ty));
            }
            super::decl::format_binding(lhs, value)
        }
        Stmt::LetFun {
            name,
            params,
            guard,
            body,
            ..
        } => {
            let mut lhs = Doc::text(format!("let {}", name));
            for p in params {
                lhs = lhs.append(Doc::text(" ")).append(format_pat(p));
            }
            if let Some(g) = guard {
                lhs = lhs.append(Doc::text(" when ")).append(format_expr(g));
            }
            super::decl::format_binding(lhs, body)
        }

        Stmt::Expr(expr) => format_expr(expr),
    }
}

/// Format an interpolated string, choosing single-line or triple-quoted form.
fn format_interp_string(parts: &[StringPart], kind: StringKind) -> Doc {
    match kind {
        StringKind::InterpolatedMultiline => format_interp_multiline(parts),
        _ => format_interp_single_line(parts),
    }
}

/// Format a single-line interpolated string: `$"text {expr} text"`.
fn format_interp_single_line(parts: &[StringPart]) -> Doc {
    let mut parts_doc = vec![Doc::text("$\"")];
    for part in parts {
        match part {
            StringPart::Lit(text) => parts_doc.push(Doc::text(escape_string(text))),
            StringPart::Expr(expr) => {
                parts_doc.push(Doc::text("{"));
                parts_doc.push(Doc::flat(format_expr(expr)));
                parts_doc.push(Doc::text("}"));
            }
        }
    }
    parts_doc.push(Doc::text("\""));
    docs_from_vec(parts_doc)
}

/// Format a multiline interpolated string: `$"""\n  text {expr}\n  """`.
fn format_interp_multiline(parts: &[StringPart]) -> Doc {
    // Walk parts, building Doc fragments per line. Literal text is split at
    // newlines; expression holes stay as Doc::flat nodes on their current line.
    let mut inner = Vec::new();
    // Fragments accumulating for the current line
    let mut line_frags: Vec<Doc> = Vec::new();

    let flush_line = |inner: &mut Vec<Doc>, line_frags: &mut Vec<Doc>| {
        inner.push(Doc::hardline());
        if !line_frags.is_empty() {
            inner.append(line_frags);
        }
    };

    for part in parts {
        match part {
            StringPart::Lit(text) => {
                let mut first = true;
                for segment in text.split('\n') {
                    if !first {
                        flush_line(&mut inner, &mut line_frags);
                    }
                    if !segment.is_empty() {
                        line_frags.push(Doc::text(segment.to_string()));
                    }
                    first = false;
                }
            }
            StringPart::Expr(expr) => {
                line_frags.push(Doc::text("{"));
                line_frags.push(Doc::flat(format_expr(expr)));
                line_frags.push(Doc::text("}"));
            }
        }
    }

    // Emit remaining line content
    flush_line(&mut inner, &mut line_frags);
    inner.push(Doc::hardline());
    inner.push(Doc::text("\"\"\""));

    Doc::text("$\"\"\"").append(Doc::nest(2, docs_from_vec(inner)))
}

/// Format the header of a handler expression: `handler for Log`
/// (no hardlines — safe to wrap in Doc::group for width-based breaking).
pub fn format_handler_expr_header(body: &crate::ast::HandlerBody) -> Doc {
    let mut parts = Vec::new();
    parts.push(Doc::text("handler for "));
    let eff_docs: Vec<Doc> = body
        .effects
        .iter()
        .map(super::type_expr::format_effect_ref)
        .collect();
    parts.push(Doc::join(Doc::text(", "), eff_docs));
    if !body.needs.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(super::type_expr::format_needs(&body.needs, &[]));
    }
    if !body.where_clause.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(super::type_expr::format_where_clause(&body.where_clause));
    }
    docs_from_vec(parts)
}

/// Format the arms of a handler expression (with hardlines between arms).
pub fn format_handler_expr_body(body: &crate::ast::HandlerBody) -> Doc {
    let mut body_items = Vec::new();
    for (i, ann) in body.arms.iter().enumerate() {
        if i > 0 {
            body_items.push(Doc::hardline());
        }
        body_items.push(format_trivia(&ann.leading_trivia));
        body_items.push(format_handler_arm(&ann.node));
        body_items.push(format_trailing(&ann.trailing_comment));
    }
    if let Some(rc) = &body.return_clause {
        if !body.arms.is_empty() {
            body_items.push(Doc::hardline());
        }
        body_items.push(format_handler_arm(rc));
    }
    format_braced_body(&body_items, &[])
}
