use super::Doc;
use super::helpers::{docs_from_vec, format_binop, format_trivia, format_trivia_dangling, format_trailing};
use super::pat::format_pat;
use super::type_expr::format_type_expr;
use crate::ast::*;
use crate::docs;
use crate::token::Span;

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

/// Build a nested body for a braced block: each item gets a hardline before it,
/// trivia is emitted inline, and dangling trivia omits its trailing hardline.
/// The result should be wrapped in `Doc::nest(indent, body)`.
fn format_braced_body(
    items: &[Doc],
    dangling_trivia: &[Trivia],
) -> Doc {
    let mut body = Doc::Nil;
    for item in items {
        body = body.append(item.clone());
    }
    if !dangling_trivia.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling_trivia));
    }
    body
}

pub fn format_expr(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { value } => super::helpers::format_lit(value),
        ExprKind::Var { name } => Doc::text(name),
        ExprKind::Constructor { name } => Doc::text(name),
        ExprKind::QualifiedName { module, name } => Doc::text(format!("{}.{}", module, name)),

        ExprKind::App { func, arg } => {
            let func_doc = format_expr(func);
            let arg_doc = match &arg.kind {
                ExprKind::App { .. } | ExprKind::BinOp { .. } => {
                    docs![Doc::text("("), format_expr(arg), Doc::text(")")]
                }
                _ => format_expr(arg),
            };
            docs![func_doc, Doc::text(" "), arg_doc]
        }

        ExprKind::BinOp { op, left, right } => {
            let op_str = format_binop(op);
            docs![
                format_expr(left),
                Doc::text(format!(" {} ", op_str)),
                format_expr(right)
            ]
        }

        ExprKind::UnaryMinus { expr } => {
            docs![Doc::text("-"), format_expr(expr)]
        }

        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            Doc::group(docs![
                Doc::text("if "),
                format_expr(cond),
                Doc::text(" then "),
                format_expr(then_branch),
                Doc::line(),
                Doc::text("else "),
                format_expr(else_branch),
            ])
        }

        ExprKind::Case { scrutinee, arms, dangling_trivia } => {
            let mut body_items = Vec::new();
            for ann in arms {
                let arm = &ann.node;
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                let mut arm_doc = format_pat(&arm.pattern);
                if let Some(g) = &arm.guard {
                    arm_doc = arm_doc.append(Doc::text(" | ")).append(format_expr(g));
                }
                arm_doc = arm_doc.append(Doc::text(" -> ")).append(format_expr(&arm.body));
                body_items.push(arm_doc);
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("case "),
                format_expr(scrutinee),
                Doc::text(" {"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Block { stmts, dangling_trivia } => {
            let mut body_items = Vec::new();
            for ann in stmts {
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                body_items.push(format_stmt(&ann.node));
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("{"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Lambda { params, body } => {
            let mut d = Doc::text("fun ");
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    d = d.append(Doc::text(" "));
                }
                d = d.append(format_pat(p));
            }
            d = d.append(Doc::text(" -> ")).append(format_expr(body));
            d
        }

        ExprKind::FieldAccess { expr, field } => {
            docs![format_expr(expr), Doc::text(format!(".{}", field))]
        }

        ExprKind::RecordCreate { name, fields } => format_record_create(Some(name), fields),
        ExprKind::AnonRecordCreate { fields } => format_record_create(None, fields),

        ExprKind::RecordUpdate { record, fields } => {
            let field_docs: Vec<Doc> = fields
                .iter()
                .map(|(name, _, val)| docs![Doc::text(format!("{}: ", name)), format_expr(val)])
                .collect();
            Doc::group(docs![
                Doc::text("{ "),
                format_expr(record),
                Doc::text(" | "),
                Doc::join(Doc::text(", "), field_docs),
                Doc::text(" }"),
            ])
        }

        ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            let mut d = match qualifier {
                Some(q) => Doc::text(format!("{}.{}!", q, name)),
                None => Doc::text(format!("{}!", name)),
            };
            for arg in args {
                d = d.append(Doc::text(" ")).append(format_expr_atom(arg));
            }
            d
        }

        ExprKind::With { expr, handler } => {
            let expr_doc = format_expr(expr);
            let handler_doc = format_handler(handler);
            docs![expr_doc, Doc::text(" with "), handler_doc]
        }

        ExprKind::Resume { value } => {
            docs![Doc::text("resume "), format_expr(value)]
        }

        ExprKind::Tuple { elements } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_expr).collect();
            docs![
                Doc::text("("),
                Doc::join(Doc::text(", "), elem_docs),
                Doc::text(")")
            ]
        }

        ExprKind::Do {
            bindings,
            success,
            else_arms,
            dangling_trivia,
        } => {
            let mut do_body = Doc::Nil;
            for (pat, expr) in bindings {
                do_body = do_body.append(Doc::hardline());
                do_body = do_body.append(format_pat(pat));
                do_body = do_body.append(Doc::text(" <- "));
                do_body = do_body.append(format_expr(expr));
            }
            do_body = do_body.append(Doc::hardline()).append(format_expr(success));

            let mut else_items = Vec::new();
            for ann in else_arms {
                let arm = &ann.node;
                else_items.push(Doc::hardline());
                else_items.push(format_trivia(&ann.leading_trivia));
                let arm_doc = docs![
                    format_pat(&arm.pattern),
                    Doc::text(" -> "),
                    format_expr(&arm.body)
                ];
                else_items.push(arm_doc);
                else_items.push(format_trailing(&ann.trailing_comment));
            }
            let else_body = format_braced_body(&else_items, dangling_trivia);

            docs![
                Doc::text("do {"),
                Doc::nest(2, do_body),
                Doc::hardline(),
                Doc::text("} else {"),
                Doc::nest(2, else_body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }

        ExprKind::Receive { arms, after_clause, dangling_trivia } => {
            let mut body_items = Vec::new();
            for ann in arms {
                let arm = &ann.node;
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                let mut arm_doc = format_pat(&arm.pattern);
                if let Some(g) = &arm.guard {
                    arm_doc = arm_doc.append(Doc::text(" | ")).append(format_expr(g));
                }
                arm_doc = arm_doc.append(Doc::text(" -> ")).append(format_expr(&arm.body));
                body_items.push(arm_doc);
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            if let Some((timeout, timeout_body)) = after_clause {
                body_items.push(Doc::hardline());
                body_items.push(docs![
                    Doc::text("after "),
                    format_expr(timeout),
                    Doc::text(" -> "),
                    format_expr(timeout_body)
                ]);
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("receive {"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
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
        ExprKind::Pipe { segments } => {
            let has_trivia = segments.iter().any(|s| {
                s.trailing_comment.is_some() || !s.leading_trivia.is_empty()
            });
            // Head segment (not indented)
            let mut head = format_expr(&segments[0].node);
            head = head.append(format_trailing(&segments[0].trailing_comment));

            // Tail segments (indented via nest)
            let mut tail = Doc::Nil;
            for seg in &segments[1..] {
                if has_trivia {
                    tail = tail.append(Doc::hardline());
                } else {
                    tail = tail.append(Doc::line());
                }
                if !seg.leading_trivia.is_empty() {
                    tail = tail.append(format_trivia(&seg.leading_trivia));
                }
                tail = tail.append(docs![Doc::text("|> "), format_expr(&seg.node)]);
                tail = tail.append(format_trailing(&seg.trailing_comment));
            }

            let result = docs![head, Doc::nest(2, tail)];
            if has_trivia {
                result
            } else {
                Doc::group(result)
            }
        }
        ExprKind::PipeBack { segments } => {
            format_binary_chain(segments, " <| ")
        }
        ExprKind::ComposeForward { segments } => {
            format_binary_chain(segments, " >> ")
        }
        ExprKind::ComposeBack { segments } => {
            format_binary_chain(segments, " << ")
        }
        ExprKind::Cons { head, tail } => {
            docs![format_expr(head), Doc::text(" :: "), format_expr(tail)]
        }
        ExprKind::ListLit { elements } => {
            if elements.is_empty() {
                Doc::text("[]")
            } else {
                let elem_docs: Vec<Doc> = elements.iter().map(format_expr).collect();
                docs![
                    Doc::text("["),
                    Doc::join(Doc::text(", "), elem_docs),
                    Doc::text("]")
                ]
            }
        }
        ExprKind::StringInterp { parts } => {
            let mut s = String::from("$\"");
            for part in parts {
                match part {
                    StringPart::Lit(text) => s.push_str(text),
                    StringPart::Expr(_) => s.push_str("{...}"), // TODO: format expr inside
                }
            }
            s.push('"');
            Doc::text(s)
        }
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

        // Elaboration-only
        ExprKind::DictMethodAccess { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::ForeignCall { .. } => Doc::text("<elaboration-only>"),
    }
}

/// Format an expression in "atom" position (parenthesize if complex).
pub fn format_expr_atom(expr: &Expr) -> Doc {
    match &expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::Tuple { .. }
        | ExprKind::Block { .. } => format_expr(expr),
        _ => docs![Doc::text("("), format_expr(expr), Doc::text(")")],
    }
}

fn format_record_create(name: Option<&String>, fields: &[(String, Span, Expr)]) -> Doc {
    let field_docs: Vec<Doc> = fields
        .iter()
        .map(|(fname, _, val)| docs![Doc::text(format!("{}: ", fname)), format_expr(val)])
        .collect();
    let mut d = match name {
        Some(n) => Doc::text(format!("{} {{ ", n)),
        None => Doc::text("{ "),
    };
    d = d.append(Doc::join(Doc::text(", "), field_docs));
    d.append(Doc::text(" }"))
}

fn format_handler(handler: &Handler) -> Doc {
    match handler {
        Handler::Named(name, _) => Doc::text(name),
        Handler::Inline {
            named,
            arms,
            return_clause,
            dangling_trivia,
        } => {
            let mut body_items = Vec::new();
            for name in named {
                body_items.push(Doc::hardline());
                body_items.push(Doc::text(format!("{},", name)));
            }
            for ann in arms {
                body_items.push(Doc::hardline());
                body_items.push(format_trivia(&ann.leading_trivia));
                body_items.push(format_handler_arm(&ann.node));
                body_items.push(Doc::text(","));
                body_items.push(format_trailing(&ann.trailing_comment));
            }
            if let Some(rc) = return_clause {
                body_items.push(Doc::hardline());
                body_items.push(format_handler_arm(rc));
                body_items.push(Doc::text(","));
            }
            let body = format_braced_body(&body_items, dangling_trivia);
            docs![
                Doc::text("{"),
                Doc::nest(2, body),
                Doc::hardline(),
                Doc::text("}")
            ]
        }
    }
}

fn format_handler_arm(arm: &HandlerArm) -> Doc {
    let mut d = Doc::text(&arm.op_name);
    for (param, _) in &arm.params {
        d = d.append(Doc::text(format!(" {}", param)));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(&arm.body));
    d
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
            let mut d = Doc::text(kw).append(format_pat(pattern));
            if let Some(ty) = annotation {
                d = d.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            d.append(Doc::text(" = ")).append(format_expr(value))
        }
        Stmt::LetFun {
            name,
            params,
            guard,
            body,
            ..
        } => {
            let mut d = Doc::text(format!("let {}", name));
            for p in params {
                d = d.append(Doc::text(" ")).append(format_pat(p));
            }
            if let Some(g) = guard {
                d = d.append(Doc::text(" | ")).append(format_expr(g));
            }
            d.append(Doc::text(" = ")).append(format_expr(body))
        }
        Stmt::Expr(expr) => format_expr(expr),
    }
}
