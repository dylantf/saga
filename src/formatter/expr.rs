use super::Doc;
use super::helpers::{docs_from_vec, format_binop, format_trivia, format_trailing};
use super::pat::format_pat;
use super::type_expr::format_type_expr;
use crate::ast::*;
use crate::docs;
use crate::token::Span;

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
            docs![
                Doc::text("if "),
                format_expr(cond),
                Doc::text(" then "),
                format_expr(then_branch),
                Doc::hardline(),
                Doc::text("else "),
                format_expr(else_branch),
            ]
        }

        ExprKind::Case { scrutinee, arms } => {
            let mut parts = vec![Doc::text("case "), format_expr(scrutinee), Doc::text(" {")];
            for ann in arms {
                let arm = &ann.node;
                parts.push(Doc::hardline());
                parts.push(format_trivia(&ann.leading_trivia));
                parts.push(Doc::text("  "));
                parts.push(format_pat(&arm.pattern));
                if let Some(g) = &arm.guard {
                    parts.push(Doc::text(" | "));
                    parts.push(format_expr(g));
                }
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(&arm.body));
                parts.push(format_trailing(&ann.trailing_comment));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }

        ExprKind::Block { stmts } => {
            if stmts.len() == 1
                && let Stmt::Expr(e) = &stmts[0].node
            {
                return format_expr(e);
            }
            let mut parts = vec![Doc::text("{")];
            for ann in stmts {
                parts.push(Doc::hardline());
                parts.push(format_trivia(&ann.leading_trivia));
                parts.push(Doc::text("  "));
                parts.push(format_stmt(&ann.node));
                parts.push(format_trailing(&ann.trailing_comment));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
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
        } => {
            let mut parts = vec![Doc::text("do {")];
            for (pat, expr) in bindings {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  "));
                parts.push(format_pat(pat));
                parts.push(Doc::text(" <- "));
                parts.push(format_expr(expr));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("  "));
            parts.push(format_expr(success));
            parts.push(Doc::hardline());
            parts.push(Doc::text("} else {"));
            for ann in else_arms {
                let arm = &ann.node;
                parts.push(Doc::hardline());
                parts.push(format_trivia(&ann.leading_trivia));
                parts.push(Doc::text("  "));
                parts.push(format_pat(&arm.pattern));
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(&arm.body));
                parts.push(format_trailing(&ann.trailing_comment));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }

        ExprKind::Receive { arms, after_clause } => {
            let mut parts = vec![Doc::text("receive {")];
            for ann in arms {
                let arm = &ann.node;
                parts.push(Doc::hardline());
                parts.push(format_trivia(&ann.leading_trivia));
                parts.push(Doc::text("  "));
                parts.push(format_pat(&arm.pattern));
                if let Some(g) = &arm.guard {
                    parts.push(Doc::text(" | "));
                    parts.push(format_expr(g));
                }
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(&arm.body));
                parts.push(format_trailing(&ann.trailing_comment));
            }
            if let Some((timeout, body)) = after_clause {
                parts.push(Doc::hardline());
                parts.push(Doc::text("  after "));
                parts.push(format_expr(timeout));
                parts.push(Doc::text(" -> "));
                parts.push(format_expr(body));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
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
        ExprKind::Pipe { .. } => {
            // Flatten left-nested pipe chain: a |> b |> c is Pipe(Pipe(a, b), c)
            let mut segments = Vec::new();
            collect_pipe_chain(expr, &mut segments);
            let head = format_expr(segments[0]);
            let mut parts = vec![head];
            for seg in &segments[1..] {
                parts.push(Doc::line());
                parts.push(docs![Doc::text("|> "), format_expr(seg)]);
            }
            Doc::group(docs_from_vec(parts))
        }
        ExprKind::PipeBack { left, right } => {
            docs![format_expr(left), Doc::text(" <| "), format_expr(right)]
        }
        ExprKind::ComposeForward { left, right } => {
            docs![format_expr(left), Doc::text(" >> "), format_expr(right)]
        }
        ExprKind::ComposeBack { left, right } => {
            docs![format_expr(left), Doc::text(" << "), format_expr(right)]
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
            ..
        } => {
            let mut parts = vec![Doc::text("{")];
            for name in named {
                parts.push(Doc::hardline());
                parts.push(Doc::text(format!("  {},", name)));
            }
            for ann in arms {
                parts.push(Doc::hardline());
                parts.push(format_trivia(&ann.leading_trivia));
                parts.push(format_handler_arm(&ann.node));
                parts.push(Doc::text(","));
                parts.push(format_trailing(&ann.trailing_comment));
            }
            if let Some(rc) = return_clause {
                parts.push(Doc::hardline());
                parts.push(format_handler_arm(rc));
                parts.push(Doc::text(","));
            }
            parts.push(Doc::hardline());
            parts.push(Doc::text("}"));
            docs_from_vec(parts)
        }
    }
}

fn format_handler_arm(arm: &HandlerArm) -> Doc {
    let mut d = Doc::text(format!("  {}", arm.op_name));
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

/// Flatten a left-nested pipe chain into a list of segments.
/// `a |> b |> c` (= Pipe(Pipe(a, b), c)) becomes [a, b, c].
fn collect_pipe_chain<'a>(expr: &'a Expr, segments: &mut Vec<&'a Expr>) {
    match &expr.kind {
        ExprKind::Pipe { left, right } => {
            collect_pipe_chain(left, segments);
            segments.push(right);
        }
        _ => segments.push(expr),
    }
}
