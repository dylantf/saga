use crate::ast::*;
use crate::docs;
use super::Doc;
use super::helpers::format_lit;

pub fn format_pat(pat: &Pat) -> Doc {
    match pat {
        Pat::Wildcard { .. } => Doc::text("_"),
        Pat::Var { name, .. } => Doc::text(name),
        Pat::Lit { value, .. } => format_lit(value),
        Pat::Constructor { name, args, .. } => {
            if args.is_empty() {
                Doc::text(name)
            } else {
                let arg_docs: Vec<Doc> = args.iter().map(format_pat).collect();
                docs![Doc::text(format!("{}(", name)), Doc::join(Doc::text(", "), arg_docs), Doc::text(")")]
            }
        }
        Pat::Record { name, fields, as_name, .. } => {
            let mut d = if fields.is_empty() {
                Doc::text(format!("{} {{}}", name))
            } else {
                let field_docs: Vec<Doc> = fields.iter().map(|(fname, alias)| {
                    match alias {
                        Some(p) => docs![Doc::text(format!("{}: ", fname)), format_pat(p)],
                        None => Doc::text(fname),
                    }
                }).collect();
                docs![Doc::text(format!("{} {{ ", name)), Doc::join(Doc::text(", "), field_docs), Doc::text(" }")]
            };
            if let Some(a) = as_name {
                d = d.append(Doc::text(format!(" as {}", a)));
            }
            d
        }
        Pat::AnonRecord { fields, .. } => {
            let field_docs: Vec<Doc> = fields.iter().map(|(fname, alias)| {
                match alias {
                    Some(p) => docs![Doc::text(format!("{}: ", fname)), format_pat(p)],
                    None => Doc::text(fname),
                }
            }).collect();
            docs![Doc::text("{ "), Doc::join(Doc::text(", "), field_docs), Doc::text(" }")]
        }
        Pat::Tuple { elements, .. } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_pat).collect();
            docs![Doc::text("("), Doc::join(Doc::text(", "), elem_docs), Doc::text(")")]
        }
        Pat::StringPrefix { prefix, rest, .. } => {
            docs![Doc::text(format!("\"{}\" <> ", prefix)), format_pat(rest)]
        }
        Pat::ListPat { elements, .. } => {
            if elements.is_empty() {
                Doc::text("[]")
            } else {
                let elem_docs: Vec<Doc> = elements.iter().map(format_pat).collect();
                docs![Doc::text("["), Doc::join(Doc::text(", "), elem_docs), Doc::text("]")]
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            docs![format_pat(head), Doc::text(" :: "), format_pat(tail)]
        }
    }
}

/// Format a pattern in "atom" position (function params, constructor args).
/// Wraps patterns that contain spaces in parens to avoid ambiguity.
pub fn format_pat_atom(pat: &Pat) -> Doc {
    match pat {
        Pat::Wildcard { .. }
        | Pat::Var { .. }
        | Pat::Lit { .. }
        | Pat::Tuple { .. }
        | Pat::AnonRecord { .. }
        | Pat::ListPat { .. } => format_pat(pat),
        // Constructor with no args is just a name - no parens needed
        Pat::Constructor { args, .. } if args.is_empty() => format_pat(pat),
        // Record with no as_name and no fields is just `Name {}` - no parens needed
        Pat::Record { fields, as_name: None, .. } if fields.is_empty() => format_pat(pat),
        _ => docs![Doc::text("("), format_pat(pat), Doc::text(")")],
    }
}
