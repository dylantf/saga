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
                // All constructor args are space-separated: `Ok x`, `Pair a b`, `Ok ()`
                let mut d = Doc::text(name);
                for a in args {
                    d = d.append(Doc::text(" ")).append(format_pat_atom(a));
                }
                d
            }
        }
        Pat::Record { name, fields, rest, as_name, .. } => {
            let mut d = if fields.is_empty() && *rest {
                Doc::text(format!("{} {{ .. }}", name))
            } else if fields.is_empty() {
                Doc::text(format!("{} {{}}", name))
            } else {
                let mut parts: Vec<Doc> = fields.iter().map(|(fname, alias)| {
                    match alias {
                        Some(p) => docs![Doc::text(format!("{}: ", fname)), format_pat(p)],
                        None => Doc::text(fname),
                    }
                }).collect();
                if *rest {
                    parts.push(Doc::text(".."));
                }
                docs![Doc::text(format!("{} {{ ", name)), Doc::join(Doc::text(", "), parts), Doc::text(" }")]
            };
            if let Some(a) = as_name {
                d = d.append(Doc::text(format!(" as {}", a)));
            }
            d
        }
        Pat::AnonRecord { fields, rest, .. } => {
            let mut parts: Vec<Doc> = fields.iter().map(|(fname, alias)| {
                match alias {
                    Some(p) => docs![Doc::text(format!("{}: ", fname)), format_pat(p)],
                    None => Doc::text(fname),
                }
            }).collect();
            if *rest {
                parts.push(Doc::text(".."));
            }
            docs![Doc::text("{ "), Doc::join(Doc::text(", "), parts), Doc::text(" }")]
        }
        Pat::Tuple { elements, .. } => {
            let elem_docs: Vec<Doc> = elements.iter().map(format_pat).collect();
            docs![Doc::text("("), Doc::join(Doc::text(", "), elem_docs), Doc::text(")")]
        }
        Pat::StringPrefix { prefix, rest, .. } => {
            docs![Doc::text(format!("\"{}\" <> ", prefix)), format_pat(rest)]
        }
        Pat::BitStringPat { segments, .. } => {
            if segments.is_empty() {
                Doc::text("<<>>")
            } else {
                let seg_docs: Vec<Doc> = segments.iter().map(format_bit_segment_pat).collect();
                docs![Doc::text("<<"), Doc::join(Doc::text(", "), seg_docs), Doc::text(">>")]
            }
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
        Pat::Or { patterns, .. } => {
            let pat_docs: Vec<Doc> = patterns.iter().map(format_pat).collect();
            Doc::join(Doc::text(" | "), pat_docs)
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
        // Record with no as_name is just `Name {}` or `Name { .. }` - no parens needed
        Pat::Record { as_name: None, .. } => format_pat(pat),
        // BitString is self-delimited by << >>
        Pat::BitStringPat { .. } => format_pat(pat),
        _ => docs![Doc::text("("), format_pat(pat), Doc::text(")")],
    }
}

fn format_bit_segment_pat(seg: &BitSegment<Pat>) -> Doc {
    let mut d = format_pat(&seg.value);
    if let Some(size) = &seg.size {
        d = d.append(Doc::text(":")).append(super::expr::format_expr(size));
    }
    if !seg.specs.is_empty() {
        d = d.append(Doc::text("/")).append(Doc::text(format_bit_specs(&seg.specs)));
    }
    d
}

pub fn format_bit_specs(specs: &[BitSegSpec]) -> String {
    specs.iter().map(|s| match s {
        BitSegSpec::Integer => "integer",
        BitSegSpec::Float => "float",
        BitSegSpec::Binary => "binary",
        BitSegSpec::Utf8 => "utf8",
        BitSegSpec::Big => "big",
        BitSegSpec::Little => "little",
        BitSegSpec::Native => "native",
        BitSegSpec::Signed => "signed",
        BitSegSpec::Unsigned => "unsigned",
    }).collect::<Vec<_>>().join("-")
}
