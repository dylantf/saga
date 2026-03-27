use super::Doc;
use crate::ast::*;

pub fn format_lit(lit: &Lit) -> Doc {
    Doc::text(format_lit_raw(lit))
}

pub fn format_lit_raw(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => n.to_string(),
        Lit::Float(f) => {
            let s = format!("{}", f);
            if s.contains('.') {
                s
            } else {
                format!("{}.0", s)
            }
        }
        Lit::String(s) => format!("\"{}\"", s),
        Lit::Bool(true) => "True".to_string(),
        Lit::Bool(false) => "False".to_string(),
        Lit::Unit => "()".to_string(),
    }
}

pub fn format_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::FloatDiv | BinOp::IntDiv => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "==",
        BinOp::NotEq => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::LtEq => "<=",
        BinOp::GtEq => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Concat => "<>",
    }
}

pub fn format_doc_comment(doc: &[String]) -> Doc {
    let lines: Vec<Doc> = doc
        .iter()
        .map(|line| Doc::text(format!("#@ {}", line)))
        .collect();
    Doc::join(Doc::hardline(), lines)
}

/// Format trivia (blank lines, comments, doc comments) into Doc nodes.
pub fn format_trivia(trivia: &[Trivia]) -> Doc {
    let mut parts = Vec::new();
    for item in trivia {
        match item {
            Trivia::BlankLines(_) => {
                parts.push(Doc::hardline());
            }
            Trivia::Comment(text) => {
                parts.push(Doc::text(format!("# {}", text)));
                parts.push(Doc::hardline());
            }
            Trivia::DocComment(text) => {
                parts.push(Doc::text(format!("#@ {}", text)));
                parts.push(Doc::hardline());
            }
        }
    }
    docs_from_vec(parts)
}

/// Format trivia in "dangling" position (end of a braced block, before `}`).
/// Same as `format_trivia` but omits the trailing hardline on the last comment,
/// since the caller will emit its own hardline before the closing brace.
pub fn format_trivia_dangling(trivia: &[Trivia]) -> Doc {
    let mut parts = Vec::new();
    let len = trivia.len();
    for (i, item) in trivia.iter().enumerate() {
        let is_last = i == len - 1;
        match item {
            Trivia::BlankLines(_) => {
                parts.push(Doc::hardline());
            }
            Trivia::Comment(text) => {
                parts.push(Doc::text(format!("# {}", text)));
                if !is_last {
                    parts.push(Doc::hardline());
                }
            }
            Trivia::DocComment(text) => {
                parts.push(Doc::text(format!("#@ {}", text)));
                if !is_last {
                    parts.push(Doc::hardline());
                }
            }
        }
    }
    docs_from_vec(parts)
}

/// Format a trailing comment (if any) as ` # text`.
pub fn format_trailing(comment: &Option<String>) -> Doc {
    match comment {
        Some(text) => Doc::text(format!(" # {}", text)),
        None => Doc::Nil,
    }
}

/// Concatenate a Vec<Doc> into a single Doc.
pub fn docs_from_vec(docs: Vec<Doc>) -> Doc {
    let mut result = Doc::Nil;
    for d in docs {
        result = result.append(d);
    }
    result
}
