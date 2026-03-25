use crate::ast::*;
use super::Doc;

pub fn format_lit(lit: &Lit) -> Doc {
    Doc::text(format_lit_raw(lit))
}

pub fn format_lit_raw(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => n.to_string(),
        Lit::Float(f) => format!("{}", f),
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
    let lines: Vec<Doc> = doc.iter().map(|line| Doc::text(format!("#@ {}", line))).collect();
    Doc::join(Doc::hardline(), lines)
}

/// Concatenate a Vec<Doc> into a single Doc.
pub fn docs_from_vec(docs: Vec<Doc>) -> Doc {
    let mut result = Doc::Nil;
    for d in docs {
        result = result.append(d);
    }
    result
}
