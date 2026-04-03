use super::Doc;
use crate::ast::*;
use crate::token::StringKind;

pub fn format_lit(lit: &Lit) -> Doc {
    match lit {
        Lit::String(s, kind) => format_string_lit(s, *kind),
        _ => Doc::text(format_lit_raw(lit)),
    }
}

pub fn format_lit_raw(lit: &Lit) -> String {
    match lit {
        Lit::Int(s, _) => s.clone(),
        Lit::Float(s, _) => s.clone(),
        Lit::String(s, kind) => match kind {
            StringKind::Normal => format!("\"{}\"", escape_string(s)),
            StringKind::Raw => format!("@\"{}\"", s),
            _ => format!("\"{}\"", escape_string(s)),
        },
        Lit::Bool(true) => "True".to_string(),
        Lit::Bool(false) => "False".to_string(),
        Lit::Unit => "()".to_string(),
    }
}

/// Escape special characters for a regular (non-raw) string literal.
pub fn escape_string(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            ch => out.push(ch),
        }
    }
    out
}

/// Format a string literal, choosing single-line or triple-quoted form based on StringKind.
fn format_string_lit(s: &str, kind: StringKind) -> Doc {
    match kind {
        StringKind::Normal => Doc::text(format!("\"{}\"", escape_string(s))),
        StringKind::Raw => Doc::text(format!("@\"{}\"", s)),
        StringKind::Multiline => format_multiline_string_doc(s, "\"\"\"", "\"\"\""),
        StringKind::RawMultiline => format_multiline_string_doc(s, "@\"\"\"", "\"\"\""),
        // Interpolated kinds shouldn't appear in Lit::String, but handle gracefully
        StringKind::Interpolated | StringKind::InterpolatedMultiline => {
            Doc::text(format!("\"{}\"", escape_string(s)))
        }
    }
}

/// Build a Doc for a triple-quoted string: `"""\n  content\n  """`.
/// Content lines and the closing delimiter are nested +2 from current indent.
fn format_multiline_string_doc(content: &str, open: &str, close: &str) -> Doc {
    let lines: Vec<&str> = content.split('\n').collect();
    let mut inner = Vec::new();
    for line in &lines {
        inner.push(Doc::hardline());
        if !line.is_empty() {
            inner.push(Doc::text(line.to_string()));
        }
    }
    inner.push(Doc::hardline());
    inner.push(Doc::text(close));
    Doc::text(open).append(Doc::nest(2, docs_from_vec(inner)))
}

pub fn format_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::FloatDiv | BinOp::IntDiv => "/",
        BinOp::Mod | BinOp::FloatMod => "%",
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

/// Emit a doc comment block (if non-empty) followed by a hardline,
/// as a preamble to a definition.
pub fn format_doc_preamble(doc: &[String], parts: &mut Vec<Doc>) {
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }
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
        Some(text) => Doc::TrailingComment(text.clone()),
        None => Doc::Nil,
    }
}

/// Format a handler arm: `op_name params = body`.
/// Zero-arg effect ops get explicit `()` since the parser strips it.
pub fn format_handler_arm(arm: &crate::ast::HandlerArm) -> Doc {
    let mut d = if let Some(ref q) = arm.qualifier {
        Doc::text(format!("{}.{}", q, arm.op_name))
    } else {
        Doc::text(&arm.op_name)
    };
    if arm.params.is_empty() {
        // Zero-arg effect ops need explicit () in handler arms
        d = d.append(Doc::text(" ()"));
    } else {
        for (param, _) in &arm.params {
            d = d.append(Doc::text(format!(" {}", param)));
        }
    }
    d = d.append(Doc::text(" = ")).append(super::expr::format_expr(&arm.body));
    if let Some(ref finally_expr) = arm.finally_block {
        d = d
            .append(Doc::text(" finally "))
            .append(super::expr::format_expr(finally_expr));
    }
    d
}

/// Build the body of a braced block from pre-built Doc items and dangling trivia.
/// The result should be wrapped in `Doc::nest(indent, body)` by the caller.
pub fn format_braced_body(items: &[Doc], dangling_trivia: &[Trivia]) -> Doc {
    let mut body = Doc::Nil;
    for item in items {
        body = body.append(item.clone());
    }
    // Only emit dangling comments, not blank lines (blank lines before `}` are noise)
    let comments: Vec<&Trivia> = dangling_trivia
        .iter()
        .filter(|t| !matches!(t, Trivia::BlankLines(_)))
        .collect();
    if !comments.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(&comments.iter().map(|t| (*t).clone()).collect::<Vec<_>>()));
    }
    body
}

/// Format a braced block body from annotated items. Each item gets a hardline,
/// leading trivia, the formatted node, and trailing comment. Dangling trivia
/// is appended at the end. Returns the body doc (caller wraps in `nest` + `}`).
pub fn format_annotated_body<T>(
    items: &[Annotated<T>],
    format_item: impl Fn(&T) -> Doc,
    dangling_trivia: &[Trivia],
) -> Doc {
    let mut body_items = Vec::new();
    for ann in items {
        body_items.push(Doc::hardline());
        body_items.push(format_trivia(&ann.leading_trivia));
        body_items.push(format_item(&ann.node));
        body_items.push(format_trailing(&ann.trailing_comment));
    }
    format_braced_body(&body_items, dangling_trivia)
}

/// Concatenate a Vec<Doc> into a single Doc.
pub fn docs_from_vec(docs: Vec<Doc>) -> Doc {
    let mut result = Doc::Nil;
    for d in docs {
        result = result.append(d);
    }
    result
}
