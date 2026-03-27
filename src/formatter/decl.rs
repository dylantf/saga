use super::Doc;
use super::expr::format_expr;
use super::helpers::{
    docs_from_vec, format_doc_comment, format_lit_raw, format_trailing, format_trivia,
    format_trivia_dangling,
};
use super::pat::format_pat;
use super::type_expr::*;
use crate::ast::*;
use crate::docs;
use crate::token::Span;

pub fn format_import(
    path: &[String],
    alias: &Option<String>,
    exposing: &Option<Vec<ExposedItem>>,
) -> Doc {
    let mut d = Doc::text(format!("import {}", path.join(".")));
    if let Some(a) = alias {
        d = d.append(Doc::text(format!(" as {}", a)));
    }
    if let Some(items) = exposing {
        let item_docs: Vec<Doc> = items.iter().map(|i| Doc::text(i.as_str())).collect();
        let items_joined = Doc::join(docs![Doc::text(","), Doc::line()], item_docs);
        d = Doc::group(docs![
            d,
            Doc::text(" ("),
            Doc::nest(2, docs![Doc::softline(), items_joined]),
            Doc::softline(),
            Doc::text(")")
        ]);
    }
    d
}

pub fn format_annotation(ann: &Annotation) -> Doc {
    let mut d = Doc::text(format!("@{}", ann.name));
    if !ann.args.is_empty() {
        let args: Vec<String> = ann.args.iter().map(format_lit_raw).collect();
        d = d
            .append(Doc::text("("))
            .append(Doc::text(args.join(", ")))
            .append(Doc::text(")"));
    }
    d
}

pub fn format_fun_binding(
    name: &str,
    params: &[Pat],
    guard: &Option<Box<Expr>>,
    body: &Expr,
) -> Doc {
    let mut lhs = Doc::text(name.to_string());
    for p in params {
        lhs = lhs.append(Doc::text(" ")).append(format_pat(p));
    }
    if let Some(g) = guard {
        lhs = lhs.append(Doc::text(" | ")).append(format_expr(g));
    }
    format_binding(lhs, body)
}

/// Format `lhs = body` with smart line-breaking.
/// Block-like bodies (blocks, case, etc.) stay on the `=` line since they
/// handle their own multi-line layout. Other bodies break after `=` when
/// the whole thing doesn't fit on one line.
pub fn format_binding(lhs: Doc, body: &Expr) -> Doc {
    let body_doc = format_expr(body);
    if is_block_like(body) {
        // { and case stay on the = line; the body handles its own breaking
        docs![lhs, Doc::text(" = "), body_doc]
    } else {
        // Try one line; break after = if too long
        Doc::group(docs![
            lhs,
            Doc::text(" ="),
            Doc::nest(2, docs![Doc::line(), body_doc])
        ])
    }
}

/// Is this expression "block-like" — handles its own multi-line layout?
/// These should stay on the `=` line rather than breaking after `=`.
pub(super) fn is_block_like(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Block { .. }
        | ExprKind::Case { .. }
        | ExprKind::Do { .. }
        | ExprKind::Receive { .. } => true,
        // Multiline strings handle their own layout with hardlines
        ExprKind::Lit {
            value: Lit::String(_, kind),
            ..
        } => kind.is_multiline(),
        ExprKind::StringInterp { kind, .. } => kind.is_multiline(),
        // Pipes are not block-like — they break after = like other expressions
        ExprKind::Pipe { .. } => false,
        // with expressions where the handler is inline are block-like
        ExprKind::With { handler, .. } => matches!(handler.as_ref(), Handler::Inline { .. }),
        _ => false,
    }
}

pub fn format_type_def(
    doc: &[String],
    public: bool,
    opaque: bool,
    name: &str,
    type_params: &[String],
    variants: &[Annotated<TypeConstructor>],
    deriving: &[String],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if opaque {
        header.push_str("opaque ");
    } else if public {
        header.push_str("pub ");
    }
    header.push_str("type ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }

    parts.push(Doc::text(header));

    // Variants use nest(2) so = / | prefixes are indented
    let mut variant_body = Doc::Nil;
    for (i, ann) in variants.iter().enumerate() {
        let variant = &ann.node;
        if !ann.leading_trivia.is_empty() {
            variant_body = variant_body.append(Doc::hardline());
            variant_body = variant_body.append(format_trivia(&ann.leading_trivia));
        }
        let prefix = if i == 0 { "= " } else { "| " };
        variant_body = variant_body.append(Doc::hardline());
        variant_body = variant_body.append(Doc::text(prefix));
        variant_body = variant_body.append(Doc::text(&variant.name));
        if !variant.fields.is_empty() {
            let fields: Vec<Doc> = variant
                .fields
                .iter()
                .map(|(label, ty)| match label {
                    Some(l) => docs![Doc::text(format!("{}: ", l)), format_type_expr(ty)],
                    None => format_type_expr(ty),
                })
                .collect();
            variant_body = variant_body.append(Doc::text("("));
            variant_body = variant_body.append(Doc::join(Doc::text(", "), fields));
            variant_body = variant_body.append(Doc::text(")"));
        }
        variant_body = variant_body.append(format_trailing(&ann.trailing_comment));
    }
    parts.push(Doc::nest(2, variant_body));

    if !deriving.is_empty() {
        parts.push(Doc::text(format!(" deriving ({})", deriving.join(", "))));
    }

    docs_from_vec(parts)
}

pub fn format_record_def(
    doc: &[String],
    public: bool,
    name: &str,
    type_params: &[String],
    fields: &[Annotated<(String, TypeExpr)>],
    deriving: &[String],
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("record ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }
    header.push_str(" {");
    parts.push(Doc::text(header));

    let mut body = Doc::Nil;
    for ann in fields {
        let (fname, ty) = &ann.node;
        body = body.append(Doc::hardline());
        body = body.append(format_trivia(&ann.leading_trivia));
        body = body.append(docs![
            Doc::text(format!("{} : ", fname)),
            format_type_expr(ty),
            Doc::text(",")
        ]);
        body = body.append(format_trailing(&ann.trailing_comment));
    }
    if !dangling.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling));
    }
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));

    if !deriving.is_empty() {
        parts.push(Doc::text(format!(" deriving ({})", deriving.join(", "))));
    }

    docs_from_vec(parts)
}

pub fn format_effect_def(
    doc: &[String],
    public: bool,
    name: &str,
    type_params: &[String],
    operations: &[Annotated<EffectOp>],
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("effect ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }
    header.push_str(" {");
    parts.push(Doc::text(header));

    let mut body = Doc::Nil;
    for ann in operations {
        let op = &ann.node;
        body = body.append(Doc::hardline());
        body = body.append(format_trivia(&ann.leading_trivia));
        body = body.append(Doc::text(format!("fun {} : ", op.name)));
        body = body.append(format_fun_type(&op.params, &op.return_type, &[], &None));
        body = body.append(format_trailing(&ann.trailing_comment));
    }
    if !dangling.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling));
    }
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

pub fn format_trait_def(
    doc: &[String],
    public: bool,
    name: &str,
    type_param: &str,
    supertraits: &[(String, Span)],
    methods: &[Annotated<TraitMethod>],
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("trait ");
    header.push_str(name);
    header.push(' ');
    header.push_str(type_param);
    parts.push(Doc::text(header));

    if !supertraits.is_empty() {
        let st_names: Vec<&str> = supertraits
            .iter()
            .map(|(n, _): &(String, Span)| n.as_str())
            .collect();
        parts.push(Doc::text(format!(
            " where {{{}: {}}}",
            type_param,
            st_names.join(" + ")
        )));
    }

    parts.push(Doc::text(" {"));

    let mut body = Doc::Nil;
    for ann in methods {
        let method = &ann.node;
        body = body.append(Doc::hardline());
        body = body.append(format_trivia(&ann.leading_trivia));
        body = body.append(Doc::text(format!("fun {} : ", method.name)));
        body = body.append(format_fun_type(
            &method.params,
            &method.return_type,
            &[],
            &None,
        ));
        body = body.append(format_trailing(&ann.trailing_comment));
    }
    if !dangling.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling));
    }
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

#[allow(clippy::too_many_arguments)]
pub fn format_handler_def(
    doc: &[String],
    public: bool,
    name: &str,
    effects: &[EffectRef],
    needs: &[EffectRef],
    where_clause: &[TraitBound],
    arms: &[Annotated<HandlerArm>],
    return_clause: &Option<Box<HandlerArm>>,
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("handler ");
    header.push_str(name);
    header.push_str(" for ");
    let eff_strs: Vec<String> = effects.iter().map(format_effect_ref_str).collect();
    header.push_str(&eff_strs.join(", "));
    parts.push(Doc::text(header));

    if !needs.is_empty() {
        let need_strs: Vec<String> = needs.iter().map(format_effect_ref_str).collect();
        parts.push(Doc::text(format!(" needs {{{}}}", need_strs.join(", "))));
    }
    if !where_clause.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(format_where_clause(where_clause));
    }

    parts.push(Doc::text(" {"));

    let mut body = Doc::Nil;
    for ann in arms {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia(&ann.leading_trivia));
        body = body.append(format_handler_arm(&ann.node));
        body = body.append(format_trailing(&ann.trailing_comment));
    }
    if let Some(rc) = return_clause {
        body = body.append(Doc::hardline());
        body = body.append(format_handler_arm(rc));
    }
    if !dangling.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling));
    }
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

fn format_handler_arm(arm: &HandlerArm) -> Doc {
    let mut d = Doc::text(&arm.op_name);
    for (param, _) in &arm.params {
        d = d.append(Doc::text(format!(" {}", param)));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(&arm.body));
    d
}

pub fn format_impl_def(
    doc: &[String],
    trait_name: &str,
    target_type: &str,
    type_params: &[String],
    where_clause: &[TraitBound],
    needs: &[EffectRef],
    methods: &[Annotated<ImplMethod>],
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    if !doc.is_empty() {
        parts.push(format_doc_comment(doc));
        parts.push(Doc::hardline());
    }

    let mut header = format!("impl {} for {}", trait_name, target_type);
    for tp in type_params {
        header.push(' ');
        header.push_str(tp);
    }
    parts.push(Doc::text(header));

    if !needs.is_empty() {
        let need_strs: Vec<String> = needs.iter().map(format_effect_ref_str).collect();
        parts.push(Doc::text(format!(" needs {{{}}}", need_strs.join(", "))));
    }
    if !where_clause.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(format_where_clause(where_clause));
    }

    parts.push(Doc::text(" {"));

    let mut body = Doc::Nil;
    for ann in methods {
        let ImplMethod {
            name: method_name,
            params,
            body: method_body,
            ..
        } = &ann.node;
        body = body.append(Doc::hardline());
        body = body.append(format_trivia(&ann.leading_trivia));
        body = body.append(format_fun_binding(method_name, params, &None, method_body));
        body = body.append(format_trailing(&ann.trailing_comment));
    }
    if !dangling.is_empty() {
        body = body.append(Doc::hardline());
        body = body.append(format_trivia_dangling(dangling));
    }
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}
