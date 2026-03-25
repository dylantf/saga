use crate::ast::*;
use crate::token::Span;
use crate::docs;
use super::Doc;
use super::helpers::{format_doc_comment, format_lit_raw, docs_from_vec};
use super::type_expr::*;
use super::expr::format_expr;
use super::pat::format_pat;

pub fn format_import(path: &[String], alias: &Option<String>, exposing: &Option<Vec<ExposedItem>>) -> Doc {
    let mut d = Doc::text(format!("import {}", path.join(".")));
    if let Some(a) = alias {
        d = d.append(Doc::text(format!(" as {}", a)));
    }
    if let Some(items) = exposing {
        d = d.append(Doc::text(" ("))
            .append(Doc::text(items.join(", ")))
            .append(Doc::text(")"));
    }
    d
}

pub fn format_annotation(ann: &Annotation) -> Doc {
    let mut d = Doc::text(format!("@{}", ann.name));
    if !ann.args.is_empty() {
        let args: Vec<String> = ann.args.iter().map(format_lit_raw).collect();
        d = d.append(Doc::text("("))
            .append(Doc::text(args.join(", ")))
            .append(Doc::text(")"));
    }
    d
}

pub fn format_fun_binding(name: &str, params: &[Pat], guard: &Option<Box<Expr>>, body: &Expr) -> Doc {
    let mut d = Doc::text(name.to_string());
    for p in params {
        d = d.append(Doc::text(" ")).append(format_pat(p));
    }
    if let Some(g) = guard {
        d = d.append(Doc::text(" | ")).append(format_expr(g));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(body));
    d
}

pub fn format_type_def(
    doc: &[String], public: bool, opaque: bool, name: &str,
    type_params: &[String], variants: &[TypeConstructor], deriving: &[String],
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

    for (i, variant) in variants.iter().enumerate() {
        let prefix = if i == 0 { "\n  = " } else { "\n  | " };
        parts.push(Doc::text(prefix));
        parts.push(Doc::text(&variant.name));
        if !variant.fields.is_empty() {
            let fields: Vec<Doc> = variant.fields.iter().map(|(label, ty)| {
                match label {
                    Some(l) => docs![Doc::text(format!("{}: ", l)), format_type_expr(ty)],
                    None => format_type_expr(ty),
                }
            }).collect();
            parts.push(Doc::text("("));
            parts.push(Doc::join(Doc::text(", "), fields));
            parts.push(Doc::text(")"));
        }
    }

    if !deriving.is_empty() {
        parts.push(Doc::text(format!(" deriving ({})", deriving.join(", "))));
    }

    docs_from_vec(parts)
}

pub fn format_record_def(
    doc: &[String], public: bool, name: &str,
    type_params: &[String], fields: &[(String, TypeExpr)], deriving: &[String],
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

    let field_docs: Vec<Doc> = fields.iter().map(|(fname, ty)| {
        docs![Doc::text(format!("  {} : ", fname)), format_type_expr(ty), Doc::text(",")]
    }).collect();

    parts.push(Doc::nest(0, Doc::join(Doc::hardline(), field_docs)));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));

    if !deriving.is_empty() {
        parts.push(Doc::text(format!(" deriving ({})", deriving.join(", "))));
    }

    docs_from_vec(parts)
}

pub fn format_effect_def(
    doc: &[String], public: bool, name: &str,
    type_params: &[String], operations: &[EffectOp],
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

    for op in operations {
        parts.push(Doc::hardline());
        if !op.doc.is_empty() {
            parts.push(format_doc_comment(&op.doc));
            parts.push(Doc::hardline());
        }
        parts.push(Doc::text(format!("  fun {} : ", op.name)));
        parts.push(format_fun_type(&op.params, &op.return_type, &[], &None));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

pub fn format_trait_def(
    doc: &[String], public: bool, name: &str, type_param: &str,
    supertraits: &[(String, Span)], methods: &[TraitMethod],
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
        let st_names: Vec<&str> = supertraits.iter().map(|(n, _): &(String, Span)| n.as_str()).collect();
        parts.push(Doc::text(format!(" where {{{}: {}}}", type_param, st_names.join(" + "))));
    }

    parts.push(Doc::text(" {"));

    for method in methods {
        parts.push(Doc::hardline());
        if !method.doc.is_empty() {
            parts.push(format_doc_comment(&method.doc));
            parts.push(Doc::hardline());
        }
        parts.push(Doc::text(format!("  fun {} : ", method.name)));
        parts.push(format_fun_type(&method.params, &method.return_type, &[], &None));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

#[allow(clippy::too_many_arguments)]
pub fn format_handler_def(
    doc: &[String], public: bool, name: &str,
    effects: &[EffectRef], needs: &[EffectRef], where_clause: &[TraitBound],
    arms: &[HandlerArm], return_clause: &Option<Box<HandlerArm>>,
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

    for arm in arms {
        parts.push(Doc::hardline());
        parts.push(format_handler_arm(arm));
    }
    if let Some(rc) = return_clause {
        parts.push(Doc::hardline());
        parts.push(format_handler_arm(rc));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

fn format_handler_arm(arm: &HandlerArm) -> Doc {
    let mut d = Doc::text(format!("  {}", arm.op_name));
    for (param, _) in &arm.params {
        d = d.append(Doc::text(format!(" {}", param)));
    }
    d = d.append(Doc::text(" = ")).append(format_expr(&arm.body));
    d
}

pub fn format_impl_def(
    doc: &[String], trait_name: &str, target_type: &str,
    type_params: &[String], where_clause: &[TraitBound], needs: &[EffectRef],
    methods: &[(String, Span, Vec<Pat>, Expr)],
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

    for (method_name, _, params, body) in methods {
        parts.push(Doc::hardline());
        parts.push(format_fun_binding(method_name, params, &None, body));
    }

    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}
