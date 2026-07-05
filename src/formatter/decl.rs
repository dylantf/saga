use super::expr::format_expr;
use super::helpers::{
    docs_from_vec, format_annotated_body, format_braced_body, format_doc_preamble,
    format_handler_arm, format_lit_raw, format_trailing, format_trivia,
};
use super::pat::format_pat_atom;
use super::type_expr::*;
use super::{Doc, pretty};
use crate::ast::*;
use crate::docs;
use std::fmt::Write;

fn format_derive_spec(spec: &DeriveSpec) -> String {
    if spec.type_args.is_empty() {
        return spec.trait_name.clone();
    }
    let args = spec
        .type_args
        .iter()
        .map(|arg| {
            pretty(1000, &format_type_expr_atom(arg))
                .trim_end()
                .to_string()
        })
        .collect::<Vec<_>>()
        .join(" ");
    format!("{} {}", spec.trait_name, args)
}

fn format_deriving_clause(deriving: &[DeriveSpec]) -> String {
    deriving
        .iter()
        .map(format_derive_spec)
        .collect::<Vec<_>>()
        .join(", ")
}

pub fn format_import(path: &[String], alias: &Option<String>, exposing: &Option<Exposing>) -> Doc {
    let mut d = Doc::text(format!("import {}", path.join(".")));
    if let Some(a) = alias
        && path.last() != Some(a)
    {
        d = d.append(Doc::text(format!(" as {}", a)));
    }
    match exposing {
        None => {}
        Some(Exposing::All { .. }) => {
            let text = match exposing {
                Some(Exposing::All { public: true, .. }) => " (pub ..)",
                _ => " (..)",
            };
            d = d.append(Doc::text(text));
        }
        Some(Exposing::Items(items)) => {
            let item_docs: Vec<Doc> = items
                .iter()
                .map(|i| {
                    let mut text = String::new();
                    if i.public {
                        text.push_str("pub ");
                    }
                    text.push_str(&i.name);
                    if let Some(alias) = &i.alias {
                        text.push_str(" as ");
                        text.push_str(alias);
                    }
                    Doc::text(text)
                })
                .collect();
            let items_joined = Doc::join(docs![Doc::text(","), Doc::line()], item_docs);
            d = Doc::group(docs![
                d,
                Doc::text(" ("),
                Doc::nest(2, docs![Doc::softline(), items_joined]),
                Doc::softline(),
                Doc::text(")")
            ]);
        }
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
        lhs = lhs.append(Doc::text(" ")).append(format_pat_atom(p));
    }
    if let Some(g) = guard {
        lhs = lhs.append(Doc::text(" when ")).append(format_expr(g));
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

/// Is this expression "block-like" - handles its own multi-line layout?
/// These should stay on the `=` line rather than breaking after `=`.
pub(super) fn is_block_like(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Block { .. }
        | ExprKind::Case { .. }
        | ExprKind::Do { .. }
        | ExprKind::Receive { .. }
        | ExprKind::HandlerExpr { .. } => true,
        // Multiline strings handle their own layout with hardlines
        ExprKind::Lit {
            value: Lit::String(_, kind),
            ..
        } => kind.is_multiline(),
        ExprKind::StringInterp { kind, .. } => kind.is_multiline(),
        // Pipes and binop chains stay on the = line - they handle their own
        // multi-line layout like `x |> f |> g` or `"a" <> "b" <> "c"`
        ExprKind::Pipe { .. } => false,
        ExprKind::BinOp { .. } | ExprKind::BinOpChain { .. } => true,
        // Lists and tuples stay on the = line - they handle their own breaking
        ExprKind::ListLit { elements } => !elements.is_empty(),
        ExprKind::Tuple { .. } => true,
        // Named record creates stay on = line
        ExprKind::RecordCreate { .. } | ExprKind::AnonRecordCreate { .. } => true,
        // with expressions are block-like when the inner expr is block-like or handler is inline
        ExprKind::With { expr, handler } => {
            matches!(handler.as_ref(), Handler::Inline { .. }) || is_block_like(expr)
        }
        // App with a trailing lambda whose body is block-like: `f (fun x -> { ... })`
        ExprKind::App { .. } => {
            let (_, args) = crate::formatter::expr::flatten_app(expr);
            args.last().is_some_and(
                |last| matches!(&last.kind, ExprKind::Lambda { body, .. } if is_block_like(body)),
            )
        }
        _ => false,
    }
}

pub fn format_type_def(decl: &Decl) -> Doc {
    let Decl::TypeDef {
        doc,
        public,
        opaque,
        name,
        type_params,
        variants,
        deriving,
        multiline,
        ..
    } = decl
    else {
        unreachable!()
    };

    let mut parts = Vec::new();
    format_doc_preamble(doc, &mut parts);

    let mut header = String::new();
    if *opaque {
        header.push_str("opaque ");
    } else if *public {
        header.push_str("pub ");
    }
    header.push_str("type ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        write!(header, "{}", tp).unwrap();
    }

    parts.push(Doc::text(header));

    let deriving_doc = if !deriving.is_empty() {
        Doc::text(format!(" deriving ({})", format_deriving_clause(deriving)))
    } else {
        Doc::Nil
    };

    // Format each variant body (name + fields + trailing comment, no prefix)
    let format_variant = |ann: &Annotated<TypeConstructor>| -> Doc {
        let variant = &ann.node;
        let mut vdoc = Doc::Nil;
        if !ann.leading_trivia.is_empty() {
            vdoc = vdoc.append(format_trivia(&ann.leading_trivia));
        }
        vdoc = vdoc.append(Doc::text(&variant.name));
        for (label, ty) in &variant.fields {
            vdoc = vdoc.append(Doc::text(" "));
            match label {
                Some(l) => {
                    vdoc = vdoc.append(docs![
                        Doc::text(format!("({}: ", l)),
                        format_type_expr(ty),
                        Doc::text(")")
                    ]);
                }
                None => {
                    vdoc = vdoc.append(format_type_expr_atom(ty));
                }
            }
        }
        vdoc.append(format_trailing(&ann.trailing_comment))
    };

    let deriving_bare = if !deriving.is_empty() {
        Doc::text(format!("deriving ({})", format_deriving_clause(deriving)))
    } else {
        Doc::Nil
    };

    if *multiline {
        // User wrote variants on separate lines - `=` on header, `|` before each
        parts.push(Doc::text(" ="));
        let mut broken_variants = Doc::Nil;
        for ann in variants {
            broken_variants = broken_variants
                .append(Doc::hardline())
                .append(Doc::text("| "))
                .append(format_variant(ann));
        }
        if !deriving.is_empty() {
            broken_variants = broken_variants
                .append(Doc::hardline())
                .append(deriving_bare);
        }
        parts.push(Doc::nest(2, broken_variants));
    } else {
        // Try flat: `type Name = A | B | C deriving (...)`
        // Broken:  `type Name =\n  | A\n  | B\n  | C\n  deriving (...)`
        let mut flat_variants = Doc::text(" = ");
        for (i, ann) in variants.iter().enumerate() {
            if i > 0 {
                flat_variants = flat_variants.append(Doc::text(" | "));
            }
            flat_variants = flat_variants.append(format_variant(ann));
        }
        flat_variants = flat_variants.append(deriving_doc.clone());

        let mut broken_variants = Doc::text(" =");
        for ann in variants {
            broken_variants = broken_variants
                .append(Doc::hardline())
                .append(Doc::text("| "))
                .append(format_variant(ann));
        }
        if !deriving.is_empty() {
            broken_variants = broken_variants
                .append(Doc::hardline())
                .append(deriving_bare);
        }

        parts.push(Doc::group(Doc::if_break(
            Doc::nest(2, broken_variants),
            flat_variants,
        )));
    }

    docs_from_vec(parts)
}

pub fn format_type_alias(decl: &Decl) -> Doc {
    let Decl::TypeAlias {
        doc,
        public,
        name,
        type_params,
        body,
        ..
    } = decl
    else {
        unreachable!()
    };

    let mut parts = Vec::new();
    format_doc_preamble(doc, &mut parts);

    let mut header = String::new();
    if *public {
        header.push_str("pub ");
    }
    header.push_str("type alias ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        write!(header, "{}", tp).unwrap();
    }
    header.push_str(" = ");
    parts.push(Doc::text(header));
    parts.push(format_type_expr(body));
    docs_from_vec(parts)
}

pub fn format_record_def(decl: &Decl) -> Doc {
    let Decl::RecordDef {
        doc,
        public,
        name,
        type_params,
        fields,
        deriving,
        multiline,
        dangling_trivia: dangling,
        ..
    } = decl
    else {
        unreachable!()
    };

    let mut parts = Vec::new();
    format_doc_preamble(doc, &mut parts);

    let mut header = String::new();
    if *public {
        header.push_str("pub ");
    }
    header.push_str("record ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        write!(header, "{}", tp).unwrap();
    }
    parts.push(Doc::text(header));

    let deriving_doc = if !deriving.is_empty() {
        Doc::text(format!(" deriving ({})", format_deriving_clause(deriving)))
    } else {
        Doc::Nil
    };

    let broken_fields = {
        let body = format_annotated_body(
            fields,
            |(fname, ty)| {
                docs![
                    Doc::text(format!("{}: ", fname)),
                    format_type_expr(ty),
                    Doc::text(",")
                ]
            },
            dangling,
        );
        docs![
            Doc::text(" {"),
            Doc::nest(2, body),
            Doc::hardline(),
            Doc::text("}"),
            deriving_doc.clone()
        ]
    };

    if *multiline {
        parts.push(broken_fields);
    } else {
        let field_docs: Vec<Doc> = fields
            .iter()
            .map(|ann| {
                let (fname, ty) = &ann.node;
                let mut d = docs![Doc::text(format!("{}: ", fname)), format_type_expr(ty)];
                d = d.append(format_trailing(&ann.trailing_comment));
                d
            })
            .collect();
        let flat_fields = {
            let joined = Doc::join(Doc::text(", "), field_docs);
            docs![Doc::text(" { "), joined, Doc::text(" }"), deriving_doc]
        };
        parts.push(Doc::group(Doc::if_break(broken_fields, flat_fields)));
    }

    docs_from_vec(parts)
}

pub fn format_effect_def(
    doc: &[String],
    public: bool,
    name: &str,
    type_params: &[TypeParam],
    operations: &[Annotated<EffectOp>],
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    format_doc_preamble(doc, &mut parts);

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("effect ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        write!(header, "{}", tp).unwrap();
    }
    header.push_str(" {");
    parts.push(Doc::text(header));

    let body = format_annotated_body(
        operations,
        |op| {
            let mut sig = docs![
                Doc::text(format!("fun {} : ", op.name)),
                format_fun_type(&op.params, &op.return_type, &op.effects, &op.effect_row_var)
            ];
            if !op.where_clause.is_empty() {
                sig = sig
                    .append(Doc::text(" "))
                    .append(format_where_clause(&op.where_clause));
            }
            sig
        },
        dangling,
    );
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

#[allow(clippy::too_many_arguments)]
pub fn format_trait_def(
    doc: &[String],
    public: bool,
    name: &str,
    type_params: &[TypeParam],
    supertraits: &[TraitRef],
    methods: &[Annotated<TraitMethod>],
    dangling: &[Trivia],
) -> Doc {
    let mut parts = Vec::new();
    format_doc_preamble(doc, &mut parts);

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("trait ");
    header.push_str(name);
    for tp in type_params {
        header.push(' ');
        write!(header, "{}", tp).unwrap();
    }
    parts.push(Doc::text(header));

    let self_param = type_params
        .first()
        .map(|tp| tp.name.as_str())
        .unwrap_or("a");
    if !supertraits.is_empty() {
        let st_names: Vec<&str> = supertraits.iter().map(|tr| tr.name.as_str()).collect();
        parts.push(Doc::text(format!(
            " where {{{}: {}}}",
            self_param,
            st_names.join(" + ")
        )));
    }

    if methods.is_empty() && dangling.is_empty() {
        parts.push(Doc::text(" {}"));
        return docs_from_vec(parts);
    }

    parts.push(Doc::text(" {"));

    let body = format_annotated_body(
        methods,
        |method| {
            let sig = docs![
                Doc::text(format!("fun {} : ", method.name)),
                format_fun_type(
                    &method.params,
                    &method.return_type,
                    &method.effects,
                    &method.effect_row_var,
                )
            ];
            if let Some(default) = &method.default_body {
                docs![
                    sig,
                    Doc::hardline(),
                    format_fun_binding(&method.name, &default.params, &None, &default.body)
                ]
            } else {
                sig
            }
        },
        dangling,
    );
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
    format_doc_preamble(doc, &mut parts);

    let mut header = String::new();
    if public {
        header.push_str("pub ");
    }
    header.push_str("handler ");
    header.push_str(name);
    header.push_str(" for ");
    parts.push(Doc::text(header));
    let eff_docs: Vec<Doc> = effects.iter().map(format_effect_ref).collect();
    parts.push(Doc::join(Doc::text(", "), eff_docs));

    if !needs.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(format_needs(needs, &[]));
    }
    if !where_clause.is_empty() {
        parts.push(Doc::text(" "));
        parts.push(format_where_clause(where_clause));
    }

    parts.push(Doc::text(" {"));

    let mut body_items = Vec::new();
    for ann in arms {
        body_items.push(Doc::hardline());
        body_items.push(format_trivia(&ann.leading_trivia));
        body_items.push(format_handler_arm(&ann.node));
        body_items.push(format_trailing(&ann.trailing_comment));
    }
    if let Some(rc) = return_clause {
        body_items.push(Doc::hardline());
        body_items.push(format_handler_arm(rc));
    }
    let body = format_braced_body(&body_items, dangling);
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}

pub fn format_impl_def(decl: &Decl) -> Doc {
    let Decl::ImplDef {
        doc,
        trait_name,
        trait_type_args,
        target_type,
        target_type_expr,
        type_params,
        where_clause,
        where_apps,
        needs,
        methods,
        dangling_trivia: dangling,
        ..
    } = decl
    else {
        unreachable!()
    };

    let mut parts = Vec::new();
    format_doc_preamble(doc, &mut parts);

    let trait_type_arg_names: Vec<String> = trait_type_args
        .iter()
        .map(|te| {
            pretty(1000, &format_type_expr_atom(te))
                .trim_end()
                .to_string()
        })
        .collect();
    let is_tuple_target = target_type == "Tuple" && type_params.len() >= 2;
    let target_rendered = if let Some(target_type_expr) = target_type_expr {
        let rendered = pretty(1000, &format_type_expr(target_type_expr))
            .trim_end()
            .to_string();
        if impl_target_needs_parens(target_type_expr) {
            format!("({})", rendered)
        } else {
            rendered
        }
    } else if is_tuple_target {
        let params: Vec<String> = type_params.iter().map(|tp| tp.to_string()).collect();
        format!("({})", params.join(", "))
    } else {
        target_type.clone()
    };
    let mut header = if trait_type_args.is_empty() {
        format!("impl {} for {}", trait_name, target_rendered)
    } else {
        format!(
            "impl {} {} for {}",
            trait_name,
            trait_type_arg_names.join(" "),
            target_rendered
        )
    };
    if target_type_expr.is_none() && !is_tuple_target {
        for tp in type_params {
            header.push(' ');
            write!(header, "{}", tp).unwrap();
        }
    }
    parts.push(Doc::text(header));

    let multiline_where = !where_apps.is_empty();
    if multiline_where {
        parts.push(Doc::hardline());
        parts.push(Doc::text("  "));
        parts.push(format_impl_where_clause(where_clause, where_apps));
        if !needs.is_empty() {
            parts.push(Doc::text(" "));
            parts.push(format_needs(needs, &[]));
        }
        parts.push(Doc::hardline());
        parts.push(Doc::text("{"));
    } else {
        if !where_clause.is_empty() {
            parts.push(Doc::text(" "));
            parts.push(format_impl_where_clause(where_clause, where_apps));
        }
        if !needs.is_empty() {
            parts.push(Doc::text(" "));
            parts.push(format_needs(needs, &[]));
        }
        parts.push(Doc::text(" {"));
    }

    if methods.is_empty() && dangling.is_empty() {
        parts.push(Doc::text("}"));
        return docs_from_vec(parts);
    }

    let body = format_annotated_body(
        methods,
        |m| format_fun_binding(&m.name, &m.params, &None, &m.body),
        dangling,
    );
    parts.push(Doc::nest(2, body));
    parts.push(Doc::hardline());
    parts.push(Doc::text("}"));
    docs_from_vec(parts)
}
