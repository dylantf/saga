use super::Doc;
use super::decl::*;
use super::helpers::{format_trailing, format_trivia};
use super::type_expr::*;
use crate::ast::*;
use crate::docs;

/// Format an entire program (list of annotated declarations).
pub fn format_program(program: &AnnotatedProgram) -> Doc {
    let mut result = Doc::Nil;
    let mut first = true;
    for ann in &program.declarations {
        if matches!(ann.node, Decl::DictConstructor { .. }) {
            continue;
        }

        if first {
            // First declaration: emit leading trivia without separator
            result = result.append(format_trivia(&ann.leading_trivia));
        } else {
            // Newline to end previous declaration
            result = result.append(Doc::hardline());
            // Leading trivia (blank lines, comments) between declarations
            result = result.append(format_trivia(&ann.leading_trivia));
        }
        first = false;

        // The declaration itself
        result = result.append(format_decl(&ann.node));

        // Trailing comment (same line)
        result = result.append(format_trailing(&ann.trailing_comment));

        // Trailing trivia (own-line comments following this decl, before a blank line)
        if !ann.trailing_trivia.is_empty() {
            result = result.append(Doc::hardline());
            result = result.append(format_trivia(&ann.trailing_trivia));
        }
    }

    // Trailing trivia at end of file
    if !program.trailing_trivia.is_empty() {
        if !first {
            result = result.append(Doc::hardline());
        }
        result = result.append(format_trivia(&program.trailing_trivia));
    }

    result
}

/// Format a single declaration.
fn format_decl(decl: &Decl) -> Doc {
    match decl {
        Decl::ModuleDecl { path, .. } => Doc::text(format!("module {}", path.join("."))),
        Decl::Import {
            module_path,
            alias,
            exposing,
            ..
        } => format_import(module_path, alias, exposing),
        Decl::FunSignature {
            public,
            name,
            params,
            return_type,
            effects,
            effect_row_var,
            where_clause,
            annotations,
            ..
        } => {
            let mut prefix = Doc::Nil;
            for ann in annotations {
                prefix = prefix.append(format_annotation(ann)).append(Doc::hardline());
            }
            if *public {
                prefix = prefix.append(Doc::text("pub "));
            }

            let head = docs![
                prefix,
                Doc::text(format!("fun {} : ", name)),
                format_arrow_chain(params, return_type)
            ];
            let needs = format_needs(effects, effect_row_var);
            let where_doc = if where_clause.is_empty() {
                Doc::Nil
            } else {
                format_where_clause(where_clause)
            };

            // Break from the end: needs/where break to indented lines when too long
            let has_needs = !effects.is_empty() || effect_row_var.is_some();
            let has_where = !where_clause.is_empty();
            if !has_needs && !has_where {
                head
            } else {
                let mut trailing = Doc::Nil;
                if has_needs {
                    trailing = trailing.append(Doc::line()).append(needs);
                }
                if has_where {
                    trailing = trailing.append(Doc::line()).append(where_doc);
                }
                Doc::group(docs![head, Doc::nest(2, trailing)])
            }
        }
        Decl::FunBinding {
            name,
            params,
            guard,
            body,
            ..
        } => format_fun_binding(name, params, guard, body),
        Decl::Let {
            name,
            annotation,
            value,
            ..
        } => {
            let mut lhs = Doc::text(format!("let {}", name));
            if let Some(ty) = annotation {
                lhs = lhs.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            format_binding(lhs, value)
        }
        Decl::TypeDef {
            doc,
            public,
            opaque,
            name,
            type_params,
            variants,
            deriving,
            ..
        } => format_type_def(doc, *public, *opaque, name, type_params, variants, deriving),
        Decl::RecordDef {
            doc,
            public,
            name,
            type_params,
            fields,
            deriving,
            dangling_trivia,
            ..
        } => format_record_def(
            doc,
            *public,
            name,
            type_params,
            fields,
            deriving,
            dangling_trivia,
        ),
        Decl::EffectDef {
            doc,
            public,
            name,
            type_params,
            operations,
            dangling_trivia,
            ..
        } => format_effect_def(doc, *public, name, type_params, operations, dangling_trivia),
        Decl::TraitDef {
            doc,
            public,
            name,
            type_param,
            supertraits,
            methods,
            dangling_trivia,
            ..
        } => format_trait_def(
            doc,
            *public,
            name,
            type_param,
            supertraits,
            methods,
            dangling_trivia,
        ),
        Decl::HandlerDef {
            doc,
            public,
            name,
            effects,
            needs,
            where_clause,
            arms,
            return_clause,
            dangling_trivia,
            ..
        } => format_handler_def(
            doc,
            *public,
            name,
            effects,
            needs,
            where_clause,
            arms,
            return_clause,
            dangling_trivia,
        ),
        Decl::ImplDef {
            doc,
            trait_name,
            target_type,
            type_params,
            where_clause,
            needs,
            methods,
            dangling_trivia,
            ..
        } => format_impl_def(
            doc,
            trait_name,
            target_type,
            type_params,
            where_clause,
            needs,
            methods,
            dangling_trivia,
        ),
        Decl::DictConstructor { .. } => Doc::Nil,
    }
}
