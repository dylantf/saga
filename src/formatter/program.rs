use super::Doc;
use super::decl::*;
use super::expr::format_expr;
use super::helpers::{docs_from_vec, format_trailing, format_trivia};
use super::type_expr::*;
use crate::ast::*;

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

        // Trailing comment
        result = result.append(format_trailing(&ann.trailing_comment));
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
            let mut parts = Vec::new();
            for ann in annotations {
                parts.push(format_annotation(ann));
                parts.push(Doc::hardline());
            }
            if *public {
                parts.push(Doc::text("pub "));
            }
            parts.push(Doc::text(format!("fun {} : ", name)));
            parts.push(format_fun_type(
                params,
                return_type,
                effects,
                effect_row_var,
            ));
            if !where_clause.is_empty() {
                parts.push(Doc::text(" "));
                parts.push(format_where_clause(where_clause));
            }
            docs_from_vec(parts)
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
            let mut d = Doc::text(format!("let {}", name));
            if let Some(ty) = annotation {
                d = d.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            d = d.append(Doc::text(" = ")).append(format_expr(value));
            d
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
