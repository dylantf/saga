use crate::ast::*;
use super::Doc;
use super::helpers::{docs_from_vec, format_trivia, format_trailing};
use super::type_expr::*;
use super::expr::format_expr;
use super::decl::*;

/// Format an entire program (list of annotated declarations).
pub fn format_program(decls: &[Annotated<Decl>]) -> Doc {
    let mut result = Doc::Nil;
    let mut first = true;
    for ann in decls {
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
    result
}

/// Format a single declaration.
fn format_decl(decl: &Decl) -> Doc {
    match decl {
        Decl::ModuleDecl { path, .. } => {
            Doc::text(format!("module {}", path.join(".")))
        }
        Decl::Import { module_path, alias, exposing, .. } => {
            format_import(module_path, alias, exposing)
        }
        Decl::FunSignature { public, name, params, return_type, effects, effect_row_var, where_clause, annotations, .. } => {
            let mut parts = Vec::new();
            for ann in annotations {
                parts.push(format_annotation(ann));
                parts.push(Doc::hardline());
            }
            if *public {
                parts.push(Doc::text("pub "));
            }
            parts.push(Doc::text(format!("fun {} : ", name)));
            parts.push(format_fun_type(params, return_type, effects, effect_row_var));
            if !where_clause.is_empty() {
                parts.push(Doc::text(" "));
                parts.push(format_where_clause(where_clause));
            }
            docs_from_vec(parts)
        }
        Decl::FunBinding { name, params, guard, body, .. } => {
            format_fun_binding(name, params, guard, body)
        }
        Decl::Let { name, annotation, value, .. } => {
            let mut d = Doc::text(format!("let {}", name));
            if let Some(ty) = annotation {
                d = d.append(Doc::text(" : ")).append(format_type_expr(ty));
            }
            d = d.append(Doc::text(" = ")).append(format_expr(value));
            d
        }
        Decl::TypeDef { doc, public, opaque, name, type_params, variants, deriving, .. } => {
            format_type_def(doc, *public, *opaque, name, type_params, variants, deriving)
        }
        Decl::RecordDef { doc, public, name, type_params, fields, deriving, .. } => {
            format_record_def(doc, *public, name, type_params, fields, deriving)
        }
        Decl::EffectDef { doc, public, name, type_params, operations, .. } => {
            format_effect_def(doc, *public, name, type_params, operations)
        }
        Decl::TraitDef { doc, public, name, type_param, supertraits, methods, .. } => {
            format_trait_def(doc, *public, name, type_param, supertraits, methods)
        }
        Decl::HandlerDef { doc, public, name, effects, needs, where_clause, arms, return_clause, .. } => {
            format_handler_def(doc, *public, name, effects, needs, where_clause, arms, return_clause)
        }
        Decl::ImplDef { doc, trait_name, target_type, type_params, where_clause, needs, methods, .. } => {
            format_impl_def(doc, trait_name, target_type, type_params, where_clause, needs, methods)
        }
        Decl::DictConstructor { .. } => Doc::Nil,
    }
}
