use crate::ast::*;
use super::Doc;
use super::helpers::{format_doc_comment, docs_from_vec};
use super::type_expr::*;
use super::expr::format_expr;
use super::decl::*;

/// Format an entire program (list of declarations).
pub fn format_program(decls: &[Decl]) -> Doc {
    let docs: Vec<Doc> = decls
        .iter()
        .filter_map(format_decl)
        .collect();
    Doc::join(Doc::hardline(), docs)
}

/// Format a single declaration. Returns None for elaboration-only nodes.
fn format_decl(decl: &Decl) -> Option<Doc> {
    Some(match decl {
        Decl::ModuleDecl { path, .. } => {
            Doc::text(format!("module {}", path.join(".")))
        }
        Decl::Import { module_path, alias, exposing, .. } => {
            format_import(module_path, alias, exposing)
        }
        Decl::FunSignature { doc, public, name, params, return_type, effects, effect_row_var, where_clause, annotations, .. } => {
            let mut parts = Vec::new();
            for ann in annotations {
                parts.push(format_annotation(ann));
                parts.push(Doc::hardline());
            }
            if !doc.is_empty() {
                parts.push(format_doc_comment(doc));
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
        Decl::DictConstructor { .. } => return None,
    })
}
