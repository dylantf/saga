use super::Doc;
use super::decl::*;
use super::helpers::{format_trailing, format_trivia};
use super::type_expr::*;
use crate::ast::*;
use crate::docs;

/// Which section of the file a declaration belongs to.
#[derive(PartialEq)]
enum DeclSection {
    ModuleDecl,
    Import,
    Code,
}

fn decl_section(decl: &Decl) -> DeclSection {
    match decl {
        Decl::ModuleDecl { .. } => DeclSection::ModuleDecl,
        Decl::Import { .. } => DeclSection::Import,
        _ => DeclSection::Code,
    }
}

/// Whether trivia already contains a blank line.
fn has_blank_line(trivia: &[Trivia]) -> bool {
    trivia.iter().any(|t| matches!(t, Trivia::BlankLines(_)))
}

/// Format an entire program (list of annotated declarations).
pub fn format_program(program: &AnnotatedProgram) -> Doc {
    let decls = sort_imports(&program.declarations);
    let mut result = Doc::Nil;
    let mut first = true;
    let mut prev_section: Option<DeclSection> = None;
    for ann in &decls {
        if matches!(ann.node, Decl::DictConstructor { .. }) {
            continue;
        }

        let section = decl_section(&ann.node);

        if first {
            // First declaration: emit leading trivia without separator
            result = result.append(format_trivia(&ann.leading_trivia));
        } else {
            // Newline to end previous declaration
            result = result.append(Doc::hardline());

            // Ensure a blank line between sections (module decl -> imports -> code)
            // even if the source didn't have one.
            let section_changed = prev_section.as_ref() != Some(&section);
            if section_changed && !has_blank_line(&ann.leading_trivia) {
                result = result.append(Doc::hardline());
            }

            // Leading trivia (blank lines, comments) between declarations
            result = result.append(format_trivia(&ann.leading_trivia));
        }
        first = false;
        prev_section = Some(section);

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

/// Sort imports: Std.* first (sorted), then everything else (sorted).
/// Non-import declarations keep their original order.
fn sort_imports(decls: &[Annotated<Decl>]) -> Vec<Annotated<Decl>> {
    // Find the range of contiguous imports (they must stay grouped together)
    let mut result = decls.to_vec();

    // Collect indices of all import declarations
    let import_indices: Vec<usize> = result
        .iter()
        .enumerate()
        .filter(|(_, ann)| matches!(ann.node, Decl::Import { .. }))
        .map(|(i, _)| i)
        .collect();

    if import_indices.len() <= 1 {
        return result;
    }

    // Extract imports, sort them, put them back
    let mut imports: Vec<Annotated<Decl>> =
        import_indices.iter().map(|&i| result[i].clone()).collect();

    imports.sort_by(|a, b| {
        let path_a = import_path(&a.node);
        let path_b = import_path(&b.node);
        let a_is_std = path_a.first() == Some(&"Std".to_string());
        let b_is_std = path_b.first() == Some(&"Std".to_string());
        match (a_is_std, b_is_std) {
            (true, false) => std::cmp::Ordering::Less,
            (false, true) => std::cmp::Ordering::Greater,
            _ => path_a.cmp(path_b),
        }
    });

    // Put sorted imports back at their original positions
    for (slot, import) in import_indices.iter().zip(imports) {
        result[*slot] = import;
    }

    result
}

fn import_path(decl: &Decl) -> &[String] {
    match decl {
        Decl::Import { module_path, .. } => module_path,
        _ => &[],
    }
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
            let mut preamble = Doc::Nil;
            for ann in annotations {
                preamble = preamble
                    .append(format_annotation(ann))
                    .append(Doc::hardline());
            }

            let mut sig_head = Doc::Nil;
            if *public {
                sig_head = sig_head.append(Doc::text("pub "));
            }
            sig_head = docs![
                sig_head,
                Doc::text(format!("fun {} : ", name)),
                format_arrow_chain(params, return_type)
            ];
            let needs = format_needs(effects, effect_row_var);
            let where_doc = if where_clause.is_empty() {
                Doc::Nil
            } else {
                format_where_clause(where_clause)
            };

            // Break from the end: needs/where break to indented lines when too long.
            // Annotations (with hardlines) stay outside the group so they don't
            // force the signature itself to break.
            let has_needs = !effects.is_empty() || effect_row_var.is_some();
            let has_where = !where_clause.is_empty();
            let sig = if !has_needs && !has_where {
                sig_head
            } else {
                let mut trailing = Doc::Nil;
                if has_needs {
                    trailing = trailing.append(Doc::line()).append(needs);
                }
                if has_where {
                    trailing = trailing.append(Doc::line()).append(where_doc);
                }
                Doc::group(docs![sig_head, Doc::nest(2, trailing)])
            };
            docs![preamble, sig]
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
                lhs = lhs.append(Doc::text(": ")).append(format_type_expr(ty));
            }
            format_binding(lhs, value)
        }
        Decl::Val {
            public,
            name,
            annotations,
            value,
            ..
        } => {
            let mut preamble = Doc::Nil;
            for ann in annotations {
                preamble = preamble
                    .append(format_annotation(ann))
                    .append(Doc::hardline());
            }
            let mut lhs = Doc::Nil;
            if *public {
                lhs = lhs.append(Doc::text("pub "));
            }
            lhs = lhs.append(Doc::text(format!("val {}", name)));
            docs![preamble, format_binding(lhs, value)]
        }
        Decl::TypeDef { .. } => format_type_def(decl),
        Decl::RecordDef { .. } => format_record_def(decl),
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
            type_params,
            supertraits,
            methods,
            dangling_trivia,
            ..
        } => format_trait_def(
            doc,
            *public,
            name,
            type_params,
            supertraits,
            methods,
            dangling_trivia,
        ),
        Decl::HandlerDef {
            doc,
            public,
            name,
            body,
            dangling_trivia,
            ..
        } => format_handler_def(
            doc,
            *public,
            name,
            &body.effects,
            &body.needs,
            &body.where_clause,
            &body.arms,
            &body.return_clause,
            dangling_trivia,
        ),
        Decl::ImplDef { .. } => format_impl_def(decl),
        Decl::DictConstructor { .. } => Doc::Nil,
    }
}
