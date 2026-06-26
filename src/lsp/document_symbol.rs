use saga::ast;
use tower_lsp::lsp_types::{Location, SymbolInformation, SymbolKind, Url};

use super::text::{LineIndex, span_to_range};

#[allow(deprecated)]
pub(super) fn collect_document_symbols(
    uri: &Url,
    program: &[ast::Decl],
    line_index: &LineIndex,
    source: &str,
) -> Vec<SymbolInformation> {
    let mut symbols = Vec::new();
    let mut annotated = std::collections::HashSet::new();

    for decl in program {
        if let ast::Decl::FunSignature { name, .. } = decl {
            annotated.insert(name.as_str());
        }
    }

    for decl in program {
        let symbol = match decl {
            ast::Decl::ModuleDecl { path, span, .. } => Some((
                path.join("."),
                SymbolKind::MODULE,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::FunSignature { name, span, .. } => Some((
                name.clone(),
                SymbolKind::FUNCTION,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::FunBinding { name, span, .. } if !annotated.contains(name.as_str()) => {
                Some((
                    name.clone(),
                    SymbolKind::FUNCTION,
                    span_to_range(span, line_index, source),
                ))
            }
            ast::Decl::Let { name, span, .. } => Some((
                name.clone(),
                SymbolKind::VARIABLE,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::TypeDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::ENUM,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::TypeAlias { name, span, .. } => Some((
                name.clone(),
                SymbolKind::TYPE_PARAMETER,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::RecordDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::STRUCT,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::EffectDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::INTERFACE,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::HandlerDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::FUNCTION,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::TraitDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::INTERFACE,
                span_to_range(span, line_index, source),
            )),
            ast::Decl::ImplDef {
                trait_name,
                target_type,
                span,
                ..
            } => Some((
                format!("impl {} for {}", trait_name, target_type),
                SymbolKind::CLASS,
                span_to_range(span, line_index, source),
            )),
            _ => None,
        };

        if let Some((name, kind, range)) = symbol {
            symbols.push(SymbolInformation {
                name,
                kind,
                location: Location {
                    uri: uri.clone(),
                    range,
                },
                tags: None,
                deprecated: None,
                container_name: None,
            });
        }
    }

    symbols
}
