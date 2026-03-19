use tower_lsp::lsp_types::*;

use dylang::ast::Decl;

use super::line_index::LineIndex;

fn span_to_range(span: &dylang::token::Span, li: &LineIndex) -> Range {
    let (sl, sc) = li.offset_to_line_col(span.start);
    let (el, ec) = li.offset_to_line_col(span.end);
    Range {
        start: Position::new(sl as u32, sc as u32),
        end: Position::new(el as u32, ec as u32),
    }
}

#[allow(deprecated)] // SymbolInformation::deprecated is deprecated but required by the struct
pub fn collect_symbols(program: &[Decl], li: &LineIndex) -> Vec<SymbolInformation> {
    let mut symbols = Vec::new();
    // Track which names already have an annotation so we skip duplicate FunBindings
    let mut annotated: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for decl in program {
        if let Decl::FunAnnotation { name, .. } = decl {
            annotated.insert(name);
        }
    }

    for decl in program {
        match decl {
            Decl::FunAnnotation { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::FUNCTION,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::FunBinding { name, span, .. } if !annotated.contains(name.as_str()) => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::FUNCTION,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::Let { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::VARIABLE,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::TypeDef { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::ENUM,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::RecordDef { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::STRUCT,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::EffectDef { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::INTERFACE,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::HandlerDef { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::FUNCTION,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::TraitDef { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::INTERFACE,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::ImplDef {
                trait_name,
                target_type,
                span,
                ..
            } => {
                symbols.push(SymbolInformation {
                    name: format!("impl {} for {}", trait_name, target_type),
                    kind: SymbolKind::CLASS,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            Decl::ExternalFun { name, span, .. } => {
                symbols.push(SymbolInformation {
                    name: name.clone(),
                    kind: SymbolKind::FUNCTION,
                    location: Location {
                        uri: Url::parse("file:///").unwrap(),
                        range: span_to_range(span, li),
                    },
                    tags: None,
                    deprecated: None,
                    container_name: None,
                });
            }
            _ => {}
        }
    }
    symbols
}
