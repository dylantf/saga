use std::collections::HashMap;
use tower_lsp::lsp_types::{Position, Range, Url};

use dylang::ast::{Decl, NodeId};
use dylang::token::Span;
use dylang::typechecker::CheckResult;

use crate::line_index::LineIndex;

fn span_to_range(line_index: &LineIndex, source: &str, span: &Span) -> Range {
    let (start_line, start_col) = line_index.offset_to_line_col(span.start, source);
    let (end_line, end_col) = line_index.offset_to_line_col(span.end, source);
    Range {
        start: Position::new(start_line as u32, start_col as u32),
        end: Position::new(end_line as u32, end_col as u32),
    }
}

/// Stable cross-module identity for a symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolKey {
    pub module: String,
    pub name: String,
}

/// A reference location in a specific file.
#[derive(Debug, Clone)]
pub struct SymbolRef {
    pub uri: Url,
    pub range: Range,
}

/// Project-wide symbol reference index, updated per-file on each check.
///
/// When a file is re-checked, its entry is replaced entirely. Queries
/// iterate all files and collect entries matching a SymbolKey.
#[derive(Default)]
pub struct SymbolIndex {
    /// All known references, grouped by the file that contains them.
    by_file: HashMap<Url, Vec<(SymbolKey, Range)>>,
}

impl SymbolIndex {
    /// Find all references to a symbol across the project.
    pub fn query(&self, key: &SymbolKey) -> Vec<SymbolRef> {
        let mut results = Vec::new();
        for (uri, entries) in &self.by_file {
            for (k, range) in entries {
                if k == key {
                    results.push(SymbolRef {
                        uri: uri.clone(),
                        range: *range,
                    });
                }
            }
        }
        results
    }

    /// Replace all reference entries for a file with fresh data from a check result.
    pub fn update_file(
        &mut self,
        uri: &Url,
        tc_result: &CheckResult,
        program: &[Decl],
        line_index: &LineIndex,
        source: &str,
    ) {
        // Determine the current file's module name (for locally-defined symbols).
        // For single-file scripts without a module declaration, use the file URI
        // to avoid collisions between unrelated scripts sharing the same name.
        let local_module: Option<String> = Some(
            program
                .iter()
                .find_map(|decl| {
                    if let Decl::ModuleDecl { path, .. } = decl {
                        Some(path.join("."))
                    } else {
                        None
                    }
                })
                .unwrap_or_else(|| uri.to_string()),
        );

        // Build reverse map: def_id -> (module, name) so we can resolve each reference.
        let mut def_id_to_symbol: HashMap<NodeId, SymbolKey> = HashMap::new();

        // Imported names: use scope_map origins
        for (name, did) in tc_result.env.all_def_ids() {
            if let Some(module) = tc_result.scope_map.origin_of(&name) {
                def_id_to_symbol.insert(
                    did,
                    SymbolKey {
                        module: module.to_string(),
                        name,
                    },
                );
            }
        }

        // Locally-defined names: anything with a def_id that isn't from an import
        if let Some(ref local_mod) = local_module {
            for (name, did) in tc_result.env.all_def_ids() {
                if !def_id_to_symbol.contains_key(&did) && !tc_result.scope_map.is_import(&name) {
                    def_id_to_symbol.insert(
                        did,
                        SymbolKey {
                            module: local_mod.clone(),
                            name,
                        },
                    );
                }
            }
        }

        // Constructor def_ids (not in env, stored separately)
        if let Some(ref local_mod) = local_module {
            for (name, &did) in &tc_result.constructor_def_ids {
                def_id_to_symbol.entry(did).or_insert_with(|| {
                    let module = tc_result
                        .scope_map
                        .origin_of(name)
                        .unwrap_or(local_mod.as_str())
                        .to_string();
                    SymbolKey {
                        module,
                        name: name.clone(),
                    }
                });
            }
        }

        // Scan all references and resolve each to a SymbolKey + location.
        let mut entries = Vec::new();
        for (usage_id, def_id) in &tc_result.references {
            if let Some(key) = def_id_to_symbol.get(def_id)
                && let Some(span) = tc_result.node_spans.get(usage_id)
            {
                entries.push((key.clone(), span_to_range(line_index, source, span)));
            }
        }

        // Type/effect name references (from annotations, handler `for` clauses, etc.)
        for (span, type_name) in &tc_result.type_references {
            // Determine the module: check scope_map origins first, then local
            let module = tc_result
                .scope_map
                .origin_of(type_name)
                .map(|s| s.to_string())
                .unwrap_or_else(|| local_module.clone().unwrap_or_else(|| uri.to_string()));
            let key = SymbolKey {
                module,
                name: type_name.clone(),
            };
            entries.push((key, span_to_range(line_index, source, span)));
        }

        self.by_file.insert(uri.clone(), entries);
    }

    /// Remove all entries for a file (e.g. on close/delete).
    #[allow(dead_code)]
    pub fn remove_file(&mut self, uri: &Url) {
        self.by_file.remove(uri);
    }

    /// Check whether a file has been indexed.
    pub fn has_file(&self, uri: &Url) -> bool {
        self.by_file.contains_key(uri)
    }
}
