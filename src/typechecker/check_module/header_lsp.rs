use crate::typechecker::{Checker, ScopeMap};

impl Checker {
    pub(super) fn merge_header_lsp_scope(&mut self, import_scope: &ScopeMap) {
        for (surface, canonical) in import_scope
            .values
            .iter()
            .chain(import_scope.types.iter())
            .chain(import_scope.handlers.iter())
            .chain(import_scope.effects.iter())
            .chain(import_scope.traits.iter())
        {
            self.copy_imported_doc(surface, canonical);
        }
        for (surface, canonical) in &import_scope.constructors {
            self.copy_imported_doc(surface, canonical);
            if let Some(def_id) = self.lsp.constructor_def_ids.get(canonical).copied() {
                self.lsp
                    .constructor_def_ids
                    .entry(surface.clone())
                    .or_insert(def_id);
            }
        }
    }

    fn copy_imported_doc(&mut self, surface: &str, canonical: &str) {
        if let Some(doc) = self.lsp.imported_docs.get(canonical).cloned() {
            self.lsp
                .imported_docs
                .entry(surface.to_string())
                .or_insert(doc);
        }
    }
}
