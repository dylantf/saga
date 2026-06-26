use std::collections::{HashMap, HashSet};

use saga::ast;
use tower_lsp::lsp_types::*;

use super::text::{range_contains_position, range_width, sort_and_dedup_locations};

pub(super) fn member_symbol_name(owner: &str, member: &str) -> String {
    format!("{owner}.{member}")
}

#[derive(Clone, Default)]
pub(super) struct SemanticIndex {
    pub(super) definition_locations: HashMap<ast::NodeId, Location>,
    pub(super) references: HashMap<ast::NodeId, ast::NodeId>,
    pub(super) references_by_definition: HashMap<ast::NodeId, Vec<SemanticOccurrence>>,
    pub(super) type_definition_locations: HashMap<String, Location>,
    pub(super) type_occurrences_by_name: HashMap<String, Vec<SemanticOccurrence>>,
    pub(super) type_occurrences: Vec<NamedLocation>,
    pub(super) module_definition_locations: HashMap<String, Location>,
    pub(super) module_occurrences_by_name: HashMap<String, Vec<SemanticOccurrence>>,
    pub(super) module_occurrences: Vec<NamedLocation>,
    pub(super) symbol_definition_locations: HashMap<SemanticSymbolKey, Location>,
    pub(super) symbol_occurrences_by_key: HashMap<SemanticSymbolKey, Vec<SemanticOccurrence>>,
    pub(super) symbol_occurrences: Vec<SemanticSymbolLocation>,
    pub(super) docs_by_key: HashMap<SemanticDocKey, Vec<String>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum SemanticSymbolKind {
    Module,
    Trait,
    TraitMethod,
    Effect,
    EffectOperation,
    Handler,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct SemanticSymbolKey {
    pub(super) kind: SemanticSymbolKind,
    pub(super) name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum SemanticDocKey {
    Value(ast::NodeId),
    Type(String),
    Symbol(SemanticSymbolKey),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OccurrenceKind {
    Definition,
    Reference,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SemanticOccurrence {
    kind: OccurrenceKind,
    pub(super) location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NamedLocation {
    pub(super) name: String,
    pub(super) location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SemanticSymbolLocation {
    pub(super) key: SemanticSymbolKey,
    pub(super) location: Location,
}

impl SemanticIndex {
    pub(super) fn new(definition_locations: HashMap<ast::NodeId, Location>) -> Self {
        Self {
            definition_locations,
            references: HashMap::new(),
            references_by_definition: HashMap::new(),
            type_definition_locations: HashMap::new(),
            type_occurrences_by_name: HashMap::new(),
            type_occurrences: Vec::new(),
            module_definition_locations: HashMap::new(),
            module_occurrences_by_name: HashMap::new(),
            module_occurrences: Vec::new(),
            symbol_definition_locations: HashMap::new(),
            symbol_occurrences_by_key: HashMap::new(),
            symbol_occurrences: Vec::new(),
            docs_by_key: HashMap::new(),
        }
    }

    pub(super) fn add_references(
        &mut self,
        references: &HashMap<ast::NodeId, ast::NodeId>,
        definition_nodes: &HashSet<ast::NodeId>,
    ) {
        for (&usage_id, &definition_id) in references {
            self.references.insert(usage_id, definition_id);
            if let Some(location) = self.definition_locations.get(&usage_id) {
                let kind = if definition_nodes.contains(&usage_id) {
                    OccurrenceKind::Definition
                } else {
                    OccurrenceKind::Reference
                };
                self.references_by_definition
                    .entry(definition_id)
                    .or_default()
                    .push(SemanticOccurrence {
                        kind,
                        location: location.clone(),
                    });
            }
        }
    }

    pub(super) fn add_type_definition(&mut self, name: String, location: Location) {
        self.type_definition_locations
            .entry(name.clone())
            .or_insert_with(|| location.clone());
        self.type_occurrences_by_name
            .entry(name.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Definition,
                location: location.clone(),
            });
        self.type_occurrences.push(NamedLocation { name, location });
    }

    pub(super) fn add_type_reference(&mut self, name: String, location: Location) {
        self.type_occurrences_by_name
            .entry(name.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Reference,
                location: location.clone(),
            });
        self.type_occurrences.push(NamedLocation { name, location });
    }

    pub(super) fn add_module_definition(&mut self, name: String, location: Location) {
        self.module_definition_locations
            .entry(name.clone())
            .or_insert_with(|| location.clone());
        self.module_occurrences_by_name
            .entry(name.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Definition,
                location: location.clone(),
            });
        self.module_occurrences
            .push(NamedLocation { name, location });
    }

    pub(super) fn add_module_reference(&mut self, name: String, location: Location) {
        self.module_occurrences_by_name
            .entry(name.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Reference,
                location: location.clone(),
            });
        self.module_occurrences
            .push(NamedLocation { name, location });
    }

    pub(super) fn add_symbol_definition(
        &mut self,
        kind: SemanticSymbolKind,
        name: String,
        location: Location,
    ) {
        let key = SemanticSymbolKey { kind, name };
        self.symbol_definition_locations
            .entry(key.clone())
            .or_insert_with(|| location.clone());
        self.symbol_occurrences_by_key
            .entry(key.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Definition,
                location: location.clone(),
            });
        self.symbol_occurrences
            .push(SemanticSymbolLocation { key, location });
    }

    pub(super) fn add_symbol_reference(
        &mut self,
        kind: SemanticSymbolKind,
        name: String,
        location: Location,
    ) {
        let key = SemanticSymbolKey { kind, name };
        self.symbol_occurrences_by_key
            .entry(key.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Reference,
                location: location.clone(),
            });
        self.symbol_occurrences
            .push(SemanticSymbolLocation { key, location });
    }

    pub(super) fn add_docs(&mut self, key: SemanticDocKey, docs: &[String]) {
        if !docs.is_empty() {
            self.docs_by_key.entry(key).or_insert_with(|| docs.to_vec());
        }
    }

    pub(super) fn type_name_at_position(&self, uri: &Url, position: Position) -> Option<&str> {
        self.type_occurrence_at_position(uri, position)
            .map(|occurrence| occurrence.name.as_str())
    }

    pub(super) fn type_occurrence_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<&NamedLocation> {
        self.type_occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.location.uri == *uri
                    && range_contains_position(&occurrence.location.range, position)
            })
            .min_by_key(|occurrence| range_width(&occurrence.location.range))
    }

    pub(super) fn type_definition_location_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<Location> {
        let name = self.type_name_at_position(uri, position)?;
        self.type_definition_locations.get(name).cloned()
    }

    pub(super) fn type_doc_at_position(&self, uri: &Url, position: Position) -> Option<&[String]> {
        let name = self.type_name_at_position(uri, position)?;
        self.docs_by_key
            .get(&SemanticDocKey::Type(name.to_string()))
            .map(Vec::as_slice)
    }

    pub(super) fn type_reference_locations_at(
        &self,
        uri: &Url,
        position: Position,
        include_declaration: bool,
    ) -> Option<Vec<Location>> {
        let name = self.type_name_at_position(uri, position)?;
        Some(self.type_reference_locations_for_name(name, include_declaration))
    }

    pub(super) fn type_reference_locations_for_name(
        &self,
        name: &str,
        include_declaration: bool,
    ) -> Vec<Location> {
        let mut locations: Vec<Location> = self
            .type_occurrences_by_name
            .get(name)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();
        sort_and_dedup_locations(&mut locations);
        locations
    }

    pub(super) fn symbol_key_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<&SemanticSymbolKey> {
        self.symbol_location_at_position(uri, position)
            .map(|occurrence| &occurrence.key)
    }

    pub(super) fn symbol_location_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<&SemanticSymbolLocation> {
        self.symbol_occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.location.uri == *uri
                    && range_contains_position(&occurrence.location.range, position)
            })
            .min_by_key(|occurrence| range_width(&occurrence.location.range))
    }

    pub(super) fn symbol_definition_location_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<Location> {
        let key = self.symbol_key_at_position(uri, position)?;
        self.symbol_definition_locations.get(key).cloned()
    }

    pub(super) fn module_name_at_position(&self, uri: &Url, position: Position) -> Option<&str> {
        self.module_occurrence_at_position(uri, position)
            .map(|occurrence| occurrence.name.as_str())
    }

    pub(super) fn module_occurrence_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<&NamedLocation> {
        self.module_occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.location.uri == *uri
                    && range_contains_position(&occurrence.location.range, position)
            })
            .min_by_key(|occurrence| range_width(&occurrence.location.range))
    }

    pub(super) fn module_definition_location_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<Location> {
        let name = self.module_name_at_position(uri, position)?;
        self.module_definition_locations.get(name).cloned()
    }

    pub(super) fn module_reference_locations_at(
        &self,
        uri: &Url,
        position: Position,
        include_declaration: bool,
    ) -> Option<Vec<Location>> {
        let name = self.module_name_at_position(uri, position)?;
        Some(self.module_reference_locations_for_name(name, include_declaration))
    }

    pub(super) fn module_reference_locations_for_name(
        &self,
        name: &str,
        include_declaration: bool,
    ) -> Vec<Location> {
        let mut locations: Vec<Location> = self
            .module_occurrences_by_name
            .get(name)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();
        sort_and_dedup_locations(&mut locations);
        locations
    }

    pub(super) fn symbol_reference_locations_at(
        &self,
        uri: &Url,
        position: Position,
        include_declaration: bool,
    ) -> Option<Vec<Location>> {
        let key = self.symbol_key_at_position(uri, position)?;
        Some(self.symbol_reference_locations_for_key(key, include_declaration))
    }

    pub(super) fn symbol_reference_locations_for_key(
        &self,
        key: &SemanticSymbolKey,
        include_declaration: bool,
    ) -> Vec<Location> {
        let mut locations: Vec<Location> = self
            .symbol_occurrences_by_key
            .get(key)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();
        sort_and_dedup_locations(&mut locations);
        locations
    }

    pub(super) fn identity_for_node(&self, node_id: ast::NodeId) -> ast::NodeId {
        self.references.get(&node_id).copied().unwrap_or(node_id)
    }

    pub(super) fn definition_location_for_node(&self, node_id: ast::NodeId) -> Option<Location> {
        let definition_id = self.identity_for_node(node_id);
        self.definition_locations.get(&definition_id).cloned()
    }

    pub(super) fn value_doc_for_node(&self, node_id: ast::NodeId) -> Option<&[String]> {
        let definition_id = self.identity_for_node(node_id);
        self.docs_by_key
            .get(&SemanticDocKey::Value(definition_id))
            .map(Vec::as_slice)
    }

    pub(super) fn reference_locations_for_node(
        &self,
        node_id: ast::NodeId,
        include_declaration: bool,
    ) -> Vec<Location> {
        let definition_id = self.identity_for_node(node_id);
        let mut locations: Vec<Location> = self
            .references_by_definition
            .get(&definition_id)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();

        if include_declaration && let Some(location) = self.definition_locations.get(&definition_id)
        {
            locations.push(location.clone());
        }

        sort_and_dedup_locations(&mut locations);
        locations
    }
}
