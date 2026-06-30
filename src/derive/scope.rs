use super::*;
use crate::ast::*;
use std::collections::HashMap;

/// Minimal trait info captured at expand_derives time so that
/// `inherit_trait_defaults` can clone a trait's default-method bodies into
/// impls that omit them, qualifying free names against the trait's module.
#[derive(Clone)]
pub struct RoutedTraitInfo {
    pub type_params: Vec<TypeParam>,
    pub methods: Vec<TraitMethod>,
    /// Module that defines this trait, e.g. "Lib" or "Std.Generic". Used to
    /// retarget free identifiers in cloned default-method bodies so they
    /// resolve against the trait's defining module rather than the
    /// downstream impl-site module.
    pub defining_module: Option<String>,
    /// Names of top-level `fun` bindings exported from
    /// `defining_module`. A free identifier inside a cloned default body
    /// that matches one of these names is rewritten to a `QualifiedName`
    /// referencing the trait's module, so cross-module impls don't see
    /// "undefined variable" errors for identifiers defined alongside the
    /// trait.
    pub defining_module_values: std::collections::HashSet<String>,
    /// Names of data constructors (ADT variants) declared in
    /// `defining_module`, regardless of whether their type is exported. A
    /// constructor reference inside a cloned default body that matches one of
    /// these is rewritten to its module-qualified canonical name, so
    /// cross-module impls don't see "undefined constructor" errors for
    /// constructors defined alongside the trait.
    pub defining_module_constructors: std::collections::HashSet<String>,
}

pub(crate) struct DeriveScope<'a> {
    pub(crate) imported: &'a ImportedDecls,
    pub(crate) current_module: Option<&'a str>,
    pub(crate) local_traits: HashMap<String, SummaryEntry<RoutedTraitInfo>>,
}

impl<'a> DeriveScope<'a> {
    pub(crate) fn new(imported: &'a ImportedDecls, current_module: Option<&'a str>) -> Self {
        Self {
            imported,
            current_module,
            local_traits: HashMap::new(),
        }
    }

    pub(crate) fn add_local_trait(&mut self, name: String, info: RoutedTraitInfo) {
        insert_local(&mut self.local_traits, self.current_module, name, info);
    }

    pub(crate) fn trait_entry(
        &self,
        name: &str,
    ) -> Result<Option<&SummaryEntry<RoutedTraitInfo>>, String> {
        lookup_summary(name, &self.local_traits, &self.imported.traits, "trait")
    }
}

pub(crate) fn insert_local<T: Clone>(
    map: &mut HashMap<String, SummaryEntry<T>>,
    current_module: Option<&str>,
    name: String,
    info: T,
) {
    let canonical = current_module
        .map(|m| format!("{m}.{name}"))
        .unwrap_or_else(|| name.clone());
    let entry = SummaryEntry { canonical, info };
    map.insert(name.clone(), entry.clone());
    if let Some(module) = current_module {
        map.insert(format!("{module}.{name}"), entry);
    }
}

pub(crate) fn lookup_summary<'a, T>(
    name: &str,
    local: &'a HashMap<String, SummaryEntry<T>>,
    imported: &'a HashMap<String, Vec<SummaryEntry<T>>>,
    label: &str,
) -> Result<Option<&'a SummaryEntry<T>>, String> {
    if let Some(entry) = local.get(name) {
        return Ok(Some(entry));
    }
    let Some(entries) = imported.get(name) else {
        return Ok(None);
    };
    match entries.as_slice() {
        [] => Ok(None),
        [entry] => Ok(Some(entry)),
        many => {
            let mut candidates: Vec<String> = many.iter().map(|e| e.canonical.clone()).collect();
            candidates.sort();
            Err(format!(
                "{label} `{name}` is ambiguous; candidates: {}",
                candidates.join(", ")
            ))
        }
    }
}
