use super::*;
use crate::ast::*;
use crate::token::Span;
use std::collections::HashMap;

/// Minimal trait info captured at expand_derives time for routed-derive
/// method/signature discovery. We only need the method names and signature
/// shapes — direction detection and body generation work off these.
#[derive(Clone)]
pub struct RoutedTraitInfo {
    pub type_params: Vec<TypeParam>,
    pub is_functional: bool,
    /// The trait's functional dependency, if any. A record-synthesizing trait
    /// reads carrier vs. synthesized roles from it (determinant = carrier,
    /// determined = synthesized type).
    pub fundep: Option<TraitFunctionalDependency>,
    /// `synthesizes via <Trait> deriving (...)` metadata, if this is a
    /// record-synthesizing link trait. Trait names within are qualified to the
    /// trait's defining module so they resolve at any derive site.
    pub synthesis: Option<SynthesisSpec>,
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


/// A trait impl captured at derive time, used to resolve the scope parameter of
/// a parameterized record when applying a routed functional derive (see
/// `determine_scope_specialization`). Only impls with a structured target are
/// kept, since those are the ones a record field can match against.
#[derive(Clone)]
pub(crate) struct DeriveImplInfo {
    pub(crate) trait_bare: String,
    pub(crate) target: TypeExpr,
    /// The single non-self trait argument (the determined "row" of a functional
    /// two-parameter trait).
    pub(crate) row: TypeExpr,
}


pub(crate) struct DeriveScope<'a> {
    pub(crate) imported: &'a ImportedDecls,
    pub(crate) current_module: Option<&'a str>,
    pub(crate) local_traits: HashMap<String, SummaryEntry<RoutedTraitInfo>>,
    pub(crate) local_types: HashMap<String, SummaryEntry<WrapperTypeInfo>>,
    pub(crate) local_records: HashMap<String, SummaryEntry<WrapperRecordInfo>>,
    pub(crate) local_impls: Vec<DeriveImplInfo>,
}


impl<'a> DeriveScope<'a> {
    pub(crate) fn new(imported: &'a ImportedDecls, current_module: Option<&'a str>) -> Self {
        Self {
            imported,
            current_module,
            local_traits: HashMap::new(),
            local_types: HashMap::new(),
            local_records: HashMap::new(),
            local_impls: Vec::new(),
        }
    }

    pub(crate) fn add_local_trait(&mut self, name: String, info: RoutedTraitInfo) {
        insert_local(&mut self.local_traits, self.current_module, name, info);
    }

    pub(crate) fn add_local_type(&mut self, name: String, info: WrapperTypeInfo) {
        insert_local(&mut self.local_types, self.current_module, name, info);
    }

    pub(crate) fn add_local_record(&mut self, name: String, info: WrapperRecordInfo) {
        insert_local(&mut self.local_records, self.current_module, name, info);
    }

    pub(crate) fn trait_entry(&self, name: &str) -> Result<Option<&SummaryEntry<RoutedTraitInfo>>, String> {
        lookup_summary(name, &self.local_traits, &self.imported.traits, "trait")
    }

    pub(crate) fn type_entry(&self, name: &str) -> Result<Option<&SummaryEntry<WrapperTypeInfo>>, String> {
        lookup_summary(
            name,
            &self.local_types,
            &self.imported.types,
            "wrapper type",
        )
    }

    pub(crate) fn record_entry(&self, name: &str) -> Result<Option<&SummaryEntry<WrapperRecordInfo>>, String> {
        lookup_summary(
            name,
            &self.local_records,
            &self.imported.records,
            "wrapper record",
        )
    }
}


/// Qualify a bare trait name in a `synthesizes` clause to the trait's defining
/// module, so it resolves at any derive site (imported modules register every
/// public trait under its `Module.Name` key regardless of the `exposing` list).
/// Already-qualified names are left as written.
pub(crate) fn qualify_synthesis_spec(
    spec: &SynthesisSpec,
    defining_module: Option<&str>,
) -> SynthesisSpec {
    let qualify = |name: &str| -> String {
        match defining_module {
            Some(m) if !name.contains('.') => format!("{m}.{name}"),
            _ => name.to_string(),
        }
    };
    SynthesisSpec {
        via_trait: qualify(&spec.via_trait),
        via_trait_span: spec.via_trait_span,
        attach_derives: spec
            .attach_derives
            .iter()
            .map(|d| DeriveSpec {
                trait_name: qualify(&d.trait_name),
                trait_name_span: d.trait_name_span,
                type_args: d.type_args.clone(),
                span: d.span,
            })
            .collect(),
        span: spec.span,
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


pub(crate) fn is_hardcoded_derive(bare: &str) -> bool {
    matches!(
        bare,
        "Show" | "Debug" | "Eq" | "Ord" | "Enum" | "Generic" | "Default"
    )
}

// --- Derive-time TypeExpr matching (for scope specialization) ---------------
//
// A small Robinson-style unifier over `TypeExpr`, used to figure out the
// concrete value a parameterized record's scope variable must take so that each
// field column is `Selectable` to the requested row's field. All `Var` nodes
// are treated as unification holes; `Named`/`Symbol` are rigid constructors.
// Callers rename each side's variables with a distinct prefix so the two
// namespaces don't collide.


/// Determine concrete values for a parameterized record's type parameters when
/// applying a routed functional derive. For each record field, find the unique
/// trait impl whose target matches the field *and* whose determined row matches
/// the corresponding field of the requested row type; read off which record
/// parameters that forces to a concrete type. Returns the map of record
/// parameter name -> concrete `TypeExpr` (empty if nothing can be pinned, in
/// which case the caller falls back to leaving the parameters polymorphic).
pub(crate) fn determine_scope_specialization(
    trait_bare: &str,
    type_name: &str,
    type_params: &[TypeParam],
    row_type: &TypeExpr,
    scope: &DeriveScope<'_>,
) -> HashMap<String, TypeExpr> {
    let mut bindings: HashMap<String, TypeExpr> = HashMap::new();
    if type_params.is_empty() {
        return bindings;
    }
    let param_names: std::collections::HashSet<&str> =
        type_params.iter().map(|p| p.name.as_str()).collect();

    let Ok(Some(source_entry)) = scope.record_entry(type_name) else {
        return bindings;
    };
    let Some(row_head) = row_type.head_name() else {
        return bindings;
    };
    let Ok(Some(row_entry)) = scope.record_entry(row_head) else {
        return bindings;
    };
    // The row type must be unparameterized for a direct field-type comparison.
    if !row_entry.info.type_params.is_empty() {
        return bindings;
    }
    let row_fields: HashMap<&str, &TypeExpr> = row_entry
        .info
        .fields
        .iter()
        .map(|(n, t)| (n.as_str(), t))
        .collect();

    for (fname, col_te) in &source_entry.info.fields {
        let Some(row_te) = row_fields.get(fname.as_str()) else {
            continue;
        };
        let Some(col_head) = te_head(col_te) else {
            continue;
        };
        let col_renamed = te_rename_vars(col_te, "s$");
        let row_renamed = te_rename_vars(row_te, "w$");

        let mut field_bindings: Option<HashMap<String, TypeExpr>> = None;
        let mut ambiguous = false;
        for imp in scope.local_impls.iter().chain(scope.imported.impls.iter()) {
            if imp.trait_bare != trait_bare {
                continue;
            }
            if te_head(&imp.target).as_deref() != Some(col_head.as_str()) {
                continue;
            }
            let target_renamed = te_rename_vars(&imp.target, "i$");
            let impl_row_renamed = te_rename_vars(&imp.row, "i$");
            let mut subst = HashMap::new();
            if !te_unify(&col_renamed, &target_renamed, &mut subst) {
                continue;
            }
            if !te_unify(&row_renamed, &impl_row_renamed, &mut subst) {
                continue;
            }
            // Read off which record parameters this impl forces concrete.
            let mut here: HashMap<String, TypeExpr> = HashMap::new();
            for p in &param_names {
                let resolved = te_apply(
                    &TypeExpr::Var {
                        id: NodeId::fresh(),
                        name: format!("s${p}"),
                        span: Span { start: 0, end: 0 },
                    },
                    &subst,
                );
                if te_is_concrete(&resolved) {
                    here.insert((*p).to_string(), resolved);
                }
            }
            if field_bindings.is_some() {
                ambiguous = true;
                break;
            }
            field_bindings = Some(here);
        }
        if ambiguous {
            continue;
        }
        if let Some(here) = field_bindings {
            for (k, v) in here {
                match bindings.get(&k) {
                    Some(existing) if !te_structural_eq(existing, &v) => {
                        // Conflicting requirements across fields — give up on
                        // specializing this parameter.
                        bindings.remove(&k);
                    }
                    Some(_) => {}
                    None => {
                        bindings.insert(k, v);
                    }
                }
            }
        }
    }
    bindings
}

