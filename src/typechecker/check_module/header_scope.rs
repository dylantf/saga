use std::collections::{BTreeSet, HashMap, HashSet};

use super::{
    HeaderExposedItem, HeaderExposing, HeaderFunction, HeaderReExport, HeaderTypeDecl,
    HeaderTypeExpr, ModuleHeader,
};
use crate::typechecker::{RecordBuilderInfo, ScopeMap, canonical_join};

#[derive(Debug, Clone, PartialEq, Eq)]
struct HeaderTypeSurface {
    canonical: String,
    constructors: Vec<HeaderConstructorSurface>,
    record_builder: Option<RecordBuilderInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HeaderConstructorSurface {
    surface_name: String,
    canonical: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HeaderTraitSurface {
    canonical: String,
    methods: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HeaderEffectSurface {
    canonical: String,
    ops: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct HeaderSurface {
    values: HashMap<String, String>,
    handlers: HashMap<String, String>,
    types: HashMap<String, HeaderTypeSurface>,
    constructors: HashMap<String, String>,
    traits: HashMap<String, HeaderTraitSurface>,
    effects: HashMap<String, HeaderEffectSurface>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum HeaderNamespace {
    Value,
    Handler,
    Type,
    Constructor,
    Trait,
    Effect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum HeaderResolved {
    Canonical(String),
    Type(HeaderTypeSurface),
    Trait(HeaderTraitSurface),
    Effect(HeaderEffectSurface),
}

/// Build scope entries for an import using only pre-inference module headers.
pub(crate) fn resolve_header_import(
    headers: &HashMap<String, ModuleHeader>,
    module_name: &str,
    prefix: &str,
    exposing: Option<&HeaderExposing>,
) -> Result<ScopeMap, String> {
    let surface = public_header_surface(headers, module_name)?;
    let mut scope = ScopeMap::default();

    insert_header_qualified_entries(&mut scope, &surface, module_name, prefix);
    match exposing {
        None => {}
        Some(HeaderExposing::All { .. }) => {
            for item in exposed_items_for_surface(&surface) {
                insert_header_exposed_item(headers, module_name, &mut scope, &item)?;
            }
        }
        Some(HeaderExposing::Items(items)) => {
            for item in items {
                insert_header_exposed_item(headers, module_name, &mut scope, item)?;
            }
        }
    }
    insert_header_origins(&mut scope);
    Ok(scope)
}

/// Build a module's imported scope from its imports and the already-extracted
/// headers around it. This is intentionally pure data plumbing: no checker
/// state, no inference, no `NodeId`s.
pub(crate) fn scope_for_header_imports(
    header: &ModuleHeader,
    headers: &HashMap<String, ModuleHeader>,
) -> Result<ScopeMap, String> {
    let mut scope = ScopeMap::default();
    for import in &header.imports {
        let prefix = import
            .alias
            .as_deref()
            .unwrap_or_else(|| import.module.rsplit('.').next().unwrap_or(&import.module));
        let import_scope =
            resolve_header_import(headers, &import.module, prefix, import.exposing.as_ref())?;
        scope.merge(&import_scope);
    }
    Ok(scope)
}

fn insert_header_qualified_entries(
    scope: &mut ScopeMap,
    surface: &HeaderSurface,
    module_name: &str,
    prefix: &str,
) {
    for (name, canonical) in &surface.values {
        insert_qualified(&mut scope.values, canonical, module_name, prefix, name);
    }
    for (name, info) in &surface.types {
        insert_qualified(&mut scope.types, &info.canonical, module_name, prefix, name);
        if let Some(builder) = &info.record_builder {
            scope
                .record_builders
                .entry(builder.context.clone())
                .or_insert_with(|| builder.clone());
        }
    }
    for (name, canonical) in &surface.constructors {
        insert_qualified(
            &mut scope.constructors,
            canonical,
            module_name,
            prefix,
            name,
        );
    }
}

fn insert_qualified(
    map: &mut HashMap<String, String>,
    canonical: &str,
    module_name: &str,
    prefix: &str,
    surface_name: &str,
) {
    map.entry(canonical.to_string())
        .or_insert_with(|| canonical.to_string());
    map.entry(canonical_join(module_name, surface_name))
        .or_insert_with(|| canonical.to_string());
    if prefix != module_name {
        map.entry(canonical_join(prefix, surface_name))
            .or_insert_with(|| canonical.to_string());
    }
}

fn insert_header_exposed_item(
    headers: &HashMap<String, ModuleHeader>,
    module_name: &str,
    scope: &mut ScopeMap,
    item: &HeaderExposedItem,
) -> Result<(), String> {
    let name = item.name.as_str();
    let surface = item.surface_name();
    let mut found = false;

    if resolve_header_surface_name(headers, module_name, name, HeaderNamespace::Handler)?.is_some()
    {
        return Err(unsupported_cycle_import(name, module_name, "handler"));
    }
    if resolve_header_surface_name(headers, module_name, name, HeaderNamespace::Trait)?.is_some() {
        return Err(unsupported_cycle_import(name, module_name, "trait"));
    }
    if resolve_header_surface_name(headers, module_name, name, HeaderNamespace::Effect)?.is_some() {
        return Err(unsupported_cycle_import(name, module_name, "effect"));
    }

    if let Some(HeaderResolved::Canonical(canonical)) =
        resolve_header_surface_name(headers, module_name, name, HeaderNamespace::Value)?
    {
        if let Some(error) = unsupported_function_boundary(headers, &canonical) {
            return Err(error);
        }
        scope.values.entry(surface.to_string()).or_insert(canonical);
        found = true;
    }
    if let Some(HeaderResolved::Canonical(canonical)) =
        resolve_header_surface_name(headers, module_name, name, HeaderNamespace::Constructor)?
    {
        scope
            .constructors
            .entry(surface.to_string())
            .or_insert_with(|| canonical.clone());
        scope.values.entry(surface.to_string()).or_insert(canonical);
        found = true;
    }
    if let Some(HeaderResolved::Type(info)) =
        resolve_header_surface_name(headers, module_name, name, HeaderNamespace::Type)?
    {
        scope
            .types
            .entry(surface.to_string())
            .or_insert_with(|| info.canonical.clone());
        for ctor in &info.constructors {
            scope
                .constructors
                .entry(ctor.surface_name.clone())
                .or_insert_with(|| ctor.canonical.clone());
            scope
                .values
                .entry(ctor.surface_name.clone())
                .or_insert_with(|| ctor.canonical.clone());
        }
        if let Some(builder) = &info.record_builder {
            scope
                .record_builders
                .entry(builder.context.clone())
                .or_insert_with(|| builder.clone());
        }
        found = true;
    }
    if found {
        Ok(())
    } else if headers
        .get(module_name)
        .is_some_and(|header| header.unannotated_functions.iter().any(|fun| fun == name))
    {
        Err(format!(
            "function '{}' from module '{}' needs a type annotation to be used across a circular import boundary",
            name, module_name
        ))
    } else {
        Err(format!(
            "'{}' is not exported by module '{}'",
            name, module_name
        ))
    }
}

fn exposed_items_for_surface(surface: &HeaderSurface) -> Vec<HeaderExposedItem> {
    let mut names = BTreeSet::new();
    names.extend(surface.values.keys().cloned());
    names.extend(surface.types.keys().cloned());
    names
        .into_iter()
        .map(|name| HeaderExposedItem {
            name,
            alias: None,
            public: false,
        })
        .collect()
}

fn insert_header_origins(scope: &mut ScopeMap) {
    let canonicals = scope
        .values
        .values()
        .chain(scope.handlers.values())
        .chain(scope.constructors.values())
        .chain(scope.effects.values())
        .chain(scope.traits.values())
        .chain(scope.types.values())
        .chain(scope.record_builders.keys())
        .cloned()
        .collect::<Vec<_>>();
    for canonical in canonicals {
        scope
            .origins
            .entry(canonical.clone())
            .or_insert_with(|| canonical_module(&canonical));
    }
}

fn canonical_module(canonical: &str) -> String {
    canonical
        .rsplit_once('.')
        .map(|(module, _)| module.to_string())
        .unwrap_or_else(|| canonical.to_string())
}

fn public_header_surface(
    headers: &HashMap<String, ModuleHeader>,
    module_name: &str,
) -> Result<HeaderSurface, String> {
    let mut visiting = HashSet::new();
    collect_header_surface(headers, module_name, &mut visiting)
}

fn collect_header_surface(
    headers: &HashMap<String, ModuleHeader>,
    module_name: &str,
    visiting: &mut HashSet<String>,
) -> Result<HeaderSurface, String> {
    if !visiting.insert(module_name.to_string()) {
        return Ok(HeaderSurface::default());
    }
    let header = headers
        .get(module_name)
        .ok_or_else(|| format!("unknown module '{}'", module_name))?;
    let mut surface = local_header_surface(module_name, header);

    for edge in &header.re_exports {
        merge_explicit_header_re_export(headers, &mut surface, edge)?;
    }
    for edge in &header.re_export_all {
        let imported = collect_header_surface(headers, &edge.origin_module, visiting)?;
        surface.merge(imported);
    }

    visiting.remove(module_name);
    Ok(surface)
}

fn local_header_surface(module_name: &str, header: &ModuleHeader) -> HeaderSurface {
    let mut surface = HeaderSurface::default();
    for (name, function) in &header.functions {
        if function.public {
            surface
                .values
                .insert(name.clone(), canonical_join(module_name, name));
        }
    }
    for (name, decl) in &header.types {
        if !decl.public() {
            continue;
        }
        let constructors = match decl {
            HeaderTypeDecl::Adt {
                opaque,
                constructors,
                ..
            } if !opaque => constructors
                .iter()
                .map(|ctor| HeaderConstructorSurface {
                    surface_name: ctor.name.clone(),
                    canonical: canonical_join(module_name, &ctor.name),
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        surface.types.insert(
            name.clone(),
            HeaderTypeSurface {
                canonical: canonical_join(module_name, name),
                constructors: constructors.clone(),
                record_builder: None,
            },
        );
        for ctor in constructors {
            surface
                .constructors
                .insert(ctor.surface_name.clone(), ctor.canonical.clone());
            surface.values.insert(ctor.surface_name, ctor.canonical);
        }
    }
    for (name, record) in &header.records {
        if record.public {
            let canonical = canonical_join(module_name, name);
            surface.types.insert(
                name.clone(),
                HeaderTypeSurface {
                    canonical: canonical.clone(),
                    constructors: vec![HeaderConstructorSurface {
                        surface_name: name.clone(),
                        canonical: canonical.clone(),
                    }],
                    record_builder: None,
                },
            );
            surface.constructors.insert(name.clone(), canonical.clone());
            surface.values.insert(name.clone(), canonical);
        }
    }
    for (name, trait_decl) in &header.traits {
        if trait_decl.public {
            surface.traits.insert(
                name.clone(),
                HeaderTraitSurface {
                    canonical: canonical_join(module_name, name),
                    methods: trait_decl
                        .methods
                        .iter()
                        .map(|method| method.name.clone())
                        .collect(),
                },
            );
        }
    }
    for (name, effect) in &header.effects {
        if effect.public {
            surface.effects.insert(
                name.clone(),
                HeaderEffectSurface {
                    canonical: canonical_join(module_name, name),
                    ops: effect.operations.iter().map(|op| op.name.clone()).collect(),
                },
            );
        }
    }
    for (name, handler) in &header.handlers {
        if handler.public {
            let canonical = canonical_join(module_name, name);
            surface.handlers.insert(name.clone(), canonical.clone());
            surface.values.insert(name.clone(), canonical);
        }
    }
    for builder in header.record_builders.values() {
        if !builder.public {
            continue;
        }
        let context_surface = builder
            .context
            .rsplit('.')
            .next()
            .unwrap_or(builder.context.as_str());
        let Some(start) = resolve_local_header_value(&surface, module_name, &builder.start) else {
            continue;
        };
        let Some(field) = resolve_local_header_value(&surface, module_name, &builder.field) else {
            continue;
        };
        let Some(context_type) = surface.types.get_mut(context_surface) else {
            continue;
        };
        context_type.record_builder = Some(RecordBuilderInfo {
            context: context_type.canonical.clone(),
            start,
            field,
        });
    }
    surface
}

fn resolve_local_header_value(
    surface: &HeaderSurface,
    module_name: &str,
    name: &str,
) -> Option<String> {
    surface.values.get(name).cloned().or_else(|| {
        name.rsplit_once('.').and_then(|(module, value)| {
            if module == module_name {
                surface.values.get(value).cloned()
            } else {
                Some(name.to_string())
            }
        })
    })
}

fn merge_explicit_header_re_export(
    headers: &HashMap<String, ModuleHeader>,
    surface: &mut HeaderSurface,
    edge: &HeaderReExport,
) -> Result<(), String> {
    for namespace in [
        HeaderNamespace::Value,
        HeaderNamespace::Handler,
        HeaderNamespace::Type,
        HeaderNamespace::Constructor,
        HeaderNamespace::Trait,
        HeaderNamespace::Effect,
    ] {
        if let Some(resolved) =
            resolve_header_surface_name(headers, &edge.origin_module, &edge.origin_name, namespace)?
        {
            surface.insert_resolved(&edge.origin_name, &edge.surface_name, namespace, resolved);
        }
    }
    Ok(())
}

fn resolve_header_surface_name(
    headers: &HashMap<String, ModuleHeader>,
    module_name: &str,
    name: &str,
    namespace: HeaderNamespace,
) -> Result<Option<HeaderResolved>, String> {
    let mut path = Vec::new();
    resolve_header_surface_name_inner(headers, module_name, name, namespace, &mut path, true)
}

fn resolve_header_surface_name_inner(
    headers: &HashMap<String, ModuleHeader>,
    module_name: &str,
    name: &str,
    namespace: HeaderNamespace,
    path: &mut Vec<(String, String, HeaderNamespace)>,
    strict_cycles: bool,
) -> Result<Option<HeaderResolved>, String> {
    let key = (module_name.to_string(), name.to_string(), namespace);
    if path.contains(&key) {
        if strict_cycles {
            return Err(format!(
                "re-export cycle while resolving '{}' from module '{}'",
                name, module_name
            ));
        }
        return Ok(None);
    }
    path.push(key);

    let header = headers
        .get(module_name)
        .ok_or_else(|| format!("unknown module '{}'", module_name))?;
    if let Some(local) = local_header_surface(module_name, header).resolve(name, namespace) {
        path.pop();
        return Ok(Some(local));
    }

    for edge in &header.re_exports {
        if edge.surface_name == name
            && let Some(resolved) = resolve_header_surface_name_inner(
                headers,
                &edge.origin_module,
                &edge.origin_name,
                namespace,
                path,
                true,
            )?
        {
            path.pop();
            return Ok(Some(resolved));
        }
    }
    for edge in &header.re_export_all {
        if let Some(resolved) = resolve_header_surface_name_inner(
            headers,
            &edge.origin_module,
            name,
            namespace,
            path,
            false,
        )? {
            path.pop();
            return Ok(Some(resolved));
        }
    }

    path.pop();
    Ok(None)
}

fn unsupported_cycle_import(name: &str, module_name: &str, kind: &str) -> String {
    format!(
        "{} '{}' from module '{}' cannot be used across a circular import boundary; move it to a shared module",
        kind, name, module_name
    )
}

fn unsupported_function_boundary(
    headers: &HashMap<String, ModuleHeader>,
    canonical: &str,
) -> Option<String> {
    let (module_name, name) = canonical.rsplit_once('.')?;
    let function = headers.get(module_name)?.functions.get(name)?;
    if !function.public {
        return None;
    }
    if !function.where_clause.is_empty() {
        return Some(format!(
            "function '{}' from module '{}' uses trait constraints that cannot cross a circular import boundary; move it to a shared module",
            name, module_name
        ));
    }
    if header_function_uses_effects(function) {
        return Some(format!(
            "function '{}' from module '{}' uses effects that cannot cross a circular import boundary; move it to a shared module",
            name, module_name
        ));
    }
    None
}

fn header_function_uses_effects(function: &HeaderFunction) -> bool {
    !function.effects.is_empty()
        || !function.effect_row_vars.is_empty()
        || function
            .params
            .iter()
            .any(|(_, ty)| header_type_expr_uses_effects(ty))
        || header_type_expr_uses_effects(&function.return_type)
}

fn header_type_expr_uses_effects(ty: &HeaderTypeExpr) -> bool {
    match ty {
        HeaderTypeExpr::Arrow {
            from,
            to,
            effects,
            effect_row_vars,
        } => {
            !effects.is_empty()
                || !effect_row_vars.is_empty()
                || header_type_expr_uses_effects(from)
                || header_type_expr_uses_effects(to)
        }
        HeaderTypeExpr::App { func, arg } => {
            header_type_expr_uses_effects(func) || header_type_expr_uses_effects(arg)
        }
        HeaderTypeExpr::Record(fields) => fields
            .iter()
            .any(|(_, ty)| header_type_expr_uses_effects(ty)),
        HeaderTypeExpr::Labeled { inner, .. } => header_type_expr_uses_effects(inner),
        HeaderTypeExpr::Named(_) | HeaderTypeExpr::Var(_) => false,
    }
}

impl HeaderSurface {
    fn resolve(&self, name: &str, namespace: HeaderNamespace) -> Option<HeaderResolved> {
        match namespace {
            HeaderNamespace::Value => self
                .values
                .get(name)
                .cloned()
                .map(HeaderResolved::Canonical),
            HeaderNamespace::Handler => self
                .handlers
                .get(name)
                .cloned()
                .map(HeaderResolved::Canonical),
            HeaderNamespace::Type => self.types.get(name).cloned().map(HeaderResolved::Type),
            HeaderNamespace::Constructor => self
                .constructors
                .get(name)
                .cloned()
                .map(HeaderResolved::Canonical),
            HeaderNamespace::Trait => self.traits.get(name).cloned().map(HeaderResolved::Trait),
            HeaderNamespace::Effect => self.effects.get(name).cloned().map(HeaderResolved::Effect),
        }
    }

    fn insert_resolved(
        &mut self,
        origin_name: &str,
        surface_name: &str,
        namespace: HeaderNamespace,
        resolved: HeaderResolved,
    ) {
        match (namespace, resolved) {
            (HeaderNamespace::Value, HeaderResolved::Canonical(canonical)) => {
                self.values
                    .entry(surface_name.to_string())
                    .or_insert(canonical);
            }
            (HeaderNamespace::Handler, HeaderResolved::Canonical(canonical)) => {
                self.handlers
                    .entry(surface_name.to_string())
                    .or_insert(canonical);
            }
            (HeaderNamespace::Constructor, HeaderResolved::Canonical(canonical)) => {
                self.constructors
                    .entry(surface_name.to_string())
                    .or_insert_with(|| canonical.clone());
                self.values
                    .entry(surface_name.to_string())
                    .or_insert(canonical);
            }
            (HeaderNamespace::Type, HeaderResolved::Type(mut info)) => {
                for ctor in &mut info.constructors {
                    if ctor.surface_name == origin_name {
                        ctor.surface_name = surface_name.to_string();
                    }
                }
                for ctor in &info.constructors {
                    self.constructors
                        .entry(ctor.surface_name.clone())
                        .or_insert_with(|| ctor.canonical.clone());
                    self.values
                        .entry(ctor.surface_name.clone())
                        .or_insert_with(|| ctor.canonical.clone());
                }
                self.types.entry(surface_name.to_string()).or_insert(info);
            }
            (HeaderNamespace::Trait, HeaderResolved::Trait(info)) => {
                self.traits.entry(surface_name.to_string()).or_insert(info);
            }
            (HeaderNamespace::Effect, HeaderResolved::Effect(info)) => {
                self.effects.entry(surface_name.to_string()).or_insert(info);
            }
            _ => {}
        }
    }

    fn merge(&mut self, other: HeaderSurface) {
        for (name, canonical) in other.values {
            self.values.entry(name).or_insert(canonical);
        }
        for (name, canonical) in other.handlers {
            self.handlers.entry(name).or_insert(canonical);
        }
        for (name, info) in other.types {
            self.types.entry(name).or_insert(info);
        }
        for (name, canonical) in other.constructors {
            self.constructors.entry(name).or_insert(canonical);
        }
        for (name, info) in other.traits {
            self.traits.entry(name).or_insert(info);
        }
        for (name, info) in other.effects {
            self.effects.entry(name).or_insert(info);
        }
    }
}

#[cfg(test)]
mod header_scope_tests {
    use super::*;

    fn header(src: &str) -> ModuleHeader {
        let tokens = crate::lexer::Lexer::new(src).lex().expect("lex");
        let program = crate::parser::Parser::new(tokens)
            .parse_program()
            .expect("parse");
        ModuleHeader::from_program(&program)
    }

    fn headers(modules: &[(&str, &str)]) -> HashMap<String, ModuleHeader> {
        modules
            .iter()
            .map(|(name, src)| ((*name).to_string(), header(src)))
            .collect()
    }

    #[test]
    fn header_import_scope_uses_headers_without_inference() {
        let headers = headers(&[(
            "B",
            r#"
module B

pub fun make : Unit -> Choice
make () = Left

pub type Choice = Left | Right
pub record User { name: String }
"#,
        )]);

        let scope = resolve_header_import(
            &headers,
            "B",
            "B",
            Some(&HeaderExposing::Items(vec![
                HeaderExposedItem {
                    name: "make".to_string(),
                    alias: None,
                    public: false,
                },
                HeaderExposedItem {
                    name: "Choice".to_string(),
                    alias: None,
                    public: false,
                },
                HeaderExposedItem {
                    name: "User".to_string(),
                    alias: None,
                    public: false,
                },
            ])),
        )
        .expect("header scope");

        assert_eq!(scope.resolve_value("make"), Some("B.make"));
        assert_eq!(scope.resolve_type("Choice"), Some("B.Choice"));
        assert_eq!(scope.resolve_constructor("Left"), Some("B.Left"));
        assert_eq!(scope.resolve_constructor("User"), Some("B.User"));
    }

    #[test]
    fn header_scope_follows_re_export_edges_to_origin() {
        let headers = headers(&[
            (
                "A",
                r#"
module A
import B (pub value as exposed, pub Choice as PublicChoice)
"#,
            ),
            (
                "B",
                r#"
module B
pub fun value : Unit -> Unit
value () = ()
pub type Choice = Pick
"#,
            ),
            (
                "C",
                r#"
module C
import A (exposed, PublicChoice)
"#,
            ),
        ]);
        let c = headers.get("C").expect("C");

        let scope = scope_for_header_imports(c, &headers).expect("header scope");

        assert_eq!(scope.resolve_value("exposed"), Some("B.value"));
        assert_eq!(scope.resolve_value("A.exposed"), Some("B.value"));
        assert_eq!(scope.resolve_type("PublicChoice"), Some("B.Choice"));
        assert_eq!(scope.resolve_constructor("Pick"), Some("B.Pick"));
    }

    #[test]
    fn header_scope_reports_ungrounded_re_export_cycle() {
        let headers = headers(&[
            (
                "A",
                r#"
module A
import B (pub x)
"#,
            ),
            (
                "B",
                r#"
module B
import A (pub x)
"#,
            ),
        ]);

        let err = resolve_header_import(
            &headers,
            "A",
            "A",
            Some(&HeaderExposing::Items(vec![HeaderExposedItem {
                name: "x".to_string(),
                alias: None,
                public: false,
            }])),
        )
        .expect_err("cycle");

        assert!(err.contains("re-export cycle"));
    }

    #[test]
    fn header_scope_treats_pub_dot_dot_cycle_as_not_found() {
        let headers = headers(&[
            (
                "B",
                r#"
module B
import C (pub ..)
"#,
            ),
            (
                "C",
                r#"
module C
import B (pub ..)
"#,
            ),
        ]);

        let err = resolve_header_import(
            &headers,
            "B",
            "B",
            Some(&HeaderExposing::Items(vec![HeaderExposedItem {
                name: "Missing".to_string(),
                alias: None,
                public: false,
            }])),
        )
        .expect_err("missing export");

        assert!(err.contains("'Missing' is not exported by module 'B'"));
    }
}
