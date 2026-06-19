use std::collections::HashMap;

use super::header_scope::scope_for_header_imports;
use super::{
    HeaderEffectRef, HeaderFunction, HeaderTraitBound, HeaderTraitRef, HeaderTypeDecl,
    HeaderTypeExpr, HeaderTypeParam, ModuleHeader,
};
use crate::ast::{Decl, Kind, NodeId};
use crate::token::Span;
use crate::typechecker::{
    Checker, EffectEntry, EffectRow, RecordInfo, Scheme, ScopeMap, Type, TypeAliasInfo,
    canonical_join, canonicalize_type_name, collect_free_vars,
};

const HEADER_SPAN: Span = Span { start: 0, end: 0 };

struct HeaderRegistrationScope {
    module_name: String,
    imports: ScopeMap,
    local_types: HashMap<String, String>,
    local_traits: HashMap<String, String>,
    local_effects: HashMap<String, String>,
}

#[derive(Debug, Clone, Default)]
struct HeaderLspInfo {
    defs: HashMap<String, (NodeId, Span)>,
    constructors: HashMap<String, (NodeId, Span)>,
    docs: HashMap<String, Vec<String>>,
}

impl Checker {
    pub(crate) fn register_active_scc_headers(&mut self) -> Result<(), String> {
        let Some(headers) = self.modules.active_scc_headers.clone() else {
            return Ok(());
        };
        let lsp_info = self.active_header_lsp_info(&headers);

        for (module_name, header) in &headers {
            let scope = HeaderRegistrationScope::new(module_name, header, &headers)?;
            let lsp = lsp_info.get(module_name);
            self.register_header_type_stubs(module_name, header);
            self.register_header_docs(module_name, lsp);
            self.register_header_records_and_adts(module_name, header, &scope, lsp);
            self.register_header_aliases(module_name, header, &scope);
        }

        for (module_name, header) in &headers {
            let scope = HeaderRegistrationScope::new(module_name, header, &headers)?;
            self.register_header_functions(module_name, header, &scope, lsp_info.get(module_name));
        }

        self.modules
            .registered_canonical
            .extend(headers.keys().cloned());
        Ok(())
    }

    fn active_header_lsp_info(
        &self,
        headers: &HashMap<String, ModuleHeader>,
    ) -> HashMap<String, HeaderLspInfo> {
        headers
            .keys()
            .filter_map(|module| {
                self.modules
                    .programs
                    .get(module)
                    .map(|program| (module.clone(), collect_header_lsp_info(program)))
            })
            .collect()
    }

    fn register_header_docs(&mut self, module_name: &str, lsp: Option<&HeaderLspInfo>) {
        let Some(lsp) = lsp else {
            return;
        };
        for (name, doc) in &lsp.docs {
            self.lsp
                .imported_docs
                .entry(canonical_join(module_name, name))
                .or_insert_with(|| doc.clone());
        }
    }

    fn register_header_type_stubs(&mut self, module_name: &str, header: &ModuleHeader) {
        // Register private types too: a public trait's default-method body may
        // construct values of a type the module keeps private, and the cloned
        // body (inlined into a downstream impl) refers to that type/its
        // constructors by canonical name. Name-resolution privacy is enforced
        // separately (only public items enter the importer's scope), so these
        // canonical-keyed entries don't leak private names to user code.
        for (name, decl) in &header.types {
            let canonical = canonical_join(module_name, name);
            self.type_arity
                .entry(canonical.clone())
                .or_insert(decl.arity());
            self.type_param_kinds.entry(canonical).or_insert_with(|| {
                header_type_param_kinds(match decl {
                    HeaderTypeDecl::Adt { type_params, .. }
                    | HeaderTypeDecl::Alias { type_params, .. } => type_params,
                })
            });
        }
        for (name, record) in &header.records {
            let canonical = canonical_join(module_name, name);
            self.type_arity
                .entry(canonical.clone())
                .or_insert(record.type_params.len());
            self.type_param_kinds
                .entry(canonical)
                .or_insert_with(|| header_type_param_kinds(&record.type_params));
        }
    }

    fn register_header_records_and_adts(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
        lsp: Option<&HeaderLspInfo>,
    ) {
        for (name, decl) in &header.types {
            let HeaderTypeDecl::Adt {
                public: _,
                opaque,
                type_params,
                constructors,
            } = decl
            else {
                continue;
            };

            let mut params = header_type_param_vars(self, type_params);
            let forall: Vec<u32> = params.iter().map(|(_, id)| *id).collect();
            let type_canonical = canonical_join(module_name, name);
            let result_type = Type::Con(
                type_canonical.clone(),
                forall.iter().map(|id| Type::Var(*id)).collect(),
            );
            let mut variants = Vec::new();
            if !opaque {
                for ctor in constructors {
                    let ctor_canonical = canonical_join(module_name, &ctor.name);
                    let mut ctor_ty = result_type.clone();
                    for field in ctor.fields.iter().rev() {
                        let field_ty = self.header_type_expr_to_type(&field.ty, &mut params, scope);
                        ctor_ty = Type::arrow(field_ty, ctor_ty);
                    }
                    let scheme = Scheme {
                        forall: forall.clone(),
                        constraints: Vec::new(),
                        ty: ctor_ty,
                    };
                    self.constructors
                        .entry(ctor_canonical.clone())
                        .or_insert_with(|| scheme.clone());
                    if let Some(&(def_id, _)) =
                        lsp.and_then(|info| info.constructors.get(&ctor.name))
                    {
                        self.lsp
                            .constructor_def_ids
                            .entry(ctor_canonical.clone())
                            .or_insert(def_id);
                        self.env.entry_insert_with_def(
                            ctor_canonical.clone(),
                            scheme.clone(),
                            def_id,
                        );
                    } else {
                        self.env
                            .entry_insert(ctor_canonical.clone(), scheme.clone());
                    }
                    variants.push((ctor_canonical, ctor.fields.len()));
                }
            }
            self.adt_variants
                .entry(type_canonical)
                .or_insert_with(|| variants);
        }

        for (name, record) in &header.records {
            let mut params = header_type_param_vars(self, &record.type_params);
            let forall: Vec<u32> = params.iter().map(|(_, id)| *id).collect();
            let fields: Vec<(String, Type)> = record
                .fields
                .iter()
                .map(|(field, ty)| {
                    (
                        field.clone(),
                        self.header_type_expr_to_type(ty, &mut params, scope),
                    )
                })
                .collect();
            let canonical = canonical_join(module_name, name);
            self.records
                .entry(canonical.clone())
                .or_insert_with(|| RecordInfo {
                    type_params: forall.clone(),
                    fields: fields.clone(),
                });
            let result_type = Type::Con(
                canonical.clone(),
                forall.iter().map(|id| Type::Var(*id)).collect(),
            );
            let mut ctor_ty = result_type;
            for (_, field_ty) in fields.iter().rev() {
                ctor_ty = Type::arrow(field_ty.clone(), ctor_ty);
            }
            let scheme = Scheme {
                forall,
                constraints: Vec::new(),
                ty: ctor_ty,
            };
            self.constructors
                .entry(canonical.clone())
                .or_insert_with(|| scheme.clone());
            if let Some(&(def_id, _)) = lsp.and_then(|info| info.constructors.get(name)) {
                self.lsp
                    .constructor_def_ids
                    .entry(canonical.clone())
                    .or_insert(def_id);
                self.env
                    .entry_insert_with_def(canonical.clone(), scheme, def_id);
            } else {
                self.env.entry_insert(canonical.clone(), scheme);
            }
            self.adt_variants
                .entry(canonical.clone())
                .or_insert_with(|| vec![(canonical, fields.len())]);
        }
    }

    fn register_header_aliases(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
    ) {
        for (name, decl) in &header.types {
            let HeaderTypeDecl::Alias {
                public,
                type_params,
                body,
            } = decl
            else {
                continue;
            };
            if !public {
                continue;
            }
            let mut params = header_type_param_vars(self, type_params);
            let param_vars: Vec<u32> = params.iter().map(|(_, id)| *id).collect();
            let body = self.header_type_expr_to_type(body, &mut params, scope);
            self.type_aliases
                .entry(canonical_join(module_name, name))
                .or_insert_with(|| TypeAliasInfo {
                    param_vars,
                    param_kinds: header_type_param_kinds(type_params),
                    body,
                    span: HEADER_SPAN,
                });
        }
    }

    fn register_header_functions(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
        lsp: Option<&HeaderLspInfo>,
    ) {
        for (name, function) in &header.functions {
            if !function.public {
                continue;
            }
            let scheme = self.header_function_scheme(function, scope);
            let canonical = canonical_join(module_name, name);
            if type_contains_effects(&scheme.ty) {
                self.effect_meta.known_funs.insert(canonical.clone());
            }
            if let Some(&(def_id, _)) = lsp.and_then(|info| info.defs.get(name)) {
                self.env.entry_insert_with_def(canonical, scheme, def_id);
            } else {
                self.env.entry_insert(canonical, scheme);
            }
        }
    }

    fn header_function_scheme(
        &mut self,
        function: &HeaderFunction,
        scope: &HeaderRegistrationScope,
    ) -> Scheme {
        let mut params = Vec::new();
        let param_types: Vec<Type> = function
            .params
            .iter()
            .map(|(_, ty)| self.header_type_expr_to_type(ty, &mut params, scope))
            .collect();
        let return_type = self.header_type_expr_to_type(&function.return_type, &mut params, scope);
        let effect_row = self.header_effect_row(
            &function.effects,
            &function.effect_row_vars,
            &mut params,
            scope,
        );
        let ty = self.function_type_with_innermost_effects(&param_types, return_type, effect_row);
        let mut forall = Vec::new();
        collect_free_vars(&ty, &mut forall);
        let constraints =
            header_trait_constraints(self, &function.where_clause, &mut params, scope);
        for (_, id, extra) in &constraints {
            if !forall.contains(id) {
                forall.push(*id);
            }
            for ty in extra {
                collect_free_vars(ty, &mut forall);
            }
        }
        Scheme {
            forall,
            constraints,
            ty,
        }
    }

    fn header_type_expr_to_type(
        &mut self,
        ty: &HeaderTypeExpr,
        params: &mut Vec<(String, u32)>,
        scope: &HeaderRegistrationScope,
    ) -> Type {
        match ty {
            HeaderTypeExpr::Named(name) => {
                Type::Con(self.resolve_header_type_name(name, scope), Vec::new())
            }
            HeaderTypeExpr::Var(name) => {
                if let Some((_, id)) = params.iter().find(|(param, _)| param == name) {
                    Type::Var(*id)
                } else {
                    let id = self.next_var;
                    self.next_var += 1;
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            }
            HeaderTypeExpr::App { func, arg } => {
                let func_ty = self.header_type_expr_to_type(func, params, scope);
                let arg_ty = self.header_type_expr_to_type(arg, params, scope);
                match func_ty {
                    Type::Con(name, mut args) => {
                        args.push(arg_ty);
                        Type::Con(name, args)
                    }
                    other => Type::Con(format!("{other}"), vec![arg_ty]),
                }
            }
            HeaderTypeExpr::Arrow {
                from,
                to,
                effects,
                effect_row_vars,
            } => Type::Fun(
                Box::new(self.header_type_expr_to_type(from, params, scope)),
                Box::new(self.header_type_expr_to_type(to, params, scope)),
                self.header_effect_row(effects, effect_row_vars, params, scope),
            ),
            HeaderTypeExpr::Record(fields) => {
                let mut fields: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(name, ty)| {
                        (
                            name.clone(),
                            self.header_type_expr_to_type(ty, params, scope),
                        )
                    })
                    .collect();
                fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Type::Record(fields)
            }
            HeaderTypeExpr::Labeled { inner, .. } => {
                self.header_type_expr_to_type(inner, params, scope)
            }
            HeaderTypeExpr::Symbol(name) => Type::Symbol(name.clone()),
        }
    }

    fn header_effect_row(
        &mut self,
        effects: &[HeaderEffectRef],
        effect_row_vars: &[String],
        params: &mut Vec<(String, u32)>,
        scope: &HeaderRegistrationScope,
    ) -> EffectRow {
        let entries = effects
            .iter()
            .map(|effect| {
                let args = effect
                    .type_args
                    .iter()
                    .map(|arg| self.header_type_expr_to_type(arg, params, scope))
                    .collect();
                EffectEntry::unnamed(self.resolve_header_effect_name(&effect.name, scope), args)
            })
            .collect();
        let tails = effect_row_vars
            .iter()
            .map(|name| {
                if let Some((_, id)) = params.iter().find(|(param, _)| param == name) {
                    Type::Var(*id)
                } else {
                    let id = self.next_var;
                    self.next_var += 1;
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            })
            .collect();
        EffectRow {
            effects: entries,
            tails,
        }
    }

    fn resolve_header_type_name(&self, name: &str, scope: &HeaderRegistrationScope) -> String {
        scope
            .local_types
            .get(name)
            .cloned()
            .or_else(|| scope.imports.resolve_type(name).map(str::to_string))
            .or_else(|| self.scope_map.resolve_type(name).map(str::to_string))
            .unwrap_or_else(|| {
                if name.contains('.') {
                    name.to_string()
                } else {
                    canonicalize_type_name(name).to_string()
                }
            })
    }

    fn resolve_header_effect_name(&self, name: &str, scope: &HeaderRegistrationScope) -> String {
        scope
            .local_effects
            .get(name)
            .cloned()
            .or_else(|| scope.imports.resolve_effect(name).map(str::to_string))
            .or_else(|| self.scope_map.resolve_effect(name).map(str::to_string))
            .unwrap_or_else(|| {
                if name.contains('.') {
                    name.to_string()
                } else {
                    canonical_join(&scope.module_name, name)
                }
            })
    }

    fn resolve_header_trait_ref(
        &self,
        trait_ref: &HeaderTraitRef,
        scope: &HeaderRegistrationScope,
    ) -> String {
        scope
            .local_traits
            .get(&trait_ref.name)
            .cloned()
            .or_else(|| {
                scope
                    .imports
                    .resolve_trait(&trait_ref.name)
                    .map(str::to_string)
            })
            .or_else(|| {
                self.scope_map
                    .resolve_trait(&trait_ref.name)
                    .map(str::to_string)
            })
            .unwrap_or_else(|| {
                if trait_ref.name.contains('.') {
                    trait_ref.name.clone()
                } else {
                    canonical_join(&scope.module_name, &trait_ref.name)
                }
            })
    }
}

impl HeaderRegistrationScope {
    fn new(
        module_name: &str,
        header: &ModuleHeader,
        headers: &HashMap<String, ModuleHeader>,
    ) -> Result<Self, String> {
        let imports = scope_for_header_imports(header, headers)?;
        let local_types = header
            .types
            .keys()
            .chain(header.records.keys())
            .map(|name| (name.clone(), canonical_join(module_name, name)))
            .collect();
        let local_traits = header
            .traits
            .keys()
            .map(|name| (name.clone(), canonical_join(module_name, name)))
            .collect();
        let local_effects = header
            .effects
            .keys()
            .map(|name| (name.clone(), canonical_join(module_name, name)))
            .collect();
        Ok(HeaderRegistrationScope {
            module_name: module_name.to_string(),
            imports,
            local_types,
            local_traits,
            local_effects,
        })
    }
}

fn header_type_param_vars(checker: &mut Checker, params: &[HeaderTypeParam]) -> Vec<(String, u32)> {
    params
        .iter()
        .map(|param| {
            let var = checker.fresh_var_of_kind(param.kind);
            let Type::Var(id) = var else { unreachable!() };
            (param.name.clone(), id)
        })
        .collect()
}

fn header_type_param_kinds(params: &[HeaderTypeParam]) -> Vec<Kind> {
    params.iter().map(|param| param.kind).collect()
}

fn header_trait_constraints(
    checker: &mut Checker,
    bounds: &[HeaderTraitBound],
    params: &mut Vec<(String, u32)>,
    scope: &HeaderRegistrationScope,
) -> Vec<(String, u32, Vec<Type>)> {
    let mut constraints = Vec::new();
    for bound in bounds {
        let var_id = if let Some((_, id)) = params.iter().find(|(name, _)| name == &bound.type_var)
        {
            *id
        } else {
            let id = checker.next_var;
            checker.next_var += 1;
            params.push((bound.type_var.clone(), id));
            id
        };
        for trait_ref in &bound.traits {
            let trait_name = checker.resolve_header_trait_ref(trait_ref, scope);
            let extra = trait_ref
                .type_args
                .iter()
                .map(|arg| checker.header_type_expr_to_type(arg, params, scope))
                .collect();
            constraints.push((trait_name, var_id, extra));
        }
    }
    constraints
}

trait TypeEnvEntryInsert {
    fn entry_insert(&mut self, name: String, scheme: Scheme);
    fn entry_insert_with_def(&mut self, name: String, scheme: Scheme, def_id: NodeId);
}

fn type_contains_effects(ty: &Type) -> bool {
    match ty {
        Type::Fun(param, ret, row) => {
            !row.is_empty() || type_contains_effects(param) || type_contains_effects(ret)
        }
        Type::Con(_, args) => args.iter().any(type_contains_effects),
        Type::Record(fields) => fields.iter().any(|(_, ty)| type_contains_effects(ty)),
        Type::Var(_) | Type::Symbol(_) | Type::Error => false,
    }
}

impl TypeEnvEntryInsert for crate::typechecker::TypeEnv {
    fn entry_insert(&mut self, name: String, scheme: Scheme) {
        if self.get(&name).is_none() {
            self.insert(name, scheme);
        }
    }

    fn entry_insert_with_def(&mut self, name: String, scheme: Scheme, def_id: NodeId) {
        if self.get(&name).is_none() {
            self.insert_with_def(name, scheme, def_id);
        }
    }
}

fn collect_header_lsp_info(program: &[Decl]) -> HeaderLspInfo {
    let mut info = HeaderLspInfo::default();
    for decl in program {
        match decl {
            Decl::FunSignature {
                id,
                public: true,
                name,
                name_span,
                doc,
                ..
            } => {
                info.defs.insert(name.clone(), (*id, *name_span));
                insert_doc(&mut info, name, doc);
            }
            Decl::TypeDef {
                public: true,
                name,
                variants,
                doc,
                ..
            } => {
                insert_doc(&mut info, name, doc);
                for variant in variants {
                    info.constructors.insert(
                        variant.node.name.clone(),
                        (variant.node.id, variant.node.span),
                    );
                }
            }
            Decl::TypeAlias {
                public: true,
                name,
                doc,
                ..
            }
            | Decl::EffectDef {
                public: true,
                name,
                doc,
                ..
            }
            | Decl::HandlerDef {
                public: true,
                name,
                doc,
                ..
            }
            | Decl::TraitDef {
                public: true,
                name,
                doc,
                ..
            } => insert_doc(&mut info, name, doc),
            Decl::RecordDef {
                id,
                public: true,
                name,
                name_span,
                doc,
                ..
            } => {
                info.constructors.insert(name.clone(), (*id, *name_span));
                insert_doc(&mut info, name, doc);
            }
            _ => {}
        }
    }
    info
}

fn insert_doc(info: &mut HeaderLspInfo, name: &str, doc: &[String]) {
    if !doc.is_empty() {
        info.docs.insert(name.to_string(), doc.to_vec());
    }
}
