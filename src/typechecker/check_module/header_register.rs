use std::collections::HashMap;

use super::header_scope::scope_for_header_imports;
use super::{
    HeaderEffectRef, HeaderFunction, HeaderHandlerDecl, HeaderTraitBound, HeaderTraitDecl,
    HeaderTraitMethod, HeaderTraitRef, HeaderTypeDecl, HeaderTypeExpr, HeaderTypeParam,
    ModuleHeader,
};
use crate::ast::Kind;
use crate::token::Span;
use crate::typechecker::{
    Checker, EffectDefInfo, EffectEntry, EffectOpSig, EffectRow, HandlerInfo,
    HandlerWhereConstraints, RecordInfo, Scheme, ScopeMap, TraitInfo, TraitMethodEffectSig,
    TraitMethodInfo, Type, TypeAliasInfo, canonical_join, canonicalize_type_name,
    check_traits::FUNCTIONAL_TRAITS, collect_free_vars,
};

const HEADER_SPAN: Span = Span { start: 0, end: 0 };

struct HeaderRegistrationScope {
    module_name: String,
    imports: ScopeMap,
    local_types: HashMap<String, String>,
    local_traits: HashMap<String, String>,
    local_effects: HashMap<String, String>,
}

impl Checker {
    pub(crate) fn register_active_scc_headers(&mut self) -> Result<(), String> {
        let Some(headers) = self.modules.active_scc_headers.clone() else {
            return Ok(());
        };

        for (module_name, header) in &headers {
            let scope = HeaderRegistrationScope::new(module_name, header, &headers)?;
            self.register_header_type_stubs(module_name, header);
            self.register_header_effect_stubs(module_name, header);
            self.register_header_trait_stubs(module_name, header);
            self.register_header_records_and_adts(module_name, header, &scope);
            self.register_header_aliases(module_name, header, &scope);
        }

        for (module_name, header) in &headers {
            let scope = HeaderRegistrationScope::new(module_name, header, &headers)?;
            self.register_header_effect_ops(module_name, header, &scope);
            self.register_header_traits(module_name, header, &scope);
            self.register_header_functions_and_handlers(module_name, header, &scope);
        }

        self.modules
            .registered_canonical
            .extend(headers.keys().cloned());
        Ok(())
    }

    fn register_header_type_stubs(&mut self, module_name: &str, header: &ModuleHeader) {
        for (name, decl) in &header.types {
            if !decl.public() {
                continue;
            }
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
            if !record.public {
                continue;
            }
            let canonical = canonical_join(module_name, name);
            self.type_arity
                .entry(canonical.clone())
                .or_insert(record.type_params.len());
            self.type_param_kinds
                .entry(canonical)
                .or_insert_with(|| header_type_param_kinds(&record.type_params));
        }
    }

    fn register_header_effect_stubs(&mut self, module_name: &str, header: &ModuleHeader) {
        for (name, effect) in &header.effects {
            if !effect.public {
                continue;
            }
            let canonical = canonical_join(module_name, name);
            let type_params = header_type_param_vars(self, &effect.type_params);
            self.type_arity
                .entry(canonical.clone())
                .or_insert(effect.type_params.len());
            self.type_param_kinds
                .entry(canonical.clone())
                .or_insert_with(|| header_type_param_kinds(&effect.type_params));
            self.effects
                .entry(canonical.clone())
                .or_insert_with(|| EffectDefInfo {
                    type_params: type_params.iter().map(|(_, id)| *id).collect(),
                    ops: Vec::new(),
                    op_spans: HashMap::new(),
                    source_module: Some(module_name.to_string()),
                });
        }
    }

    fn register_header_trait_stubs(&mut self, module_name: &str, header: &ModuleHeader) {
        for (name, trait_decl) in &header.traits {
            if !trait_decl.public {
                continue;
            }
            let canonical = canonical_join(module_name, name);
            self.scope_map
                .traits
                .entry(canonical.clone())
                .or_insert_with(|| canonical.clone());
            self.type_arity
                .entry(canonical.clone())
                .or_insert(trait_decl.type_params.len());
            self.type_param_kinds
                .entry(canonical)
                .or_insert_with(|| header_type_param_kinds(&trait_decl.type_params));
        }
    }

    fn register_header_records_and_adts(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
    ) {
        for (name, decl) in &header.types {
            let HeaderTypeDecl::Adt {
                public,
                opaque,
                type_params,
                constructors,
            } = decl
            else {
                continue;
            };
            if !public {
                continue;
            }

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
                    self.env
                        .entry_insert(ctor_canonical.clone(), scheme.clone());
                    variants.push((ctor_canonical, ctor.fields.len()));
                }
            }
            self.adt_variants
                .entry(type_canonical)
                .or_insert_with(|| variants);
        }

        for (name, record) in &header.records {
            if !record.public {
                continue;
            }
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
            self.env.entry_insert(canonical.clone(), scheme);
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

    fn register_header_effect_ops(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
    ) {
        for (name, effect) in &header.effects {
            if !effect.public {
                continue;
            }
            let canonical = canonical_join(module_name, name);
            let effect_param_ids = self
                .effects
                .get(&canonical)
                .map(|info| info.type_params.clone())
                .unwrap_or_default();
            let shared_params: Vec<(String, u32)> = effect
                .type_params
                .iter()
                .zip(effect_param_ids.iter())
                .map(|(tp, id)| (tp.name.clone(), *id))
                .collect();
            let ops: Vec<EffectOpSig> = effect
                .operations
                .iter()
                .map(|op| {
                    let mut params = shared_params.clone();
                    let params_tys = op
                        .params
                        .iter()
                        .map(|(label, ty)| {
                            (
                                label.clone(),
                                self.header_type_expr_to_type(ty, &mut params, scope),
                            )
                        })
                        .collect();
                    let return_type =
                        self.header_type_expr_to_type(&op.return_type, &mut params, scope);
                    let needs = self.header_effect_row(
                        &op.effects,
                        &op.effect_row_vars,
                        &mut params,
                        scope,
                    );
                    EffectOpSig {
                        name: op.name.clone(),
                        effect_name: canonical.clone(),
                        params: params_tys,
                        return_type,
                        needs,
                    }
                })
                .collect();
            self.scope_map
                .register_effect_ops(&canonical, ops.iter().map(|op| op.name.as_str()));
            if let Some(info) = self.effects.get_mut(&canonical) {
                info.ops = ops;
            }
        }
    }

    fn register_header_traits(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
    ) {
        for (name, trait_decl) in &header.traits {
            if !trait_decl.public {
                continue;
            }
            let canonical = canonical_join(module_name, name);
            let methods: Vec<TraitMethodInfo> = trait_decl
                .methods
                .iter()
                .map(|method| self.header_trait_method_info(&canonical, trait_decl, method, scope))
                .collect();
            for method in &methods {
                self.env.entry_insert(
                    canonical_join(&canonical, &method.name),
                    method.scheme.clone(),
                );
            }
            self.scope_map
                .register_trait_methods(&canonical, methods.iter().map(|m| m.name.as_str()));
            let supertraits = trait_decl
                .supertraits
                .iter()
                .map(|tr| self.resolve_header_trait_ref(tr, scope))
                .collect();
            self.trait_state
                .traits
                .entry(canonical.clone())
                .or_insert_with(|| TraitInfo {
                    type_params: trait_decl
                        .type_params
                        .iter()
                        .map(|tp| (tp.name.clone(), tp.kind))
                        .collect(),
                    supertraits,
                    methods,
                    is_functional: FUNCTIONAL_TRAITS.contains(&canonical.as_str()),
                });
        }
    }

    fn register_header_functions_and_handlers(
        &mut self,
        module_name: &str,
        header: &ModuleHeader,
        scope: &HeaderRegistrationScope,
    ) {
        for (name, function) in &header.functions {
            if !function.public {
                continue;
            }
            let scheme = self.header_function_scheme(function, scope);
            let canonical = canonical_join(module_name, name);
            self.env.entry_insert(canonical.clone(), scheme);
            if !function.effects.is_empty() {
                self.effect_meta.known_funs.insert(canonical);
            }
        }

        for (name, handler) in &header.handlers {
            if !handler.public {
                continue;
            }
            let canonical = canonical_join(module_name, name);
            let info = self.header_handler_info(handler, scope);
            self.handlers
                .entry(canonical.clone())
                .or_insert_with(|| info.clone());
            let handler_ty = Type::Con(
                canonicalize_type_name("Handler").to_string(),
                handler
                    .effects
                    .iter()
                    .map(|effect| {
                        Type::Con(
                            self.resolve_header_effect_name(&effect.name, scope),
                            effect
                                .type_args
                                .iter()
                                .map(|arg| {
                                    self.header_type_expr_to_type(arg, &mut Vec::new(), scope)
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            );
            self.env.entry_insert(
                canonical,
                Scheme {
                    forall: Vec::new(),
                    constraints: Vec::new(),
                    ty: handler_ty,
                },
            );
        }
    }

    fn header_trait_method_info(
        &mut self,
        canonical_trait: &str,
        trait_decl: &HeaderTraitDecl,
        method: &HeaderTraitMethod,
        scope: &HeaderRegistrationScope,
    ) -> TraitMethodInfo {
        let mut params = header_type_param_vars(self, &trait_decl.type_params);
        let self_param = trait_decl
            .type_params
            .first()
            .map(|tp| tp.name.as_str())
            .unwrap_or("a");
        let param_types: Vec<Type> = method
            .params
            .iter()
            .map(|(_, ty)| self.header_type_expr_to_type(ty, &mut params, scope))
            .collect();
        let return_type = self.header_type_expr_to_type(&method.return_type, &mut params, scope);
        let effect_row =
            self.header_effect_row(&method.effects, &method.effect_row_vars, &mut params, scope);
        let fun_ty = self.function_type_with_innermost_effects(
            &param_types,
            return_type.clone(),
            effect_row,
        );
        let mut forall = Vec::new();
        collect_free_vars(&fun_ty, &mut forall);
        for (_, id) in &params {
            if !forall.contains(id) {
                forall.push(*id);
            }
        }
        let self_id = params
            .iter()
            .find(|(name, _)| name == self_param)
            .map(|(_, id)| *id);
        let extra_types = trait_decl
            .type_params
            .iter()
            .skip(1)
            .filter_map(|tp| {
                params
                    .iter()
                    .find(|(name, _)| name == &tp.name)
                    .map(|(_, id)| Type::Var(*id))
            })
            .collect();
        let constraints = self_id
            .map(|id| vec![(canonical_trait.to_string(), id, extra_types)])
            .unwrap_or_default();
        let scheme = Scheme {
            forall,
            constraints,
            ty: fun_ty.clone(),
        };
        TraitMethodInfo {
            name: method.name.clone(),
            param_types,
            return_type,
            trait_param_id: self_id,
            scheme,
            effect_sig: header_trait_method_effect_sig(&fun_ty),
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

    fn header_handler_info(
        &mut self,
        handler: &HeaderHandlerDecl,
        scope: &HeaderRegistrationScope,
    ) -> HandlerInfo {
        let mut params = Vec::new();
        let effects = handler
            .effects
            .iter()
            .map(|effect| self.resolve_header_effect_name(&effect.name, scope))
            .collect();
        let needs_effects = self.header_effect_row(&handler.needs, &Vec::new(), &mut params, scope);
        HandlerInfo {
            effects,
            return_type: None,
            needs_effects,
            forall: params.iter().map(|(_, id)| *id).collect(),
            arm_spans: HashMap::new(),
            where_constraints: HandlerWhereConstraints::new(),
            source_module: Some(scope.module_name.clone()),
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

fn header_trait_method_effect_sig(ty: &Type) -> TraitMethodEffectSig {
    let mut user_arity = 0;
    let mut effects = std::collections::BTreeSet::new();
    let mut is_open_row = false;
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        user_arity += 1;
        for entry in &row.effects {
            effects.insert(entry.name.clone());
        }
        if row.is_open() {
            is_open_row = true;
        }
        current = ret;
    }
    TraitMethodEffectSig {
        effects: effects.into_iter().collect(),
        is_open_row,
        user_arity,
    }
}

trait TypeEnvEntryInsert {
    fn entry_insert(&mut self, name: String, scheme: Scheme);
}

impl TypeEnvEntryInsert for crate::typechecker::TypeEnv {
    fn entry_insert(&mut self, name: String, scheme: Scheme) {
        if self.get(&name).is_none() {
            self.insert(name, scheme);
        }
    }
}
