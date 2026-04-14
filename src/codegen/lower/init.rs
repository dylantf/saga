/// Module initialization: registers effect definitions, handler definitions,
/// function metadata, imports, and type constructors from the program's
/// declarations and imported module codegen info.
use crate::ast::{self, Decl};
use std::collections::{BTreeSet, HashMap};

use super::util;
use super::{EffectInfo, FunInfo, HandlerInfo, Lowerer};

fn count_lambda_params(body: &ast::Expr) -> usize {
    match &body.kind {
        ast::ExprKind::Lambda { params, body, .. } => params.len() + count_lambda_params(body),
        _ => 0,
    }
}

/// Extract the (module, func) pair from an `@external("runtime", "module", "func")` annotation.
pub fn extract_external(annotations: &[ast::Annotation]) -> Option<(String, String)> {
    annotations
        .iter()
        .find(|a| a.name == "external")
        .and_then(|a| {
            if a.args.len() >= 3
                && let (ast::Lit::String(module, _), ast::Lit::String(func, _)) =
                    (&a.args[1], &a.args[2])
            {
                return Some((module.clone(), func.clone()));
            }
            None
        })
}

/// Staging area for FunSignature data consumed by FunBinding.
/// Keeps fun_info free of half-initialized entries.
pub(super) struct PendingAnnotation {
    pub effects: Vec<String>,
    pub param_absorbed_effects: HashMap<usize, Vec<String>>,
}

impl<'a> Lowerer<'a> {
    fn source_module_info(program: &ast::Program, module_name: &str) -> (bool, String) {
        let has_module_decl = program.iter().any(|d| matches!(d, Decl::ModuleDecl { .. }));
        let source_module_name = program
            .iter()
            .find_map(|d| {
                if let Decl::ModuleDecl { path, .. } = d {
                    Some(path.join("."))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| module_name.to_string());
        (has_module_decl, source_module_name)
    }

    fn canonical_name(map: &HashMap<String, String>, bare: &str) -> String {
        map.get(bare).cloned().unwrap_or_else(|| bare.to_string())
    }

    fn resolved_type_effects_for_module(
        &self,
        module_name: &str,
        ty: &ast::TypeExpr,
    ) -> BTreeSet<String> {
        match ty {
            ast::TypeExpr::Arrow {
                from, to, effects, ..
            } => {
                let mut effect_names: BTreeSet<String> = effects
                    .iter()
                    .map(|eff| self.resolved_effect_ref_for_module(module_name, eff))
                    .collect();
                effect_names.extend(self.resolved_type_effects_for_module(module_name, from));
                effect_names.extend(self.resolved_type_effects_for_module(module_name, to));
                effect_names
            }
            ast::TypeExpr::App { func, arg, .. } => {
                let mut effect_names = self.resolved_type_effects_for_module(module_name, func);
                effect_names.extend(self.resolved_type_effects_for_module(module_name, arg));
                effect_names
            }
            ast::TypeExpr::Record { fields, .. } => {
                let mut effect_names = BTreeSet::new();
                for (_, field_ty) in fields {
                    effect_names.extend(self.resolved_type_effects_for_module(module_name, field_ty));
                }
                effect_names
            }
            ast::TypeExpr::Labeled { inner, .. } => {
                self.resolved_type_effects_for_module(module_name, inner)
            }
            ast::TypeExpr::Named { .. } | ast::TypeExpr::Var { .. } => BTreeSet::new(),
        }
    }

    fn initialize_canonical_name_maps(
        &mut self,
        program: &ast::Program,
        source_module_name: &str,
    ) -> (HashMap<String, String>, HashMap<String, String>) {
        let mut effect_canonical: HashMap<String, String> = HashMap::new();
        for decl in program {
            if let Decl::EffectDef { name, .. } = decl {
                effect_canonical.insert(name.clone(), format!("{}.{}", source_module_name, name));
            }
        }
        for (_, module_semantics) in self.ctx.modules_semantics() {
            for eff_def in &module_semantics.codegen_info.effect_defs {
                if let Some(dot_pos) = eff_def.name.rfind('.') {
                    let bare = &eff_def.name[dot_pos + 1..];
                    effect_canonical
                        .entry(bare.to_string())
                        .or_insert_with(|| eff_def.name.clone());
                }
            }
        }
        for (user_visible, canonical) in &self.check_result.scope_map.effects {
            effect_canonical
                .entry(user_visible.clone())
                .or_insert_with(|| canonical.clone());
        }

        let mut handler_canonical: HashMap<String, String> = HashMap::new();
        for decl in program {
            if let Decl::HandlerDef { name, .. } = decl {
                handler_canonical.insert(name.clone(), format!("{}.{}", source_module_name, name));
            }
        }
        for (_, module_semantics) in self.ctx.modules_semantics() {
            for handler_name in &module_semantics.codegen_info.handler_defs {
                if let Some(dot_pos) = handler_name.rfind('.') {
                    let bare = &handler_name[dot_pos + 1..];
                    handler_canonical
                        .entry(bare.to_string())
                        .or_insert_with(|| handler_name.clone());
                }
            }
        }
        for (user_visible, canonical) in &self.check_result.scope_map.handlers {
            handler_canonical
                .entry(user_visible.clone())
                .or_insert_with(|| canonical.clone());
        }

        self.effect_canonical = effect_canonical.clone();
        self.handler_canonical = handler_canonical.clone();

        for canonical in self.check_result.resolution.effects.values() {
            if let Some(dot_pos) = canonical.rfind('.') {
                let bare = &canonical[dot_pos + 1..];
                effect_canonical
                    .entry(bare.to_string())
                    .or_insert_with(|| canonical.clone());
            }
            effect_canonical
                .entry(canonical.clone())
                .or_insert_with(|| canonical.clone());
        }

        (effect_canonical, handler_canonical)
    }

    fn register_local_module_decls(
        &mut self,
        program: &ast::Program,
        module_name: &str,
        source_module_name: &str,
        has_module_decl: bool,
        _effect_canonical: &HashMap<String, String>,
        pending_annotations: &mut HashMap<String, PendingAnnotation>,
    ) {
        for decl in program {
            match decl {
                Decl::RecordDef { name, fields, .. } => {
                    let field_names = fields.iter().map(|a| a.node.0.clone()).collect();
                    let key = if has_module_decl {
                        format!("{}.{}", source_module_name, name)
                    } else {
                        name.clone()
                    };
                    self.record_fields.insert(key, field_names);
                }
                Decl::TypeDef { .. } => {
                    // Constructor atom mangling is handled by resolve::build_constructor_atoms
                }
                Decl::EffectDef {
                    name, operations, ..
                } => {
                    let canonical_effect = format!("{}.{}", source_module_name, name);
                    let mut ops = HashMap::new();
                    for op in operations {
                        let is_runtime_unit_param = |ty: &crate::ast::TypeExpr| {
                            matches!(
                                ty,
                                crate::ast::TypeExpr::Named { name, .. }
                                    if crate::typechecker::canonicalize_type_name(name)
                                        == crate::typechecker::canonicalize_type_name("Unit")
                            )
                        };
                        let runtime_param_count = op
                            .node
                            .params
                            .iter()
                            .filter(|(_, ty)| !is_runtime_unit_param(ty))
                            .count();
                        let param_absorbed_effects = op
                            .node
                            .params
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, (_, ty))| {
                                let effs = self.resolved_type_effects_for_module(source_module_name, ty);
                                if effs.is_empty() {
                                    None
                                } else {
                                    let mut sorted: Vec<String> = effs
                                        .into_iter()
                                        .collect();
                                    sorted.sort();
                                    Some((idx, sorted))
                                }
                            })
                            .collect();
                        ops.insert(
                            op.node.name.clone(),
                            super::EffectOpInfo {
                                runtime_param_count,
                                source_param_count: op.node.params.len(),
                                runtime_param_positions: op
                                    .node
                                    .params
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(idx, (_, ty))| {
                                        (!is_runtime_unit_param(ty)).then_some(idx)
                                    })
                                    .collect(),
                                param_absorbed_effects,
                            },
                        );
                        self.op_to_effect
                            .insert(op.node.name.clone(), canonical_effect.clone());
                    }
                    self.effect_defs
                        .insert(canonical_effect, EffectInfo { ops });
                }
                Decl::HandlerDef { name, body, .. } => {
                    let canonical_handler = format!("{}.{}", source_module_name, name);
                    self.handler_defs.insert(
                        canonical_handler,
                        HandlerInfo {
                            effects: self
                                .resolved_effect_refs_for_module(source_module_name, &body.effects),
                            arms: body.arms.iter().map(|a| a.node.clone()).collect(),
                            return_clause: body.return_clause.clone(),
                            source_module: Some(module_name.to_string()),
                        },
                    );
                }
                Decl::FunSignature {
                    public,
                    name,
                    effects,
                    params,
                    annotations,
                    ..
                } => {
                    if *public {
                        self.pub_names.insert(name.clone());
                    }
                    if let Some((_erl_module, _erl_func)) = extract_external(annotations) {
                        let real_arity = params.len();
                        let mut sorted_effects = Vec::new();
                        if !effects.is_empty() {
                            sorted_effects = effects
                                .iter()
                                .map(|e| self.resolved_effect_ref_for_module(source_module_name, e))
                                .collect();
                            sorted_effects.sort();
                        }
                        let expanded_arity = self.expanded_arity(real_arity, &sorted_effects);
                        self.fun_info.insert(
                            name.clone(),
                            FunInfo {
                                arity: expanded_arity,
                                effects: sorted_effects,
                                param_absorbed_effects: HashMap::new(),
                            },
                        );
                    } else {
                        let mut sorted_effects: Vec<String> = effects
                            .iter()
                            .map(|e| self.resolved_effect_ref_for_module(source_module_name, e))
                            .collect();
                        sorted_effects.sort();
                        let param_effs: HashMap<usize, Vec<String>> = self
                            .check_result
                            .env
                            .get(name)
                            .map(|scheme| {
                                let resolved_ty = self.check_result.sub.apply(&scheme.ty);
                                util::param_absorbed_effects_from_type(&resolved_ty)
                                    .into_iter()
                                    .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                                    .collect()
                            })
                            .unwrap_or_else(|| {
                                let mut param_effs: HashMap<usize, Vec<String>> = HashMap::new();
                                for (i, (_param_name, type_expr)) in params.iter().enumerate() {
                                    let effs = self
                                        .resolved_type_effects_for_module(source_module_name, type_expr);
                                    if !effs.is_empty() {
                                        let mut sorted: Vec<String> = effs.into_iter().collect();
                                        sorted.sort();
                                        param_effs.insert(i, sorted);
                                    }
                                }
                                param_effs
                            });
                        pending_annotations.insert(
                            name.clone(),
                            PendingAnnotation {
                                effects: sorted_effects,
                                param_absorbed_effects: param_effs,
                            },
                        );
                    }
                }
                Decl::Val { public, name, .. } => {
                    if *public {
                        self.pub_names.insert(name.clone());
                    }
                    self.fun_info.insert(name.clone(), FunInfo::default());
                }
                _ => {}
            }
        }
    }

    fn register_std_module_semantics(
        &mut self,
        _effect_canonical: &HashMap<String, String>,
        handler_canonical: &HashMap<String, String>,
    ) {
        let canonicalize_handler = |bare: &str| Self::canonical_name(handler_canonical, bare);

        for (mod_name, module_semantics) in self.ctx.modules_semantics() {
            let info = module_semantics.codegen_info;
            let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
            let erlang_name = util::module_name_to_erlang(&mod_path);
            for d in &info.trait_impl_dicts {
                self.fun_info.entry(d.dict_name.clone()).or_insert(FunInfo {
                    arity: d.arity,
                    ..Default::default()
                });
            }
            if mod_name.starts_with("Std.") {
                let alias = mod_path.last().unwrap().clone();
                self.module_aliases
                    .entry(alias.clone())
                    .or_insert_with(|| erlang_name.clone());

                for eff_def in &info.effect_defs {
                    let mut ops_map = HashMap::new();
                    for op in &eff_def.ops {
                        ops_map.insert(
                            op.name.clone(),
                            super::EffectOpInfo {
                                source_param_count: op.source_param_count,
                                runtime_param_count: op.runtime_param_count,
                                runtime_param_positions: op.runtime_param_positions.clone(),
                                param_absorbed_effects: op.param_absorbed_effects.clone(),
                            },
                        );
                        self.op_to_effect
                            .entry(op.name.clone())
                            .or_insert_with(|| eff_def.name.clone());
                    }
                    self.effect_defs
                        .entry(eff_def.name.clone())
                        .or_insert(EffectInfo { ops: ops_map });
                }

                for (name, scheme) in &info.exports {
                    let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
                    let effects = self.canonicalize_effects(effects);
                    let dict_param_count = util::dict_param_count(&scheme.constraints);
                    let expanded_arity =
                        self.expanded_arity(base_arity, &effects) + dict_param_count;
                    let param_absorbed = util::param_absorbed_effects_from_type(&scheme.ty);
                    let param_absorbed: HashMap<usize, Vec<String>> = param_absorbed
                        .into_iter()
                        .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                        .collect();
                    let fi = FunInfo {
                        arity: expanded_arity,
                        effects,
                        param_absorbed_effects: param_absorbed,
                    };
                    let alias_qualified = format!("{}.{}", mod_path.last().unwrap(), name);
                    self.fun_info.entry(alias_qualified).or_insert(fi.clone());
                    let canonical = format!("{}.{}", mod_name, name);
                    self.fun_info.entry(canonical).or_insert(fi);
                }

                self.register_imported_module_local_funs(mod_name, module_semantics.elaborated);
                for decl in module_semantics.elaborated {
                    match decl {
                        Decl::HandlerDef { name, body, .. } => {
                            let canonical_handler = canonicalize_handler(name);
                            let resolved_effects =
                                self.resolved_effect_refs_for_module(mod_name, &body.effects);
                            self.handler_defs
                                .entry(canonical_handler)
                                .or_insert(HandlerInfo {
                                    effects: resolved_effects,
                                    arms: body.arms.iter().map(|a| a.node.clone()).collect(),
                                    return_clause: body.return_clause.clone(),
                                    source_module: Some(mod_name.to_string()),
                                });
                        }
                        Decl::FunSignature { .. } => {}
                        _ => {}
                    }
                }
            }
        }
    }

    fn register_imported_effect_defs(&mut self, info: &crate::typechecker::ModuleCodegenInfo) {
        for eff_def in &info.effect_defs {
            let mut ops_map = HashMap::new();
            for op in &eff_def.ops {
                ops_map.insert(
                    op.name.clone(),
                    super::EffectOpInfo {
                        source_param_count: op.source_param_count,
                        runtime_param_count: op.runtime_param_count,
                        runtime_param_positions: op.runtime_param_positions.clone(),
                        param_absorbed_effects: op.param_absorbed_effects.clone(),
                    },
                );
                self.op_to_effect
                    .insert(op.name.clone(), eff_def.name.clone());
            }
            self.effect_defs
                .insert(eff_def.name.clone(), EffectInfo { ops: ops_map });
        }
    }

    fn register_imported_exports(
        &mut self,
        module_name: &str,
        prefix: &str,
        exposing: Option<&[String]>,
        info: &crate::typechecker::ModuleCodegenInfo,
    ) {
        let is_exposed = |name: &str| match exposing {
            None => false,
            Some(names) => names.iter().any(|n| n == name),
        };
        let exported_names: std::collections::HashSet<&str> =
            info.exports.iter().map(|(n, _)| n.as_str()).collect();

        for (name, scheme) in &info.exports {
            let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
            let effects = self.canonicalize_effects(effects);
            let dict_param_count = util::dict_param_count(&scheme.constraints);
            let expanded_arity = self.expanded_arity(base_arity, &effects) + dict_param_count;
            let param_effs = util::param_absorbed_effects_from_type(&scheme.ty);
            let param_effs: HashMap<usize, Vec<String>> = param_effs
                .into_iter()
                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                .collect();

            let alias_qualified = format!("{}.{}", prefix, name);
            let fi = FunInfo {
                arity: expanded_arity,
                effects: effects.clone(),
                param_absorbed_effects: param_effs.clone(),
            };
            self.fun_info.insert(alias_qualified, fi.clone());
            let canonical = format!("{}.{}", module_name, name);
            self.fun_info.entry(canonical).or_insert(fi);

            if is_exposed(name) && exported_names.contains(name.as_str()) {
                self.fun_info.entry(name.clone()).or_insert(FunInfo {
                    arity: expanded_arity,
                    effects,
                    param_absorbed_effects: param_effs,
                });
            }
        }
    }

    fn register_imported_records_and_dicts(
        &mut self,
        module_name: &str,
        info: &crate::typechecker::ModuleCodegenInfo,
    ) {
        for (rec_name, fields) in &info.record_fields {
            let canonical = format!("{}.{}", module_name, rec_name);
            self.record_fields.insert(canonical, fields.clone());
        }

        for d in &info.trait_impl_dicts {
            self.fun_info.entry(d.dict_name.clone()).or_insert(FunInfo {
                arity: d.arity,
                ..Default::default()
            });
        }
    }

    fn register_imported_handler_defs(&mut self, module_name: &str, program: &ast::Program) {
        self.register_imported_module_local_funs(module_name, program);
        let (_, source_module_name) = Self::source_module_info(program, module_name);
        for decl in program {
            match decl {
                Decl::HandlerDef { name, body, .. } => {
                    let canonical_effects =
                        self.resolved_effect_refs_for_module(&source_module_name, &body.effects);
                    let canonical_handler = format!("{}.{}", module_name, name);
                    self.handler_defs
                        .entry(canonical_handler)
                        .or_insert(HandlerInfo {
                            effects: canonical_effects,
                            arms: body.arms.iter().map(|a| a.node.clone()).collect(),
                            return_clause: body.return_clause.clone(),
                            source_module: Some(module_name.to_string()),
                        });
                }
                Decl::FunSignature { .. } => {
                    // External function resolution handled by resolve.rs
                }
                _ => {}
            }
        }
    }

    fn register_imported_module_local_funs(&mut self, module_name: &str, program: &ast::Program) {
        let (_, source_module_name) = Self::source_module_info(program, module_name);

        let mut pending_annotations: HashMap<String, PendingAnnotation> = HashMap::new();
        for decl in program {
            if let Decl::FunSignature {
                name,
                effects,
                params,
                ..
            } = decl
            {
                let mut sorted_effects: Vec<String> = effects
                    .iter()
                    .map(|eff| self.resolved_effect_ref_for_module(&source_module_name, eff))
                    .collect();
                sorted_effects.sort();
                let mut param_effs: HashMap<usize, Vec<String>> = HashMap::new();
                for (i, (_param_name, type_expr)) in params.iter().enumerate() {
                    let effs =
                        self.resolved_type_effects_for_module(&source_module_name, type_expr);
                    if !effs.is_empty() {
                        let mut sorted: Vec<String> = effs
                            .into_iter()
                            .collect();
                        sorted.sort();
                        param_effs.insert(i, sorted);
                    }
                }
                pending_annotations.insert(
                    name.clone(),
                    PendingAnnotation {
                        effects: sorted_effects,
                        param_absorbed_effects: param_effs,
                    },
                );
            }
        }

        for decl in program {
            match decl {
                Decl::FunBinding {
                    name, params, body, ..
                } => {
                    let PendingAnnotation {
                        effects,
                        param_absorbed_effects,
                    } = pending_annotations
                        .remove(name.as_str())
                        .unwrap_or(PendingAnnotation {
                            effects: Vec::new(),
                            param_absorbed_effects: HashMap::new(),
                        });
                    let mut base_arity = params.len() + count_lambda_params(body);
                    // Use annotation arity for eta-reduced functions (same fix as mod.rs)
                    if let Some(scheme) = self.check_result.env.get(name) {
                        let declared =
                            super::util::arity_and_effects_from_type(
                                &self.check_result.sub.apply(&scheme.ty),
                            )
                            .0;
                        if declared > base_arity {
                            base_arity = declared;
                        }
                    }
                    let arity = self.expanded_arity(base_arity, &effects);
                    let canonical = format!("{}.{}", source_module_name, name);
                    self.fun_info.entry(canonical).or_insert(FunInfo {
                        arity,
                        effects,
                        param_absorbed_effects,
                    });
                }
                Decl::Val { name, .. } => {
                    let canonical = format!("{}.{}", source_module_name, name);
                    self.fun_info.entry(canonical).or_insert(FunInfo {
                        arity: 0,
                        ..Default::default()
                    });
                }
                _ => {}
            }
        }
    }

    /// Initialize the lowerer's lookup tables from program declarations and
    /// imported module codegen info. Returns pending annotations to be consumed
    /// during function grouping.
    pub(super) fn init_module(
        &mut self,
        module_name: &str,
        program: &ast::Program,
    ) -> HashMap<String, PendingAnnotation> {
        let mut pending_annotations: HashMap<String, PendingAnnotation> = HashMap::new();
        let (has_module_decl, source_module_name) = Self::source_module_info(program, module_name);
        let (effect_canonical, handler_canonical) =
            self.initialize_canonical_name_maps(program, &source_module_name);
        self.register_local_module_decls(
            program,
            module_name,
            &source_module_name,
            has_module_decl,
            &effect_canonical,
            &mut pending_annotations,
        );
        self.register_std_module_semantics(&effect_canonical, &handler_canonical);

        // Process prelude imports first so stdlib names are available,
        // then user imports (which can override prelude names).
        for decl in &self.ctx.prelude_imports {
            self.register_import(decl);
        }
        // Pre-populate lookup tables from user-imported modules' codegen info.
        for decl in program {
            self.register_import(decl);
        }
        // Register anonymous record types found in record field types and expressions.
        Self::collect_anon_records_from_program(program, &mut self.record_fields);

        // Pre-register qualified constructor atoms for private constructors from
        // handler source modules. Public constructors are already registered by
        // build_constructor_atoms, but private ones (used inside imported handler
        // bodies) are not. Register them under qualified names only so they don't
        // shadow bare-name BEAM overrides or local constructors.
        self.register_handler_source_module_ctors();

        pending_annotations
    }

    /// Register a single import declaration (from prelude or user code).
    /// Processes the module's exports, effects, records, constructors, dicts,
    /// handlers, and external functions.
    fn register_import(&mut self, decl: &Decl) {
        let Decl::Import {
            module_path,
            alias,
            exposing,
            ..
        } = decl
        else {
            return;
        };

        let module_name = module_path.join(".");
        let prefix = alias
            .as_deref()
            .map(|a| a.to_string())
            .unwrap_or_else(|| module_path.last().unwrap().to_string());
        let erlang_name = util::module_name_to_erlang(module_path);
        self.module_aliases
            .insert(prefix.clone(), erlang_name.clone());

        let Some(module_semantics) = self.ctx.module_semantics(&module_name) else {
            return;
        };
        let info = module_semantics.codegen_info;
        self.register_imported_effect_defs(info);
        self.register_imported_exports(&module_name, &prefix, exposing.as_deref(), info);
        self.register_imported_records_and_dicts(&module_name, info);
        self.register_imported_handler_defs(&module_name, module_semantics.elaborated);
    }

    /// Walk the AST to find anonymous record types and register them in record_fields.
    fn collect_anon_records_from_program(
        program: &[Decl],
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        for decl in program {
            if let Decl::RecordDef { fields, .. } = decl {
                for a in fields {
                    let (_, type_expr) = &a.node;
                    Self::collect_anon_records_from_type_expr(type_expr, record_fields);
                }
            }
            // Also walk function bodies for AnonRecordCreate expressions
            if let Decl::FunBinding { body, .. } = decl {
                Self::collect_anon_records_from_expr(body, record_fields);
            }
        }
    }

    fn collect_anon_records_from_type_expr(
        type_expr: &ast::TypeExpr,
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        match type_expr {
            ast::TypeExpr::Record { fields, .. } => {
                let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                let tag = ast::anon_record_tag(&names);
                let mut sorted_names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                sorted_names.sort();
                record_fields.entry(tag).or_insert(sorted_names);
                // Recurse into field types for nested anonymous records
                for (_, inner_type) in fields {
                    Self::collect_anon_records_from_type_expr(inner_type, record_fields);
                }
            }
            ast::TypeExpr::App { func, arg, .. } => {
                Self::collect_anon_records_from_type_expr(func, record_fields);
                Self::collect_anon_records_from_type_expr(arg, record_fields);
            }
            ast::TypeExpr::Arrow { from, to, .. } => {
                Self::collect_anon_records_from_type_expr(from, record_fields);
                Self::collect_anon_records_from_type_expr(to, record_fields);
            }
            ast::TypeExpr::Labeled { inner, .. } => {
                Self::collect_anon_records_from_type_expr(inner, record_fields);
            }
            ast::TypeExpr::Named { .. } | ast::TypeExpr::Var { .. } => {}
        }
    }

    fn collect_anon_records_from_expr(
        expr: &ast::Expr,
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        match &expr.kind {
            ast::ExprKind::AnonRecordCreate { fields } => {
                let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                let tag = ast::anon_record_tag(&names);
                let mut sorted_names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                sorted_names.sort();
                record_fields.entry(tag).or_insert(sorted_names);
                for (_, _, e) in fields {
                    Self::collect_anon_records_from_expr(e, record_fields);
                }
            }
            ast::ExprKind::RecordCreate { fields, .. } => {
                for (_, _, e) in fields {
                    Self::collect_anon_records_from_expr(e, record_fields);
                }
            }
            ast::ExprKind::RecordUpdate { record, fields, .. } => {
                Self::collect_anon_records_from_expr(record, record_fields);
                for (_, _, e) in fields {
                    Self::collect_anon_records_from_expr(e, record_fields);
                }
            }
            ast::ExprKind::Block { stmts, .. } => {
                for stmt in stmts {
                    match &stmt.node {
                        ast::Stmt::Expr(e) | ast::Stmt::Let { value: e, .. } => {
                            Self::collect_anon_records_from_expr(e, record_fields);
                        }
                        ast::Stmt::LetFun { body, .. } => {
                            Self::collect_anon_records_from_expr(body, record_fields);
                        }
                    }
                }
            }
            ast::ExprKind::App { func, arg, .. } => {
                Self::collect_anon_records_from_expr(func, record_fields);
                Self::collect_anon_records_from_expr(arg, record_fields);
            }
            ast::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                Self::collect_anon_records_from_expr(cond, record_fields);
                Self::collect_anon_records_from_expr(then_branch, record_fields);
                Self::collect_anon_records_from_expr(else_branch, record_fields);
            }
            ast::ExprKind::Case {
                scrutinee, arms, ..
            } => {
                Self::collect_anon_records_from_expr(scrutinee, record_fields);
                for arm in arms {
                    Self::collect_anon_records_from_expr(&arm.node.body, record_fields);
                }
            }
            ast::ExprKind::Lambda { body, .. } => {
                Self::collect_anon_records_from_expr(body, record_fields);
            }
            ast::ExprKind::FieldAccess { expr, .. } => {
                Self::collect_anon_records_from_expr(expr, record_fields);
            }
            ast::ExprKind::Tuple { elements, .. } => {
                for e in elements {
                    Self::collect_anon_records_from_expr(e, record_fields);
                }
            }
            ast::ExprKind::BinOp { left, right, .. } => {
                Self::collect_anon_records_from_expr(left, record_fields);
                Self::collect_anon_records_from_expr(right, record_fields);
            }
            _ => {}
        }
    }

    /// Register qualified constructor atoms for private constructors from
    /// handler source modules. These are needed when lowering imported handler
    /// bodies that reference private constructors from their defining module.
    fn register_handler_source_module_ctors(&mut self) {
        let source_modules: Vec<String> = self
            .handler_defs
            .values()
            .filter_map(|info| info.source_module.as_ref())
            .filter(|m| m.as_str() != self.current_source_module)
            .cloned()
            .collect::<std::collections::HashSet<_>>()
            .into_iter()
            .collect();

        for source_module in &source_modules {
            let erlang_mod = Self::module_name_to_erlang(source_module);
            if let Some(semantics) = self.ctx.module_semantics(source_module) {
                for decl in semantics.elaborated {
                    match decl {
                        crate::ast::Decl::TypeDef { variants, .. } => {
                            for variant in variants {
                                let ctor = &variant.node.name;
                                let qualified = format!("{}.{}", source_module, ctor);
                                if !self.constructor_atoms.contains_key(&qualified) {
                                    self.constructor_atoms.insert(
                                        qualified,
                                        format!("{}_{}", erlang_mod, ctor),
                                    );
                                }
                            }
                        }
                        crate::ast::Decl::RecordDef { name, .. } => {
                            let qualified = format!("{}.{}", source_module, name);
                            if !self.constructor_atoms.contains_key(&qualified) {
                                self.constructor_atoms.insert(
                                    qualified,
                                    format!("{}_{}", erlang_mod, name),
                                );
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}
