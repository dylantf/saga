/// Module initialization: registers effect definitions, handler definitions,
/// function metadata, imports, and type constructors from the program's
/// declarations and imported module codegen info.
use crate::ast::{self, Decl};
use crate::codegen::runtime_shape::{CpsShape, RuntimeFunctionShape};
use std::collections::{BTreeSet, HashMap, HashSet};

use super::util;
use super::{EffectInfo, FunInfo, HandlerInfo, Lowerer};

fn split_canonical_fun(canonical: &str) -> Option<(&str, &str)> {
    canonical.rsplit_once('.')
}

fn export_origin<'a>(
    exporting_module: &'a str,
    info: &'a crate::typechecker::ModuleCodegenInfo,
    surface_name: &'a str,
) -> (&'a str, &'a str) {
    info.export_origins
        .iter()
        .find(|(surface, _)| surface == surface_name)
        .and_then(|(_, origin)| split_canonical_fun(origin))
        .unwrap_or((exporting_module, surface_name))
}

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

    fn handler_factory_body(expr: &ast::Expr) -> Option<&ast::HandlerBody> {
        match &expr.kind {
            ast::ExprKind::HandlerExpr { body } => Some(body),
            ast::ExprKind::Ascription { expr, .. } => Self::handler_factory_body(expr),
            ast::ExprKind::Block { stmts, .. } if stmts.len() == 1 => match &stmts[0].node {
                ast::Stmt::Expr(expr) => Self::handler_factory_body(expr),
                _ => None,
            },
            _ => None,
        }
    }

    fn handler_factory_params(params: &[ast::Pat]) -> Option<Vec<String>> {
        params
            .iter()
            .map(|param| match param {
                ast::Pat::Var { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    fn register_handler_factory_defs(&mut self, program: &ast::Program, source_module_name: &str) {
        for decl in program {
            let Decl::FunBinding {
                name,
                params,
                guard,
                body,
                ..
            } = decl
            else {
                continue;
            };
            if guard.is_some() {
                continue;
            }
            let Some(handler_body) = Self::handler_factory_body(body) else {
                continue;
            };
            let Some(param_names) = Self::handler_factory_params(params) else {
                continue;
            };

            let info = super::HandlerFactoryInfo {
                params: param_names,
                body: handler_body.clone(),
                source_module: Some(source_module_name.to_string()),
            };
            self.handler_factory_defs.insert(name.clone(), info.clone());
            self.handler_factory_defs
                .insert(format!("{}.{}", source_module_name, name), info);
        }
    }

    fn register_local_helper_defs(&mut self, program: &ast::Program, source_module_name: &str) {
        let mut seen: HashSet<String> = HashSet::new();
        let mut duplicate_names: HashSet<String> = HashSet::new();
        let mut helpers: HashMap<String, super::LocalHelperInfo> = HashMap::new();

        for decl in program {
            let Decl::FunBinding {
                name,
                params,
                guard,
                body,
                ..
            } = decl
            else {
                continue;
            };

            if !seen.insert(name.clone()) {
                duplicate_names.insert(name.clone());
                helpers.remove(name);
                helpers.remove(&format!("{}.{}", source_module_name, name));
                continue;
            }
            if guard.is_some() {
                continue;
            }

            let info = super::LocalHelperInfo {
                params: params.clone(),
                body: body.clone(),
                source_module: source_module_name.to_string(),
            };
            helpers.insert(name.clone(), info.clone());
            helpers.insert(format!("{}.{}", source_module_name, name), info);
        }

        for name in duplicate_names {
            helpers.remove(&name);
            helpers.remove(&format!("{}.{}", source_module_name, name));
        }

        self.local_helper_defs.extend(helpers);
    }

    fn register_imported_public_helper_facts(&mut self) {
        for (module_name, module_semantics) in self.ctx.modules_semantics() {
            if module_name == self.current_source_module {
                continue;
            }
            let exported_names: HashSet<&str> = module_semantics
                .codegen_info
                .exports
                .iter()
                .map(|(name, _)| name.as_str())
                .collect();
            for (name, fact) in &module_semantics.optimization.public_helpers {
                if !name.contains('.') {
                    continue;
                }
                let Some(bare_name) = name.rsplit('.').next() else {
                    continue;
                };
                if !exported_names.contains(bare_name) {
                    continue;
                }
                self.local_helper_defs
                    .entry(name.clone())
                    .or_insert_with(|| super::LocalHelperInfo {
                        params: fact.params.clone(),
                        body: fact.body.clone(),
                        source_module: fact.source_module.clone(),
                    });
            }
        }
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
                    effect_names
                        .extend(self.resolved_type_effects_for_module(module_name, field_ty));
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
            if let Decl::EffectDef { name, .. } | Decl::NewEffect { name, .. } = decl {
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
            // The active import scope is authoritative, especially for
            // re-exported handlers: the same bare surface name may have been
            // pre-seeded above from an arbitrary compiled module, while the
            // scope map retains the true origin declaration.
            handler_canonical.insert(user_visible.clone(), canonical.clone());
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
                                let effs =
                                    self.resolved_type_effects_for_module(source_module_name, ty);
                                if effs.is_empty() {
                                    None
                                } else {
                                    let mut sorted: Vec<String> = effs.into_iter().collect();
                                    sorted.sort();
                                    Some((idx, sorted))
                                }
                            })
                            .collect();
                        let param_open_rows = self
                            .check_result
                            .effects
                            .get(&canonical_effect)
                            .or_else(|| self.check_result.effects.get(name))
                            .and_then(|info| info.ops.iter().find(|sig| sig.name == op.node.name))
                            .map(|sig| {
                                sig.params
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(idx, (_, ty))| {
                                        util::has_open_effect_row(ty).then_some(idx)
                                    })
                                    .collect()
                            })
                            .unwrap_or_default();
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
                                param_open_rows,
                                dict_param_names: crate::ast::op_dict_param_names(
                                    &op.node.where_clause,
                                ),
                            },
                        );
                    }
                    self.effect_defs
                        .insert(canonical_effect, EffectInfo { ops });
                }
                Decl::NewEffect { name, .. } => {
                    let canonical_effect = format!("{}.{}", source_module_name, name);
                    let effect_info = self
                        .check_result
                        .effects
                        .get(&canonical_effect)
                        .or_else(|| self.check_result.effects.get(name))
                        .unwrap_or_else(|| panic!("missing neweffect info for {canonical_effect}"));
                    let is_unit = |ty: &crate::typechecker::Type| {
                        matches!(
                            ty,
                            crate::typechecker::Type::Con(n, args)
                                if args.is_empty() && crate::typechecker::canonicalize_type_name(n)
                                    == crate::typechecker::canonicalize_type_name("Unit")
                        )
                    };
                    let ops = effect_info
                        .ops
                        .iter()
                        .map(|op| {
                            let runtime_param_positions: Vec<usize> = op
                                .params
                                .iter()
                                .enumerate()
                                .filter_map(|(idx, (_, ty))| (!is_unit(ty)).then_some(idx))
                                .collect();
                            let param_absorbed_effects = op
                                .params
                                .iter()
                                .enumerate()
                                .filter_map(|(idx, (_, ty))| {
                                    let mut effects: Vec<String> =
                                        crate::typechecker::effects_from_type(ty)
                                            .into_iter()
                                            .collect();
                                    effects.sort();
                                    (!effects.is_empty()).then_some((idx, effects))
                                })
                                .collect();
                            let param_open_rows = op
                                .params
                                .iter()
                                .enumerate()
                                .filter_map(|(idx, (_, ty))| {
                                    util::has_open_effect_row(ty).then_some(idx)
                                })
                                .collect();
                            (
                                op.name.clone(),
                                super::EffectOpInfo {
                                    source_param_count: op.params.len(),
                                    runtime_param_count: runtime_param_positions.len(),
                                    runtime_param_positions,
                                    param_absorbed_effects,
                                    param_open_rows,
                                    dict_param_names: Vec::new(),
                                },
                            )
                        })
                        .collect();
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
                            source_module: Some(source_module_name.to_string()),
                            captures: Vec::new(),
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
                        let is_open_row = self
                            .check_result
                            .env
                            .get(name)
                            .map(|scheme| {
                                util::has_open_effect_row(&self.check_result.sub.apply(&scheme.ty))
                            })
                            .unwrap_or(false);
                        let expanded_arity =
                            self.expanded_arity_for_row(real_arity, &sorted_effects, is_open_row);
                        self.fun_info.insert(
                            name.clone(),
                            FunInfo {
                                arity: expanded_arity,
                                effects: sorted_effects,
                                is_open_row,
                                param_absorbed_effects: HashMap::new(),
                                param_types: Vec::new(),
                                dict_param_count: self
                                    .check_result
                                    .env
                                    .get(name)
                                    .map(|scheme| util::dict_param_count(&scheme.constraints))
                                    .unwrap_or(0),
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
                                    let effs = self.resolved_type_effects_for_module(
                                        source_module_name,
                                        type_expr,
                                    );
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
                                param_open_rows: op.param_open_rows.clone(),
                                dict_param_names: op.dict_param_names.clone(),
                            },
                        );
                    }
                    self.effect_defs
                        .entry(eff_def.name.clone())
                        .or_insert(EffectInfo { ops: ops_map });
                }

                for (name, scheme) in &info.exports {
                    let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
                    let effects = self.canonicalize_effects(effects);
                    let shape = RuntimeFunctionShape::from_type(&scheme.ty, |effects| {
                        self.canonicalize_effects(effects)
                    });
                    let is_open_row = shape.cps_shape().is_some_and(|shape| shape.is_open_row);
                    let dict_param_count = util::dict_param_count(&scheme.constraints);
                    let expanded_arity = shape.expanded_arity(base_arity) + dict_param_count;
                    let param_absorbed = util::param_absorbed_effects_from_type(&scheme.ty);
                    let param_absorbed: HashMap<usize, Vec<String>> = param_absorbed
                        .into_iter()
                        .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                        .collect();
                    let fi = FunInfo {
                        arity: expanded_arity,
                        effects,
                        is_open_row,
                        param_absorbed_effects: param_absorbed,
                        param_types: util::param_types_from_type(&scheme.ty),
                        dict_param_count,
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
                                    captures: Vec::new(),
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
                        param_open_rows: op.param_open_rows.clone(),
                        dict_param_names: op.dict_param_names.clone(),
                    },
                );
            }
            self.effect_defs
                .insert(eff_def.name.clone(), EffectInfo { ops: ops_map });
        }
    }

    fn register_imported_exports(
        &mut self,
        module_name: &str,
        prefix: &str,
        exposing: Option<&crate::ast::Exposing>,
        info: &crate::typechecker::ModuleCodegenInfo,
    ) {
        let exposed_surface = |name: &str| -> Option<String> {
            match exposing {
                None => None,
                Some(e) => e.surface_name_for_origin(name),
            }
        };
        let exported_names: std::collections::HashSet<&str> =
            info.exports.iter().map(|(n, _)| n.as_str()).collect();

        for (name, scheme) in &info.exports {
            let (origin_mod, origin_name) = export_origin(module_name, info, name);
            let origin_info = self
                .ctx
                .module_semantics(origin_mod)
                .map(|module| module.codegen_info)
                .unwrap_or(info);
            let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
            let mut effects = self.canonicalize_effects(effects);
            if let Some((_, ann_effs)) = origin_info
                .fun_effects
                .iter()
                .find(|(fun_name, _)| fun_name == origin_name)
            {
                for eff in ann_effs {
                    if !effects.contains(eff) {
                        effects.push(eff.clone());
                    }
                }
            }
            let shape = RuntimeFunctionShape::from_type(&scheme.ty, |effects| {
                self.canonicalize_effects(effects)
            });
            let is_open_row = shape.cps_shape().is_some_and(|shape| shape.is_open_row);
            let dict_param_count = util::dict_param_count(&scheme.constraints);
            let expanded_arity = shape.expanded_arity(base_arity) + dict_param_count;
            let param_effs = util::param_absorbed_effects_from_type(&scheme.ty);
            let param_effs: HashMap<usize, Vec<String>> = param_effs
                .into_iter()
                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                .collect();

            let alias_qualified = format!("{}.{}", prefix, name);
            let fi = FunInfo {
                arity: expanded_arity,
                effects: effects.clone(),
                is_open_row,
                param_absorbed_effects: param_effs.clone(),
                param_types: util::param_types_from_type(&scheme.ty),
                dict_param_count,
            };
            self.fun_info.insert(alias_qualified, fi.clone());
            let canonical = format!("{}.{}", origin_mod, origin_name);
            self.fun_info.entry(canonical).or_insert(fi);

            if let Some(surface) = exposed_surface(name)
                && exported_names.iter().any(|exported| *exported == name)
            {
                self.fun_info.entry(surface).or_insert(FunInfo {
                    arity: expanded_arity,
                    effects,
                    is_open_row,
                    param_absorbed_effects: param_effs,
                    param_types: util::param_types_from_type(&scheme.ty),
                    dict_param_count,
                });
            }
        }
    }

    /// Register record field layouts for every compiled module's records
    /// (public and private), keyed by `<module>.<Record>`. Uses `or_insert` so
    /// any more-specific local/imported registration already present wins.
    fn register_all_module_records(&mut self) {
        for (mod_name, module_semantics) in self.ctx.modules_semantics() {
            for decl in module_semantics.elaborated {
                if let Decl::RecordDef { name, fields, .. } = decl {
                    let canonical = format!("{}.{}", mod_name, name);
                    self.record_fields
                        .entry(canonical)
                        .or_insert_with(|| fields.iter().map(|a| a.node.0.clone()).collect());
                }
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

        for (_, scheme) in &info.exports {
            Self::collect_anon_records_from_type(&scheme.ty, &mut self.record_fields);
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
                            captures: Vec::new(),
                        });
                }
                Decl::FunSignature { .. } => {
                    // External function resolution handled by resolve.rs
                }
                _ => {}
            }
        }
    }

    fn register_reexport_origin_modules(
        &mut self,
        exporting_module: &str,
        info: &crate::typechecker::ModuleCodegenInfo,
    ) {
        let mut origin_modules = HashSet::new();
        for (_, origin) in info
            .export_origins
            .iter()
            .chain(info.effect_origins.iter())
            .chain(info.handler_origins.iter())
        {
            if let Some((origin_module, _)) = split_canonical_fun(origin)
                && origin_module != exporting_module
            {
                origin_modules.insert(origin_module.to_string());
            }
        }

        for origin_module in origin_modules {
            let Some((origin_info, origin_program)) =
                self.ctx.module_semantics(&origin_module).map(|semantics| {
                    (
                        (*semantics.codegen_info).clone(),
                        (*semantics.elaborated).clone(),
                    )
                })
            else {
                continue;
            };
            self.register_imported_effect_defs(&origin_info);
            self.register_imported_records_and_dicts(&origin_module, &origin_info);
            self.register_imported_handler_defs(&origin_module, &origin_program);
        }
    }

    fn register_imported_module_local_funs(&mut self, module_name: &str, program: &ast::Program) {
        let (_, source_module_name) = Self::source_module_info(program, module_name);

        // Public schemes for `source_module_name`'s own functions. Used to shape
        // these imported/foreign funs from their *origin* module's type, not from
        // `self.check_result.env` (the module currently being lowered). Looking up
        // the bare `name` in the current env is wrong: if the importing module
        // defines a function that shares this name, we'd pick up the wrong scheme
        // and, e.g., miss the CPS arity expansion for an effectful callee — see
        // the aliased effect re-export bug.
        let origin_schemes: HashMap<String, crate::typechecker::Scheme> = self
            .ctx
            .module_semantics(&source_module_name)
            .map(|semantics| semantics.codegen_info.exports.iter().cloned().collect())
            .unwrap_or_default();

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
                        let mut sorted: Vec<String> = effs.into_iter().collect();
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

        self.register_handler_factory_defs(program, &source_module_name);

        for decl in program {
            if let Decl::FunBinding {
                name, params, body, ..
            } = decl
            {
                let PendingAnnotation {
                    effects,
                    param_absorbed_effects,
                } = pending_annotations
                    .remove(name.as_str())
                    .unwrap_or(PendingAnnotation {
                        effects: Vec::new(),
                        param_absorbed_effects: HashMap::new(),
                    });
                let origin_scheme = origin_schemes.get(name);
                let mut base_arity = params.len() + count_lambda_params(body);
                // Use annotation arity for eta-reduced functions (same fix as mod.rs)
                if let Some(scheme) = origin_scheme {
                    let declared = super::util::arity_and_effects_from_type(&scheme.ty).0;
                    if declared > base_arity {
                        base_arity = declared;
                    }
                }
                let shape = origin_scheme
                    .map(|scheme| {
                        RuntimeFunctionShape::from_type(&scheme.ty, |effects| {
                            self.canonicalize_effects(effects)
                        })
                    })
                    .unwrap_or_else(|| {
                        if effects.is_empty() {
                            RuntimeFunctionShape::Pure
                        } else {
                            RuntimeFunctionShape::Cps(CpsShape {
                                static_effects: effects.clone(),
                                is_open_row: false,
                            })
                        }
                    });
                let is_open_row = shape.cps_shape().is_some_and(|shape| shape.is_open_row);
                let arity = shape.expanded_arity(base_arity);
                let param_types = origin_scheme
                    .map(|scheme| util::param_types_from_type(&scheme.ty))
                    .unwrap_or_default();
                let canonical = format!("{}.{}", source_module_name, name);
                self.fun_info.entry(canonical).or_insert(FunInfo {
                    arity,
                    effects,
                    is_open_row,
                    param_absorbed_effects,
                    param_types,
                    dict_param_count: origin_scheme
                        .map(|scheme| util::dict_param_count(&scheme.constraints))
                        .unwrap_or(0),
                });
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
        self.register_local_helper_defs(program, &source_module_name);
        self.register_imported_public_helper_facts();
        self.register_handler_factory_defs(program, &source_module_name);
        self.register_local_module_decls(
            program,
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
        // Register record layouts for *every* compiled module (public and
        // private), not just directly-imported ones: the cross-module generic
        // fold can inline a producer body that accesses a record from a module
        // this one only depends on transitively (e.g. a private `Options`), and
        // computing the field's tuple index needs that layout.
        self.register_all_module_records();

        // Register anonymous record types found in record field types and expressions.
        Self::collect_anon_records_from_program(program, &mut self.record_fields);

        // Pre-register canonical constructor atoms for every compiled module.
        // Generic fold and imported handlers can inline producer code that
        // references private constructors; canonical entries preserve the
        // producer module without any bare-name collision path.
        self.register_all_module_ctors();

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
        self.register_imported_exports(&module_name, &prefix, exposing.as_ref(), info);
        self.register_imported_records_and_dicts(&module_name, info);
        self.register_imported_handler_defs(&module_name, module_semantics.elaborated);
        self.register_reexport_origin_modules(&module_name, info);
    }

    /// Walk the AST to find anonymous record types and register them in record_fields.
    fn collect_anon_records_from_program(
        program: &[Decl],
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        for decl in program {
            if let Decl::TypeAlias { body, .. } = decl {
                Self::collect_anon_records_from_type_expr(body, record_fields);
            }
            if let Decl::RecordDef { fields, .. } = decl {
                for a in fields {
                    let (_, type_expr) = &a.node;
                    Self::collect_anon_records_from_type_expr(type_expr, record_fields);
                }
            }
            if let Decl::FunSignature {
                params,
                return_type,
                ..
            } = decl
            {
                for (_, type_expr) in params {
                    Self::collect_anon_records_from_type_expr(type_expr, record_fields);
                }
                Self::collect_anon_records_from_type_expr(return_type, record_fields);
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

    fn collect_anon_records_from_type(
        ty: &crate::typechecker::Type,
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        match ty {
            crate::typechecker::Type::Record(fields) => {
                let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
                let tag = ast::anon_record_tag(&names);
                let mut sorted_names: Vec<String> =
                    names.iter().map(|name| name.to_string()).collect();
                sorted_names.sort();
                record_fields.entry(tag).or_insert(sorted_names);
                for (_, field_ty) in fields {
                    Self::collect_anon_records_from_type(field_ty, record_fields);
                }
            }
            crate::typechecker::Type::Fun(param, ret, row) => {
                Self::collect_anon_records_from_type(param, record_fields);
                Self::collect_anon_records_from_type(ret, record_fields);
                for effect in &row.effects {
                    for arg in &effect.args {
                        Self::collect_anon_records_from_type(arg, record_fields);
                    }
                }
                for tail in &row.tails {
                    Self::collect_anon_records_from_type(tail, record_fields);
                }
            }
            crate::typechecker::Type::Con(_, args) => {
                for arg in args {
                    Self::collect_anon_records_from_type(arg, record_fields);
                }
            }
            crate::typechecker::Type::Var(_) | crate::typechecker::Type::Error => {}
        }
    }

    fn collect_anon_records_from_expr(
        expr: &ast::Expr,
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        if let ast::ExprKind::AnonRecordCreate { fields } = &expr.kind {
            let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
            let tag = ast::anon_record_tag(&names);
            let mut sorted_names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
            sorted_names.sort();
            record_fields.entry(tag).or_insert(sorted_names);
        }
        // Recurse into every child expression. Using the shared exhaustive
        // walker (rather than a hand-rolled match) ensures anon records nested
        // under any expression form — `with`/handler bodies, `do`, `receive`,
        // pipes, comprehensions, etc. — are registered. A missing arm here
        // silently drops the field layout and crashes lowering at the eventual
        // `.field` access.
        crate::codegen::optimize::walk_expr(expr, &mut |child| {
            Self::collect_anon_records_from_expr(child, record_fields);
        });
    }

    fn register_all_module_ctors(&mut self) {
        let modules: Vec<String> = self
            .ctx
            .modules_semantics()
            .map(|(source_module, _)| source_module.to_string())
            .collect();

        for source_module in &modules {
            let erlang_mod = Self::module_name_to_erlang(source_module);
            if let Some(semantics) = self.ctx.module_semantics(source_module) {
                for decl in semantics.elaborated {
                    match decl {
                        crate::ast::Decl::TypeDef { variants, .. } => {
                            for variant in variants {
                                let ctor = &variant.node.name;
                                let qualified = format!("{}.{}", source_module, ctor);
                                let atom = if Self::is_beam_override_ctor(ctor) {
                                    Self::beam_override_ctor_atom(ctor).to_string()
                                } else {
                                    format!("{}_{}", erlang_mod, ctor)
                                };
                                self.constructor_atoms.entry(qualified).or_insert(atom);
                            }
                        }
                        crate::ast::Decl::RecordDef { name, .. } => {
                            let qualified = format!("{}.{}", source_module, name);
                            self.constructor_atoms
                                .entry(qualified)
                                .or_insert_with(|| format!("{}_{}", erlang_mod, name));
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn is_beam_override_ctor(name: &str) -> bool {
        matches!(
            name,
            "Ok" | "Err"
                | "Just"
                | "Nothing"
                | "True"
                | "False"
                | "Normal"
                | "Shutdown"
                | "Killed"
                | "Noproc"
        )
    }

    fn beam_override_ctor_atom(name: &str) -> &'static str {
        match name {
            "Ok" => "ok",
            "Err" => "error",
            "Just" => "just",
            "Nothing" => "nothing",
            "True" => "true",
            "False" => "false",
            "Normal" => "normal",
            "Shutdown" => "shutdown",
            "Killed" => "killed",
            "Noproc" => "noproc",
            _ => unreachable!("not a BEAM override constructor: {name}"),
        }
    }
}
