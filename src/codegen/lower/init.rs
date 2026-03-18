/// Module initialization: registers effect definitions, handler definitions,
/// function metadata, imports, and type constructors from the program's
/// declarations and imported module codegen info.
use crate::ast::{self, Decl};
use std::collections::HashMap;

use super::util::{self, collect_type_effects};
use super::{EffectInfo, FunInfo, HandlerInfo, Lowerer};

/// Staging area for FunAnnotation data consumed by FunBinding.
/// Keeps fun_info free of half-initialized entries.
pub(super) struct PendingAnnotation {
    pub effects: Vec<String>,
    pub param_absorbed_effects: HashMap<usize, Vec<String>>,
}

impl<'a> Lowerer<'a> {
    /// Initialize the lowerer's lookup tables from program declarations and
    /// imported module codegen info. Returns pending annotations to be consumed
    /// during function grouping.
    pub(super) fn init_module(
        &mut self,
        module_name: &str,
        program: &ast::Program,
    ) -> HashMap<String, PendingAnnotation> {
        let mut pending_annotations: HashMap<String, PendingAnnotation> = HashMap::new();

        // Collect record field orders, effect definitions, handler definitions,
        // and function effect requirements.
        for decl in program {
            match decl {
                Decl::RecordDef { name, fields, .. } => {
                    let field_names = fields.iter().map(|(n, _)| n.clone()).collect();
                    self.record_fields.insert(name.clone(), field_names);
                    // Register record as a constructor for atom mangling
                    self.constructor_modules
                        .insert(name.clone(), module_name.to_string());
                }
                Decl::TypeDef { name, variants, .. } => {
                    // Register all constructors for atom mangling
                    for variant in variants {
                        self.constructor_modules
                            .insert(variant.name.clone(), module_name.to_string());
                    }
                    let _ = name; // type name not needed here
                }
                Decl::EffectDef {
                    name, operations, ..
                } => {
                    let mut ops = HashMap::new();
                    for op in operations {
                        ops.insert(op.name.clone(), op.params.len());
                        self.op_to_effect.insert(op.name.clone(), name.clone());
                    }
                    self.effect_defs.insert(name.clone(), EffectInfo { ops });
                }
                Decl::HandlerDef {
                    name,
                    effects,
                    arms,
                    return_clause,
                    ..
                } => {
                    self.handler_defs.insert(
                        name.clone(),
                        HandlerInfo {
                            effects: effects.iter().map(|e| e.name.clone()).collect(),
                            arms: arms.clone(),
                            return_clause: return_clause.clone(),
                            source_module: Some(module_name.to_string()),
                        },
                    );
                }
                Decl::FunAnnotation {
                    public,
                    name,
                    effects,
                    params,
                    ..
                } => {
                    if *public {
                        self.pub_names.insert(name.clone());
                    }
                    let mut sorted_effects = Vec::new();
                    if !effects.is_empty() {
                        sorted_effects = effects.iter().map(|e| e.name.clone()).collect();
                        sorted_effects.sort();
                    }
                    // Extract EffArrow info from parameter types
                    let mut param_effs: HashMap<usize, Vec<String>> = HashMap::new();
                    for (i, (_param_name, type_expr)) in params.iter().enumerate() {
                        let effs = collect_type_effects(type_expr);
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
                Decl::ExternalFun {
                    public,
                    name,
                    module: erl_module,
                    func: erl_func,
                    params,
                    effects,
                    ..
                } => {
                    if *public {
                        self.pub_names.insert(name.clone());
                    }
                    let real_arity = params.len();
                    self.external_funs.insert(
                        name.clone(),
                        (erl_module.clone(), erl_func.clone(), real_arity),
                    );
                    let mut sorted_effects = Vec::new();
                    if !effects.is_empty() {
                        sorted_effects = effects.iter().map(|e| e.name.clone()).collect();
                        sorted_effects.sort();
                    }
                    let expanded_arity = self.expanded_arity(real_arity, &sorted_effects);
                    self.fun_info.insert(
                        name.clone(),
                        FunInfo {
                            arity: expanded_arity,
                            effects: sorted_effects,
                            param_absorbed_effects: HashMap::new(),
                            import_origin: None,
                        },
                    );
                }
                _ => {}
            }
        }

        // Register trait impl dicts and constructors from all modules in codegen_info
        // so they're available even when not explicitly imported by user code. The
        // elaborator resolves dicts from all tc_codegen_info entries (not just direct
        // imports), so the lowerer must match that scope.
        for (mod_name, info) in self.codegen_info {
            let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
            let erlang_name = util::module_name_to_erlang(&mod_path);
            for d in &info.trait_impl_dicts {
                self.fun_info.entry(d.dict_name.clone()).or_insert(FunInfo {
                    arity: d.arity,
                    effects: Vec::new(),
                    param_absorbed_effects: HashMap::new(),
                    import_origin: Some((erlang_name.clone(), d.dict_name.clone())),
                });
            }
            if mod_name.starts_with("Std.") {
                // Register the prelude's module alias so qualified calls like
                // `List.map` resolve to `std_list:map` instead of `list:map`.
                let alias = mod_path.last().unwrap().clone();
                self.module_aliases
                    .entry(alias)
                    .or_insert_with(|| erlang_name.clone());

                // Register Std effect definitions so expanded_arity can look up op counts.
                for eff_def in &info.effect_defs {
                    let mut ops_map = HashMap::new();
                    for op in &eff_def.ops {
                        ops_map.insert(op.name.clone(), op.param_count);
                        self.op_to_effect
                            .entry(op.name.clone())
                            .or_insert_with(|| eff_def.name.clone());
                    }
                    self.effect_defs
                        .entry(eff_def.name.clone())
                        .or_insert(EffectInfo { ops: ops_map });
                }

                // Register Std exports so prelude-imported functions (e.g. fst, snd)
                // resolve to cross-module calls without an explicit import in user code.
                for (name, scheme) in &info.exports {
                    let (base_arity, mut effects) =
                        util::arity_and_effects_from_type(&scheme.ty);
                    // Supplement with annotation-derived effects (needs clause)
                    if let Some((_, ann_effs)) =
                        info.fun_effects.iter().find(|(n, _)| n == name)
                    {
                        for eff in ann_effs {
                            if !effects.contains(eff) {
                                effects.push(eff.clone());
                            }
                        }
                        effects.sort();
                    }
                    // Count dict params from trait constraints (excluding operator-dispatched traits)
                    let dict_param_count = util::dict_param_count(&scheme.constraints);
                    let expanded_arity =
                        self.expanded_arity(base_arity, &effects) + dict_param_count;
                    let param_effs = util::param_absorbed_effects_from_type(&scheme.ty);
                    // Register unqualified form
                    self.fun_info.entry(name.clone()).or_insert(FunInfo {
                        arity: expanded_arity,
                        effects: effects.clone(),
                        param_absorbed_effects: param_effs,
                        import_origin: Some((erlang_name.clone(), name.clone())),
                    });
                    // Register qualified (alias.name) form
                    let qualified = format!("{}.{}", mod_path.last().unwrap(), name);
                    self.fun_info.entry(qualified).or_insert(FunInfo {
                        arity: expanded_arity,
                        effects,
                        param_absorbed_effects: HashMap::new(),
                        import_origin: None,
                    });
                }
                for (_type_name, ctors) in &info.type_constructors {
                    for ctor in ctors {
                        self.constructor_modules
                            .insert(ctor.clone(), erlang_name.clone());
                    }
                }
                // Register Std handler bodies from elaborated programs
                if let Some(elab_program) = self.elaborated_modules.get(mod_name) {
                    for decl in elab_program {
                        if let Decl::HandlerDef {
                            name,
                            effects,
                            arms,
                            return_clause,
                            ..
                        } = decl
                        {
                            self.handler_defs.entry(name.clone()).or_insert(HandlerInfo {
                                effects: effects.iter().map(|e| e.name.clone()).collect(),
                                arms: arms.clone(),
                                return_clause: return_clause.clone(),
                                source_module: Some(mod_name.clone()),
                            });
                        }
                    }
                }
            }
        }

        // Pre-populate lookup tables from imported modules' codegen info.
        for decl in program {
            if let Decl::Import {
                module_path,
                alias,
                exposing,
                ..
            } = decl
            {
                let module_name = module_path.join(".");
                let prefix = alias
                    .as_deref()
                    .map(|a| a.to_string())
                    .unwrap_or_else(|| module_path.last().unwrap().to_string());
                let erlang_name = util::module_name_to_erlang(module_path);
                self.module_aliases
                    .insert(prefix.clone(), erlang_name.clone());

                if let Some(info) = self.codegen_info.get(&module_name) {
                    // Build a set of exported names for checking exposing list
                    let exported_names: std::collections::HashSet<&str> =
                        info.exports.iter().map(|(n, _)| n.as_str()).collect();

                    // Register imported functions with qualified keys
                    for (name, scheme) in &info.exports {
                        let (base_arity, mut effects) =
                            util::arity_and_effects_from_type(&scheme.ty);
                        // Supplement with annotation-derived effects (needs clause)
                        if let Some((_, ann_effs)) =
                            info.fun_effects.iter().find(|(n, _)| n == name)
                        {
                            for eff in ann_effs {
                                if !effects.contains(eff) {
                                    effects.push(eff.clone());
                                }
                            }
                            effects.sort();
                        }
                        let dict_param_count = util::dict_param_count(&scheme.constraints);
                        let expanded_arity =
                            self.expanded_arity(base_arity, &effects) + dict_param_count;
                        let param_effs = util::param_absorbed_effects_from_type(&scheme.ty);
                        let qualified = format!("{}.{}", prefix, name);
                        self.fun_info.insert(
                            qualified,
                            FunInfo {
                                arity: expanded_arity,
                                effects: effects.clone(),
                                param_absorbed_effects: param_effs.clone(),
                                import_origin: None,
                            },
                        );

                        // Register exposed (unqualified) names
                        if let Some(exposed) = exposing
                            && exposed.iter().any(|e| e == name)
                            && exported_names.contains(name.as_str())
                        {
                            self.fun_info.insert(
                                name.clone(),
                                FunInfo {
                                    arity: expanded_arity,
                                    effects,
                                    param_absorbed_effects: param_effs,
                                    import_origin: Some((erlang_name.clone(), name.clone())),
                                },
                            );
                        }
                    }

                    // Register imported effect definitions
                    for eff_def in &info.effect_defs {
                        let mut ops_map = HashMap::new();
                        for op in &eff_def.ops {
                            ops_map.insert(op.name.clone(), op.param_count);
                            self.op_to_effect
                                .insert(op.name.clone(), eff_def.name.clone());
                        }
                        self.effect_defs
                            .insert(eff_def.name.clone(), EffectInfo { ops: ops_map });
                    }
                    // Register imported record field orders
                    for (rec_name, fields) in &info.record_fields {
                        self.record_fields.insert(rec_name.clone(), fields.clone());
                    }
                    // Register imported constructors for atom mangling
                    for (_type_name, ctors) in &info.type_constructors {
                        for ctor in ctors {
                            self.constructor_modules
                                .insert(ctor.clone(), erlang_name.clone());
                        }
                    }
                    // Register imported trait impl dicts for cross-module calls
                    for d in &info.trait_impl_dicts {
                        self.fun_info.insert(
                            d.dict_name.clone(),
                            FunInfo {
                                arity: d.arity,
                                effects: Vec::new(),
                                param_absorbed_effects: HashMap::new(),
                                import_origin: Some((erlang_name.clone(), d.dict_name.clone())),
                            },
                        );
                    }
                    // Register imported handler bodies from elaborated programs
                    if let Some(elab_program) = self.elaborated_modules.get(&module_name) {
                        for decl in elab_program {
                            if let Decl::HandlerDef {
                                name,
                                effects,
                                arms,
                                return_clause,
                                ..
                            } = decl
                            {
                                self.handler_defs.entry(name.clone()).or_insert(HandlerInfo {
                                    effects: effects.iter().map(|e| e.name.clone()).collect(),
                                    arms: arms.clone(),
                                    return_clause: return_clause.clone(),
                                    source_module: Some(module_name.clone()),
                                });
                            }
                        }
                    }
                }
            }
        }

        pending_annotations
    }
}
