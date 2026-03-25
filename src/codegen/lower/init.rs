/// Module initialization: registers effect definitions, handler definitions,
/// function metadata, imports, and type constructors from the program's
/// declarations and imported module codegen info.
use crate::ast::{self, Decl};
use std::collections::HashMap;

use super::util::{self, collect_type_effects};
use super::{EffectInfo, FunInfo, HandlerInfo, Lowerer};

/// Extract the (module, func) pair from an `@external("runtime", "module", "func")` annotation.
pub fn extract_external(annotations: &[ast::Annotation]) -> Option<(String, String)> {
    annotations.iter().find(|a| a.name == "external").and_then(|a| {
        if a.args.len() >= 3
            && let (ast::Lit::String(module), ast::Lit::String(func)) = (&a.args[1], &a.args[2])
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
                    let field_names = fields.iter().map(|a| a.node.0.clone()).collect();
                    self.record_fields.insert(name.clone(), field_names);
                    // Register record as a constructor for atom mangling
                    self.constructor_modules
                        .insert(name.clone(), module_name.to_string());
                }
                Decl::TypeDef { name, variants, .. } => {
                    // Register all constructors for atom mangling
                    for variant in variants {
                        self.constructor_modules
                            .insert(variant.node.name.clone(), module_name.to_string());
                    }
                    let _ = name; // type name not needed here
                }
                Decl::EffectDef {
                    name, operations, ..
                } => {
                    let mut ops = HashMap::new();
                    for op in operations {
                        ops.insert(op.node.name.clone(), op.node.params.len());
                        self.op_to_effect.insert(op.node.name.clone(), name.clone());
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
                            arms: arms.iter().map(|a| a.node.clone()).collect(),
                            return_clause: return_clause.clone(),
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
                    if let Some((erl_module, erl_func)) = extract_external(annotations) {
                        // @external function
                        let real_arity = params.len();
                        self.external_funs.insert(
                            name.clone(),
                            (erl_module, erl_func, real_arity),
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
                    } else {
                        // Regular function signature
                        let mut sorted_effects = Vec::new();
                        if !effects.is_empty() {
                            sorted_effects = effects.iter().map(|e| e.name.clone()).collect();
                            sorted_effects.sort();
                        }
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
                }
                _ => {}
            }
        }

        // Register trait impl dicts and constructors from all modules in codegen_info
        // so they're available even when not explicitly imported by user code. The
        // elaborator resolves dicts from all tc_codegen_info entries (not just direct
        // imports), so the lowerer must match that scope.
        for (mod_name, info) in &self.ctx.codegen_info {
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
                    .entry(alias.clone())
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
                    let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
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
                // Register Std handler bodies and external functions from elaborated programs
                if let Some(elab_program) = self.ctx.elaborated_modules.get(mod_name) {
                    for decl in elab_program {
                        match decl {
                            Decl::HandlerDef {
                                name,
                                effects,
                                arms,
                                return_clause,
                                ..
                            } => {
                                self.handler_defs
                                    .entry(name.clone())
                                    .or_insert(HandlerInfo {
                                        effects: effects.iter().map(|e| e.name.clone()).collect(),
                                        arms: arms.iter().map(|a| a.node.clone()).collect(),
                                        return_clause: return_clause.clone(),
                                        source_module: Some(mod_name.clone()),
                                    });
                            }
                            Decl::FunSignature {
                                name,
                                params,
                                annotations,
                                ..
                            } => {
                                if let Some((erl_module, erl_func)) = extract_external(annotations) {
                                    let arity = params.len();
                                    let qualified_key = format!("{}.{}", alias, name);
                                    self.external_funs.entry(qualified_key).or_insert((
                                        erl_module.clone(),
                                        erl_func.clone(),
                                        arity,
                                    ));
                                    self.external_funs.entry(name.clone()).or_insert((
                                        erl_module.clone(),
                                        erl_func.clone(),
                                        arity,
                                    ));
                                    self.fun_info.entry(name.clone()).or_insert(FunInfo {
                                        arity,
                                        effects: Vec::new(),
                                        param_absorbed_effects: HashMap::new(),
                                        import_origin: None,
                                    });
                                }
                            }
                            _ => {}
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

                if let Some(info) = self.ctx.codegen_info.get(&module_name) {
                    // Build a set of exported names for checking exposing list
                    let exported_names: std::collections::HashSet<&str> =
                        info.exports.iter().map(|(n, _)| n.as_str()).collect();

                    // Register imported functions with qualified keys
                    for (name, scheme) in &info.exports {
                        let (base_arity, effects) =
                            util::arity_and_effects_from_type(&scheme.ty);
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
                    // Register imported handler bodies and external functions from elaborated programs
                    if let Some(elab_program) = self.ctx.elaborated_modules.get(&module_name) {
                        for decl in elab_program {
                            match decl {
                                Decl::HandlerDef {
                                    name,
                                    effects,
                                    arms,
                                    return_clause,
                                    ..
                                } => {
                                    self.handler_defs
                                        .entry(name.clone())
                                        .or_insert(HandlerInfo {
                                            effects: effects
                                                .iter()
                                                .map(|e| e.name.clone())
                                                .collect(),
                                            arms: arms.iter().map(|a| a.node.clone()).collect(),
                                            return_clause: return_clause.clone(),
                                            source_module: Some(module_name.clone()),
                                        });
                                }
                                Decl::FunSignature {
                                    name,
                                    params,
                                    annotations,
                                    ..
                                } => {
                                    if let Some((erl_module, erl_func)) = extract_external(annotations) {
                                        // Register external functions so handler bodies that
                                        // reference them can resolve to the correct BEAM call.
                                        let arity = params.len();
                                        let qualified_key = format!("{}.{}", prefix, name);
                                        self.external_funs.entry(qualified_key).or_insert((
                                            erl_module.clone(),
                                            erl_func.clone(),
                                            arity,
                                        ));
                                        if exposing
                                            .as_ref()
                                            .is_some_and(|e| e.iter().any(|n| n == name))
                                        {
                                            self.external_funs.insert(
                                                name.clone(),
                                                (erl_module.clone(), erl_func.clone(), arity),
                                            );
                                        } else {
                                            self.external_funs.entry(name.clone()).or_insert((
                                                erl_module.clone(),
                                                erl_func.clone(),
                                                arity,
                                            ));
                                        }
                                        self.fun_info.entry(name.clone()).or_insert(FunInfo {
                                            arity,
                                            effects: Vec::new(),
                                            param_absorbed_effects: HashMap::new(),
                                            import_origin: None,
                                        });
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        // Register anonymous record types found in record field types and expressions.
        Self::collect_anon_records_from_program(program, &mut self.record_fields);

        pending_annotations
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
                let mut sorted_names: Vec<String> = fields.iter().map(|(n, _)| n.clone()).collect();
                sorted_names.sort();
                let tag = format!("__anon_{}", sorted_names.join("_"));
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
            ast::TypeExpr::Named { .. } | ast::TypeExpr::Var { .. } => {}
        }
    }

    fn collect_anon_records_from_expr(
        expr: &ast::Expr,
        record_fields: &mut HashMap<String, Vec<String>>,
    ) {
        match &expr.kind {
            ast::ExprKind::AnonRecordCreate { fields } => {
                let mut sorted_names: Vec<String> =
                    fields.iter().map(|(n, _, _)| n.clone()).collect();
                sorted_names.sort();
                let tag = format!("__anon_{}", sorted_names.join("_"));
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
}
