/// Module initialization: registers effect definitions, handler definitions,
/// function metadata, imports, and type constructors from the program's
/// declarations and imported module codegen info.
use crate::ast::{self, Decl};
use std::collections::HashMap;

use super::util::{self, collect_type_effects};
use super::{EffectInfo, FunInfo, HandlerInfo, Lowerer};

/// Extract the (module, func) pair from an `@external("runtime", "module", "func")` annotation.
pub fn extract_external(annotations: &[ast::Annotation]) -> Option<(String, String)> {
    annotations
        .iter()
        .find(|a| a.name == "external")
        .and_then(|a| {
            if a.args.len() >= 3
                && let (ast::Lit::String(module, _), ast::Lit::String(func, _)) = (&a.args[1], &a.args[2])
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
                }
                Decl::TypeDef { .. } => {
                    // Constructor atom mangling is handled by resolve::build_constructor_atoms
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
                    if let Some((_erl_module, _erl_func)) = extract_external(annotations) {
                        // @external function: resolution handled by resolve.rs
                        let real_arity = params.len();
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
                Decl::Val {
                    public, name, ..
                } => {
                    if *public {
                        self.pub_names.insert(name.clone());
                    }
                    self.fun_info.insert(
                        name.clone(),
                        FunInfo {
                            arity: 0,
                            ..Default::default()
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
        for (mod_name, compiled) in &self.ctx.modules {
            let info = &compiled.codegen_info;
            let mod_path: Vec<String> = mod_name.split('.').map(String::from).collect();
            let erlang_name = util::module_name_to_erlang(&mod_path);
            for d in &info.trait_impl_dicts {
                self.fun_info.entry(d.dict_name.clone()).or_insert(FunInfo {
                    arity: d.arity,
                    effects: Vec::new(),
                    param_absorbed_effects: HashMap::new(),
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

                // Register Std exports under qualified names only (e.g. List.map, Dict.to_list).
                // Unqualified names are only registered when explicitly imported via
                // exposing lists, handled by the user import processing below.
                for (name, scheme) in &info.exports {
                    let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
                    let dict_param_count = util::dict_param_count(&scheme.constraints);
                    let expanded_arity =
                        self.expanded_arity(base_arity, &effects) + dict_param_count;
                    let qualified = format!("{}.{}", mod_path.last().unwrap(), name);
                    self.fun_info.entry(qualified).or_insert(FunInfo {
                        arity: expanded_arity,
                        effects,
                        param_absorbed_effects: HashMap::new(),
                    });
                }
                // Register Std handler bodies and external functions from elaborated programs
                if let Some(elab_program) = self.ctx.elaborated_module(mod_name) {
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
                            Decl::FunSignature { .. } => {
                                // External resolution handled by resolve.rs
                            }
                            _ => {}
                        }
                    }
                }
            }
        }

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

        let Some(compiled) = self.ctx.modules.get(&module_name) else {
            return;
        };
        let info = compiled.codegen_info.clone();

        // Determine which names are exposed unqualified.
        // None = glob import (all exports), Some(list) = specific names.
        let is_exposed = |name: &str| -> bool {
            match exposing {
                None => true,
                Some(names) => names.iter().any(|n| n == name),
            }
        };

        let exported_names: std::collections::HashSet<&str> =
            info.exports.iter().map(|(n, _)| n.as_str()).collect();

        // Register imported functions
        for (name, scheme) in &info.exports {
            let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
            let dict_param_count = util::dict_param_count(&scheme.constraints);
            let expanded_arity = self.expanded_arity(base_arity, &effects) + dict_param_count;
            let param_effs = util::param_absorbed_effects_from_type(&scheme.ty);

            // Always register qualified form
            let qualified = format!("{}.{}", prefix, name);
            self.fun_info.insert(
                qualified,
                FunInfo {
                    arity: expanded_arity,
                    effects: effects.clone(),
                    param_absorbed_effects: param_effs.clone(),
                },
            );

            // Register unqualified form only for exposed names
            if is_exposed(name) && exported_names.contains(name.as_str()) {
                self.fun_info.entry(name.clone()).or_insert(FunInfo {
                    arity: expanded_arity,
                    effects,
                    param_absorbed_effects: param_effs,
                });
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

        // Register imported trait impl dicts for cross-module calls
        for d in &info.trait_impl_dicts {
            self.fun_info.entry(d.dict_name.clone()).or_insert(FunInfo {
                arity: d.arity,
                effects: Vec::new(),
                param_absorbed_effects: HashMap::new(),
            });
        }

        // Register imported handler bodies and external functions from elaborated programs
        if let Some(elab_program) = self.ctx.elaborated_module(&module_name) {
            let elab_program = elab_program.clone();
            for edecl in &elab_program {
                match edecl {
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
                                source_module: Some(module_name.clone()),
                            });
                    }
                    Decl::FunSignature { .. } => {
                        // External function resolution handled by resolve.rs
                    }
                    _ => {}
                }
            }
        }
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
