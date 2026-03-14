mod builtins;
mod exprs;
mod pats;
mod util;

use crate::ast::{self, Decl, Expr, HandlerArm, Pat};
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use crate::typechecker::ModuleCodegenInfo;
use std::collections::HashMap;

use pats::{lower_params, lower_pat};
use util::{
    cerl_call, collect_ctor_call, collect_effect_call, collect_fun_call, collect_qualified_call,
    collect_type_effects, core_var, field_access_record_name, has_nested_effect_call, lower_lit,
};

type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);

/// Stored handler definition for CPS inlining at `with` sites.
struct HandlerInfo {
    effects: Vec<String>,
    arms: Vec<HandlerArm>,
    return_clause: Option<Box<HandlerArm>>,
}

/// Stored effect definition: maps op_name -> number of parameters.
#[allow(dead_code)]
struct EffectInfo {
    /// op_name -> param count
    ops: HashMap<String, usize>,
}

pub struct Lowerer<'a> {
    counter: usize,
    /// Codegen info for imported modules (from typechecker cache).
    codegen_info: &'a HashMap<String, ModuleCodegenInfo>,
    /// Maps module alias/name used in source -> Erlang module atom name.
    module_aliases: HashMap<String, String>,
    /// Maps unqualified imported name -> (erlang_module, original_name).
    /// For exposed imports like `import Math (add)`, `add` maps to `("math", "add")`.
    imported_names: HashMap<String, (String, String)>,
    /// Names declared as `pub` in the current module (for export filtering).
    pub_names: std::collections::HashSet<String>,
    /// Maps record name -> ordered field names (from RecordDef declarations).
    record_fields: HashMap<String, Vec<String>>,
    /// Maps top-level function name -> its exported arity (including handler params).
    /// All multi-arg functions are curried to arity 1.
    top_level_funs: HashMap<String, usize>,
    /// Maps effect name -> EffectInfo (op names and param counts).
    effect_defs: HashMap<String, EffectInfo>,
    /// Maps handler name -> handler arms + return clause.
    handler_defs: HashMap<String, HandlerInfo>,
    /// Maps function name -> list of effect names from `needs` (declaration order).
    fun_effects: HashMap<String, Vec<String>>,
    /// Maps op_name -> effect name (reverse lookup).
    op_to_effect: HashMap<String, String>,
    /// When lowering inside an effectful function, maps effect name -> handler param var name.
    current_handler_params: HashMap<String, String>,
    /// Maps function name -> (param_index -> absorbed effects) for EffArrow params.
    /// e.g. for `fun try (computation: () -> a needs {Fail}) -> ...`,
    /// stores `"try" -> {0 -> ["Fail"]}`.
    param_absorbed_effects: HashMap<String, HashMap<usize, Vec<String>>>,
    /// When lowering inside a function, maps local variable name -> effects it absorbs.
    /// Set from `param_absorbed_effects` for the current function.
    current_effectful_vars: HashMap<String, Vec<String>>,
    /// Effects that the next lambda being lowered should accept as extra params.
    /// Set by the call site that passes the lambda to an effectful parameter.
    lambda_effect_context: Option<Vec<String>>,
    /// Return continuation for the current `with` expression's return clause.
    /// Set by `lower_with`, consumed by `lower_block` at its terminal cases.
    /// This places the return clause inside the CPS chain so handler aborts
    /// (which don't call K) naturally bypass the return clause.
    current_return_k: Option<CExpr>,
    /// Return continuation to pass as `_ReturnK` to the next effectful call.
    /// Set by `lower_with` when the inner expression is a direct function call,
    /// consumed by the saturated call path.
    pending_callee_return_k: Option<CExpr>,
    /// Variable name for the continuation parameter in the current handler function.
    /// Set by `build_handler_fun`, read by `Expr::Resume`.
    current_handler_k: Option<String>,
    /// Maps constructor name -> erlang module name for atom mangling.
    /// e.g. "Circle" -> "shapes", "Some" -> "std_maybe".
    /// Constructors not in this map are prelude builtins and are not mangled.
    constructor_modules: HashMap<String, String>,
    /// Maps external function name -> (erlang_module, erlang_func, arity).
    /// Populated from `Decl::ExternalFun` declarations.
    external_funs: HashMap<String, (String, String, usize)>,
}

impl<'a> Lowerer<'a> {
    pub fn new(codegen_info: &'a HashMap<String, ModuleCodegenInfo>) -> Self {
        Lowerer {
            counter: 0,
            codegen_info,
            module_aliases: HashMap::new(),
            imported_names: HashMap::new(),
            pub_names: std::collections::HashSet::new(),
            record_fields: HashMap::new(),
            top_level_funs: HashMap::new(),
            effect_defs: HashMap::new(),
            handler_defs: HashMap::new(),
            fun_effects: HashMap::new(),
            op_to_effect: HashMap::new(),
            current_handler_params: HashMap::new(),
            param_absorbed_effects: HashMap::new(),
            current_effectful_vars: HashMap::new(),
            lambda_effect_context: None,
            current_return_k: None,
            pending_callee_return_k: None,
            constructor_modules: HashMap::new(),
            current_handler_k: None,
            external_funs: HashMap::new(),
        }
    }

    pub(super) fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("_Cor{}", n)
    }

    /// Find a record name that contains the given field.
    fn find_record_by_field(&self, field: &str) -> Option<&str> {
        self.record_fields.iter().find_map(|(rname, fields)| {
            if fields.iter().any(|f| f == field) {
                Some(rname.as_str())
            } else {
                None
            }
        })
    }

    /// Find a record name whose field list contains all the given update field names.
    fn find_record_by_fields(&self, field_names: &[String]) -> Option<&str> {
        self.record_fields.iter().find_map(|(rname, fields)| {
            if field_names.iter().all(|f| fields.contains(f)) {
                Some(rname.as_str())
            } else {
                None
            }
        })
    }

    pub fn lower_module(&mut self, module_name: &str, program: &ast::Program) -> CModule {
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
                    if !effects.is_empty() {
                        let mut sorted: Vec<String> =
                            effects.iter().map(|e| e.name.clone()).collect();
                        sorted.sort();
                        self.fun_effects.insert(name.clone(), sorted);
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
                    if !param_effs.is_empty() {
                        self.param_absorbed_effects.insert(name.clone(), param_effs);
                    }
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
                    // Register effects if declared
                    if !effects.is_empty() {
                        let mut sorted: Vec<String> =
                            effects.iter().map(|e| e.name.clone()).collect();
                        sorted.sort();
                        self.fun_effects.insert(name.clone(), sorted);
                    }
                    // Register as a top-level function with the appropriate arity
                    let effect_count = effects.len();
                    let expanded_arity =
                        real_arity + effect_count + if effect_count > 0 { 1 } else { 0 };
                    self.top_level_funs.insert(name.clone(), expanded_arity);
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
            for (_trait_name, _target_type, dict_name, arity) in &info.trait_impl_dicts {
                self.top_level_funs.entry(dict_name.clone()).or_insert(*arity);
                self.imported_names
                    .entry(dict_name.clone())
                    .or_insert_with(|| (erlang_name.clone(), dict_name.clone()));
            }
            if mod_name.starts_with("Std.") {
                // Register Std exports so prelude-imported functions (e.g. fst, snd)
                // resolve to cross-module calls without an explicit import in user code.
                for (name, scheme) in &info.exports {
                    let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
                    let effect_count = effects.len();
                    let expanded_arity =
                        base_arity + effect_count + if effect_count > 0 { 1 } else { 0 };
                    self.top_level_funs.entry(name.clone()).or_insert(expanded_arity);
                    self.imported_names
                        .entry(name.clone())
                        .or_insert_with(|| (erlang_name.clone(), name.clone()));
                    if !effects.is_empty() {
                        self.fun_effects.entry(name.clone()).or_insert(effects);
                    }
                }
                for (_type_name, ctors) in &info.type_constructors {
                    for ctor in ctors {
                        self.constructor_modules
                            .insert(ctor.clone(), erlang_name.clone());
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
                let prefix = alias.as_deref().unwrap_or(&module_name).to_string();
                let erlang_name = util::module_name_to_erlang(module_path);
                self.module_aliases
                    .insert(prefix.clone(), erlang_name.clone());

                if let Some(info) = self.codegen_info.get(&module_name) {
                    // Build a set of exported names for checking exposing list
                    let exported_names: std::collections::HashSet<&str> =
                        info.exports.iter().map(|(n, _)| n.as_str()).collect();

                    // Register imported functions with qualified keys
                    for (name, scheme) in &info.exports {
                        let (base_arity, effects) = util::arity_and_effects_from_type(&scheme.ty);
                        let effect_count = effects.len();
                        let expanded_arity =
                            base_arity + effect_count + if effect_count > 0 { 1 } else { 0 };
                        let qualified = format!("{}.{}", prefix, name);
                        self.top_level_funs
                            .insert(qualified.clone(), expanded_arity);
                        if !effects.is_empty() {
                            self.fun_effects.insert(qualified, effects);
                        }
                    }

                    // Register exposed (unqualified) names
                    if let Some(exposed) = exposing {
                        for name in exposed {
                            if exported_names.contains(name.as_str()) {
                                // Find the scheme to get arity/effects
                                if let Some((_, scheme)) =
                                    info.exports.iter().find(|(n, _)| n == name)
                                {
                                    let (base_arity, effects) =
                                        util::arity_and_effects_from_type(&scheme.ty);
                                    let effect_count = effects.len();
                                    let expanded_arity = base_arity
                                        + effect_count
                                        + if effect_count > 0 { 1 } else { 0 };
                                    self.top_level_funs.insert(name.clone(), expanded_arity);
                                    self.imported_names
                                        .insert(name.clone(), (erlang_name.clone(), name.clone()));
                                    if !effects.is_empty() {
                                        self.fun_effects.insert(name.clone(), effects);
                                    }
                                }
                            }
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
                    for (_trait_name, _target_type, dict_name, arity) in &info.trait_impl_dicts {
                        self.top_level_funs.insert(dict_name.clone(), *arity);
                        self.imported_names
                            .insert(dict_name.clone(), (erlang_name.clone(), dict_name.clone()));
                    }
                }
            }
        }

        // Group FunBindings by name, preserving declaration order, and simultaneously
        // populate top_level_funs. Handler params are added to the arity for effectful funs.
        let mut clause_groups: Vec<(String, usize, Vec<Clause>)> = Vec::new();
        let mut dict_constructors: Vec<(&str, &[String], &[Expr])> = Vec::new();
        for decl in program {
            match decl {
                Decl::FunBinding {
                    name,
                    params,
                    guard,
                    body,
                    ..
                } => {
                    let base_arity = lower_params(params).len();
                    let effect_count = self
                        .fun_effects
                        .get(name.as_str())
                        .map_or(0, |effs| effs.len());
                    let arity = base_arity + effect_count + if effect_count > 0 { 1 } else { 0 };
                    self.top_level_funs.entry(name.clone()).or_insert(arity);
                    if let Some(group) = clause_groups.iter_mut().find(|(n, _, _)| n == name) {
                        group.2.push((params, guard, body));
                    } else {
                        clause_groups.push((name.clone(), arity, vec![(params, guard, body)]));
                    }
                }
                Decl::DictConstructor {
                    name,
                    dict_params,
                    methods,
                    ..
                } => {
                    self.top_level_funs.insert(name.clone(), dict_params.len());
                    dict_constructors.push((name, dict_params, methods));
                }
                _ => {}
            }
        }

        let mut exports = Vec::new();
        let mut fun_defs = Vec::new();

        // If there's no module declaration, it's a single-file script -- export everything.
        let is_module = program.iter().any(|d| matches!(d, Decl::ModuleDecl { .. }));

        // Generate wrapper functions for external declarations so cross-module
        // imports can call them by the local name.
        for decl in program {
            if let Decl::ExternalFun {
                public,
                name,
                module: erl_module,
                func: erl_func,
                params,
                ..
            } = decl
            {
                let arity = params.len();
                let arg_vars: Vec<String> = (0..arity).map(|i| format!("_Ext{}", i)).collect();
                let call_args: Vec<CExpr> =
                    arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                let call = CExpr::Call(erl_module.clone(), erl_func.clone(), call_args);
                fun_defs.push(CFunDef {
                    name: name.clone(),
                    arity,
                    body: CExpr::Fun(arg_vars, Box::new(call)),
                });
                if *public || !is_module {
                    exports.push((name.clone(), arity));
                }
            }
        }

        for (name, arity, clauses) in clause_groups {
            if !is_module || self.pub_names.contains(&name) {
                exports.push((name.clone(), arity));
            }

            // Set up handler param context for effectful functions
            let effects = self.fun_effects.get(&name).cloned().unwrap_or_default();
            let handler_params: Vec<String> = effects
                .iter()
                .map(|eff| format!("_Handle{}", eff))
                .collect();
            let saved_handler_params = std::mem::take(&mut self.current_handler_params);
            for (eff, param) in effects.iter().zip(handler_params.iter()) {
                self.current_handler_params
                    .insert(eff.clone(), param.clone());
            }
            // Set up effectful variable tracking for HOF absorption.
            // Map param indices to param names from the first clause's patterns.
            let saved_effectful_vars = std::mem::take(&mut self.current_effectful_vars);
            if let Some(param_effs) = self.param_absorbed_effects.get(&name) {
                let first_clause_params = clauses[0].0;
                for (idx, effs) in param_effs {
                    if let Some(pat) = first_clause_params.get(*idx)
                        && let Pat::Var { name: src_name, .. } = pat
                    {
                        self.current_effectful_vars
                            .insert(src_name.clone(), effs.clone());
                    }
                }
            }

            let has_effects = !handler_params.is_empty();
            let base_arity = arity - handler_params.len() - if has_effects { 1 } else { 0 };

            // For effectful functions, set _ReturnK as current_return_k so
            // lower_block applies it at terminal positions. Handler aborts
            // bypass the function's normal return, so they skip _ReturnK.
            let saved_return_k = self.current_return_k.take();
            if has_effects {
                self.current_return_k = Some(CExpr::Var("_ReturnK".to_string()));
            }

            let all_simple_params = clauses.len() == 1
                && clauses[0].0.iter().all(|p| {
                    matches!(
                        p,
                        Pat::Var { .. }
                            | Pat::Wildcard { .. }
                            | Pat::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                    )
                });
            let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() && all_simple_params {
                // Single clause, no guard: emit directly without a case wrapper.
                let (params, _, body) = clauses[0];
                let mut params_ce = lower_params(params);
                params_ce.extend(handler_params.iter().cloned());
                if has_effects {
                    params_ce.push("_ReturnK".to_string());
                }
                // For non-block bodies, lower_block didn't run, so apply return_k.
                // Special case: if the body is a terminal effect call, pass _ReturnK
                // directly as K so abort-style handlers skip the rest (proper CPS).
                let body_ce = if has_effects && !matches!(body, Expr::Block { .. }) {
                    if let Some((op_name, qualifier, args)) = collect_effect_call(body) {
                        let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                        self.lower_effect_call(
                            op_name,
                            qualifier,
                            &args_owned,
                            self.current_return_k.clone(),
                        )
                    } else if has_nested_effect_call(body) {
                        // Nested effect calls in branches (e.g. if/case with fail!):
                        // thread _ReturnK through branches so abort skips the wrap.
                        let k_var = self.fresh();
                        let k_ce = self.current_return_k.clone().unwrap();
                        let body_ce = self.lower_expr_with_k(body, &k_var);
                        CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
                    } else {
                        // Check for effectful function call: pass _ReturnK directly
                        let is_eff_call = collect_fun_call(body)
                            .map(|(name, _)| {
                                self.fun_effects.contains_key(name)
                                    || self.current_effectful_vars.contains_key(name)
                            })
                            .unwrap_or(false);
                        if is_eff_call {
                            let saved = self.pending_callee_return_k.take();
                            self.pending_callee_return_k = self.current_return_k.clone();
                            let result = self.lower_expr(body);
                            self.pending_callee_return_k = saved;
                            result
                        } else {
                            let body_ce = self.lower_expr(body);
                            self.apply_return_k(body_ce)
                        }
                    }
                } else {
                    self.lower_expr(body)
                };
                CExpr::Fun(params_ce, Box::new(body_ce))
            } else {
                // Multi-clause or single clause with a guard: generate fresh arg vars
                // and case-match on them using proper Core Erlang values syntax.
                let mut arg_vars: Vec<String> =
                    (0..base_arity).map(|i| format!("_Arg{}", i)).collect();
                arg_vars.extend(handler_params.iter().cloned());
                if has_effects {
                    arg_vars.push("_ReturnK".to_string());
                }

                let arms: Vec<CArm> = clauses
                    .iter()
                    .map(|(params, guard, body)| {
                        // Unit params were dropped in arity counting; filter here too.
                        let non_unit_pats: Vec<&Pat> = params
                            .iter()
                            .filter(|p| {
                                !matches!(
                                    p,
                                    Pat::Lit {
                                        value: ast::Lit::Unit,
                                        ..
                                    }
                                )
                            })
                            .collect();
                        // Pattern only matches user params, not handler params
                        let pat = if base_arity == 1 {
                            lower_pat(
                                non_unit_pats[0],
                                &self.record_fields,
                                &self.constructor_modules,
                            )
                        } else if base_arity == 0 {
                            // No user params to match on -- use wildcard
                            CPat::Wildcard
                        } else {
                            CPat::Values(
                                non_unit_pats
                                    .iter()
                                    .map(|p| {
                                        lower_pat(p, &self.record_fields, &self.constructor_modules)
                                    })
                                    .collect(),
                            )
                        };
                        let guard_ce = guard.as_deref().map(|g| self.lower_expr(g));
                        let body_ce = if has_effects && !matches!(body, Expr::Block { .. }) {
                            if let Some((op_name, qualifier, args)) = collect_effect_call(body) {
                                let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                                self.lower_effect_call(
                                    op_name,
                                    qualifier,
                                    &args_owned,
                                    self.current_return_k.clone(),
                                )
                            } else if has_nested_effect_call(body) {
                                let k_var = self.fresh();
                                let k_ce = self.current_return_k.clone().unwrap();
                                let body_ce = self.lower_expr_with_k(body, &k_var);
                                CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
                            } else {
                                let body_ce = self.lower_expr(body);
                                self.apply_return_k(body_ce)
                            }
                        } else {
                            self.lower_expr(body)
                        };
                        CArm {
                            pat,
                            guard: guard_ce,
                            body: body_ce,
                        }
                    })
                    .collect();

                // Scrutinee: bare variable for base_arity==1, Values expression otherwise.
                // For effectful arity-0 functions, case on a dummy atom.
                let scrut_ce = if base_arity == 0 {
                    CExpr::Lit(CLit::Atom("unit".to_string()))
                } else if base_arity == 1 {
                    CExpr::Var(arg_vars[0].clone())
                } else {
                    CExpr::Values(
                        arg_vars[..base_arity]
                            .iter()
                            .map(|v| CExpr::Var(v.clone()))
                            .collect(),
                    )
                };
                let case_ce = CExpr::Case(Box::new(scrut_ce), arms);
                CExpr::Fun(arg_vars, Box::new(case_ce))
            };

            self.current_return_k = saved_return_k;

            self.current_handler_params = saved_handler_params;
            self.current_effectful_vars = saved_effectful_vars;

            fun_defs.push(CFunDef {
                name,
                arity,
                body: fun_body,
            });
        }

        // Emit dictionary constructor functions
        for (name, dict_params, methods) in dict_constructors {
            let arity = dict_params.len();
            let params: Vec<String> = dict_params.iter().map(|p| core_var(p)).collect();
            let method_exprs: Vec<CExpr> = methods.iter().map(|m| self.lower_expr(m)).collect();
            let body = CExpr::Tuple(method_exprs);
            exports.push((name.to_string(), arity));
            fun_defs.push(CFunDef {
                name: name.to_string(),
                arity,
                body: CExpr::Fun(params, Box::new(body)),
            });
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs: fun_defs,
        }
    }

    pub(super) fn lower_expr(&mut self, expr: &Expr) -> CExpr {
        match expr {
            Expr::Lit { value, .. } => CExpr::Lit(lower_lit(value)),

            Expr::Var { name, .. } => {
                // If it's an imported name used bare, emit an external fun ref.
                if let Some((erl_mod, erl_name)) = self.imported_names.get(name.as_str()) {
                    if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
                        CExpr::Call(
                            "erlang".to_string(),
                            "make_fun".to_string(),
                            vec![
                                CExpr::Lit(CLit::Atom(erl_mod.clone())),
                                CExpr::Lit(CLit::Atom(erl_name.clone())),
                                CExpr::Lit(CLit::Int(arity as i64)),
                            ],
                        )
                    } else {
                        CExpr::Var(core_var(name))
                    }
                } else if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
                    // If referenced bare (not in application position), emit a FunRef
                    // so it can be passed as a value.
                    CExpr::FunRef(name.clone(), arity)
                } else {
                    CExpr::Var(core_var(name))
                }
            }

            Expr::App { .. } => {
                if let Some((ctor_name, args)) = collect_ctor_call(expr) {
                    return self.lower_ctor(ctor_name, args);
                }

                // Check for effect call: App(EffectCall { .. }, arg1, ...)
                if let Some((op_name, qualifier, args)) = collect_effect_call(expr) {
                    return self.lower_effect_call(
                        op_name,
                        qualifier,
                        &args.into_iter().cloned().collect::<Vec<_>>(),
                        None,
                    );
                }

                // Check for a qualified call: App(QualifiedName { module, name }, arg1, ...)
                // e.g. `Math.abs x` -> call 'math':'abs'(X)
                if let Some((module, func_name, args)) = collect_qualified_call(expr) {
                    return self.lower_qualified_call(module, func_name, &args);
                }

                // Lower `print(dict, x)` to io:format("~s~n", [show(x)])
                if let Some((func_name, args)) = collect_fun_call(expr)
                    && func_name == "print"
                    && let Some(ce) = self.lower_builtin_print(&args)
                {
                    return ce;
                }

                // Lower `panic msg` / `todo msg` to erlang:error(msg)
                if let Some((func_name, args)) = collect_fun_call(expr)
                    && (func_name == "panic" || func_name == "todo")
                    && args.len() == 1
                {
                    let arg = self.lower_expr(args[0]);
                    let v = self.fresh();
                    return CExpr::Let(
                        v.clone(),
                        Box::new(arg),
                        Box::new(cerl_call("erlang", "error", vec![CExpr::Var(v)])),
                    );
                }

                // Check for a saturated call to a known top-level function.
                // e.g. `add 3 4` -> App(App(Var("add"), 3), 4)
                // For effectful functions, the user provides N args but the function
                // takes N+M where M is the number of handler params. We thread
                // the caller's handler params through automatically.
                if let Some((func_name, args)) = collect_fun_call(expr) {
                    let callee_effects = self.fun_effects.get(func_name).cloned();
                    let effect_count = callee_effects.as_ref().map_or(0, |e| e.len());
                    let total_arity = self.top_level_funs.get(func_name).copied();

                    // Filter out unit literal args (they don't count toward arity)
                    let non_unit_args: Vec<&Expr> = args
                        .into_iter()
                        .filter(|a| {
                            !matches!(
                                a,
                                Expr::Lit {
                                    value: ast::Lit::Unit,
                                    ..
                                }
                            )
                        })
                        .collect();

                    let return_k_count = if effect_count > 0 { 1 } else { 0 };
                    if let Some(arity) = total_arity
                        && non_unit_args.len() + effect_count + return_k_count == arity
                    {
                        // Saturated call: apply fun 'name'/N(arg1, ..., argN, handler1, ...)
                        let mut arg_vars: Vec<String> = Vec::new();
                        let mut bindings: Vec<(String, CExpr)> = Vec::new();
                        let callee_param_effs = self.param_absorbed_effects.get(func_name).cloned();
                        for (i, arg) in non_unit_args.iter().enumerate() {
                            let v = self.fresh();
                            // If this arg position has absorbed effects, set context
                            // so lambdas at this position get handler params added.
                            let saved_ctx = self.lambda_effect_context.take();
                            if let Some(ref pe) = callee_param_effs
                                && let Some(effs) = pe.get(&i)
                            {
                                self.lambda_effect_context = Some(effs.clone());
                            }
                            let ce = self.lower_expr(arg);
                            self.lambda_effect_context = saved_ctx;
                            arg_vars.push(v.clone());
                            bindings.push((v, ce));
                        }
                        // Append handler params for effectful callees
                        if let Some(effs) = &callee_effects {
                            for eff in effs {
                                if let Some(param) = self.current_handler_params.get(eff) {
                                    arg_vars.push(param.clone());
                                } else {
                                    panic!(
                                        "function '{}' needs effect '{}' but no handler param in scope",
                                        func_name, eff
                                    );
                                }
                            }
                            // Pass _ReturnK: take from pending (set by `with`), or identity
                            let return_k =
                                self.pending_callee_return_k.take().unwrap_or_else(|| {
                                    let p = self.fresh();
                                    CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
                                });
                            let rk_var = self.fresh();
                            bindings.push((rk_var.clone(), return_k));
                            arg_vars.push(rk_var);
                        }
                        let call_args: Vec<CExpr> =
                            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                        let call = if let Some((erl_mod, erl_func, _)) =
                            self.external_funs.get(func_name)
                        {
                            // float_to_list/1 -> float_to_list/2 with [short] option
                            if erl_mod == "erlang"
                                && erl_func == "float_to_list"
                                && call_args.len() == 1
                            {
                                let opts = CExpr::Cons(
                                    Box::new(CExpr::Lit(CLit::Atom("short".into()))),
                                    Box::new(CExpr::Nil),
                                );
                                CExpr::Call(
                                    erl_mod.clone(),
                                    erl_func.clone(),
                                    vec![call_args.into_iter().next().unwrap(), opts],
                                )
                            } else {
                                // External function: direct call to the foreign module
                                CExpr::Call(erl_mod.clone(), erl_func.clone(), call_args)
                            }
                        } else if let Some((erl_mod, erl_name)) = self.imported_names.get(func_name)
                        {
                            CExpr::Call(erl_mod.clone(), erl_name.clone(), call_args)
                        } else {
                            CExpr::Apply(
                                Box::new(CExpr::FunRef(func_name.to_string(), arity)),
                                call_args,
                            )
                        };
                        return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                            CExpr::Let(var, Box::new(val), Box::new(body))
                        });
                    }
                }

                // Check for call to an effectful variable (HOF absorption).
                // e.g. `computation ()` where computation absorbs Fail
                if let Some((var_name, args)) = collect_fun_call(expr)
                    && let Some(absorbed) = self.current_effectful_vars.get(var_name).cloned()
                {
                    let mut arg_vars: Vec<String> = Vec::new();
                    let mut bindings: Vec<(String, CExpr)> = Vec::new();
                    // Filter out unit literal args
                    let non_unit_args: Vec<&Expr> = args
                        .into_iter()
                        .filter(|a| {
                            !matches!(
                                a,
                                Expr::Lit {
                                    value: ast::Lit::Unit,
                                    ..
                                }
                            )
                        })
                        .collect();
                    for arg in non_unit_args {
                        let v = self.fresh();
                        let ce = self.lower_expr(arg);
                        arg_vars.push(v.clone());
                        bindings.push((v, ce));
                    }
                    // Append handler params for absorbed effects
                    for eff in &absorbed {
                        if let Some(param) = self.current_handler_params.get(eff) {
                            arg_vars.push(param.clone());
                        } else {
                            panic!(
                                "effectful variable '{}' needs effect '{}' but no handler param in scope",
                                var_name, eff
                            );
                        }
                    }
                    // Pass _ReturnK: take from pending (set by `with`), or identity
                    {
                        let return_k = self.pending_callee_return_k.take().unwrap_or_else(|| {
                            let p = self.fresh();
                            CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
                        });
                        let rk_var = self.fresh();
                        bindings.push((rk_var.clone(), return_k));
                        arg_vars.push(rk_var);
                    }
                    let call = CExpr::Apply(
                        Box::new(CExpr::Var(core_var(var_name))),
                        arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                    );
                    return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                        CExpr::Let(var, Box::new(val), Box::new(body))
                    });
                }

                // Collect the full App chain and emit a single multi-arg Apply.
                // e.g. `f acc h` = App(App(f, acc), h) -> apply F(Acc, H)
                let mut callee = expr;
                let mut args_rev = Vec::new();
                while let Expr::App { func, arg, .. } = callee {
                    args_rev.push(arg.as_ref());
                    callee = func.as_ref();
                }
                args_rev.reverse();

                let mut bindings = Vec::new();
                let func_var = self.fresh();
                let func_ce = self.lower_expr(callee);
                bindings.push((func_var.clone(), func_ce));

                let mut arg_vars = Vec::new();
                for arg in &args_rev {
                    let v = self.fresh();
                    let ce = self.lower_expr(arg);
                    bindings.push((v.clone(), ce));
                    arg_vars.push(v);
                }

                let call = CExpr::Apply(
                    Box::new(CExpr::Var(func_var)),
                    arg_vars.into_iter().map(CExpr::Var).collect(),
                );
                bindings.into_iter().rev().fold(call, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            Expr::Constructor { name, .. } => match name.as_str() {
                "Nil" => CExpr::Nil,
                // Booleans are bare atoms to match Erlang's native true/false
                "True" => CExpr::Lit(CLit::Atom("true".to_string())),
                "False" => CExpr::Lit(CLit::Atom("false".to_string())),
                _ => {
                    let atom = util::mangle_ctor_atom(name, &self.constructor_modules);
                    // Wrap in a 1-tuple to match pattern representation and avoid atom collisions
                    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(atom))])
                }
            },

            Expr::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right),

            Expr::UnaryMinus { expr, .. } => {
                let v = self.fresh();
                let ce = self.lower_expr(expr);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(cerl_call(
                        "erlang",
                        "-",
                        vec![CExpr::Lit(CLit::Int(0)), CExpr::Var(v)],
                    )),
                )
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_var = self.fresh();
                let cond_ce = self.lower_expr(cond);
                let then_ce = self.lower_expr(then_branch);
                let else_ce = self.lower_expr(else_branch);
                CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: then_ce,
                            },
                            CArm {
                                pat: CPat::Lit(CLit::Atom("false".to_string())),
                                guard: None,
                                body: else_ce,
                            },
                        ],
                    )),
                )
            }

            Expr::Block { stmts, .. } => self.lower_block(stmts),

            Expr::Lambda { params, body, .. } => {
                let all_simple = params.iter().all(|p| {
                    matches!(
                        p,
                        Pat::Var { .. }
                            | Pat::Wildcard { .. }
                            | Pat::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                    )
                });
                let mut param_vars = lower_params(params);
                let saved_handler_params = self.current_handler_params.clone();
                let saved_return_k = self.current_return_k.take();
                // If a lambda_effect_context is set (from being passed to an
                // effectful HOF parameter), add handler params for those effects.
                // This ensures both pure and effectful lambdas have the right arity.
                let mut is_effectful_lambda = false;
                if let Some(effects) = self.lambda_effect_context.take() {
                    for eff in &effects {
                        let handler_var = format!("_Handle{}", eff);
                        param_vars.push(handler_var.clone());
                        self.current_handler_params.insert(eff.clone(), handler_var);
                    }
                    // Add _ReturnK parameter for effectful lambdas
                    param_vars.push("_ReturnK".to_string());
                    self.current_return_k = Some(CExpr::Var("_ReturnK".to_string()));
                    is_effectful_lambda = true;
                } else {
                    // Not in a HOF context, but check if the body uses effects
                    // directly (e.g. lambda defined in a block that already has
                    // handler params in scope -- those are captured, not parameterized).
                }
                let body_ce = if is_effectful_lambda && !matches!(**body, Expr::Block { .. }) {
                    if let Some((op_name, qualifier, args)) = collect_effect_call(body) {
                        let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                        self.lower_effect_call(
                            op_name,
                            qualifier,
                            &args_owned,
                            self.current_return_k.clone(),
                        )
                    } else if has_nested_effect_call(body) {
                        let k_var = self.fresh();
                        let k_ce = self.current_return_k.clone().unwrap();
                        let body_ce = self.lower_expr_with_k(body, &k_var);
                        CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
                    } else {
                        // Check for effectful function call: pass _ReturnK directly
                        let is_eff_call = collect_fun_call(body)
                            .map(|(name, _)| {
                                self.fun_effects.contains_key(name)
                                    || self.current_effectful_vars.contains_key(name)
                            })
                            .unwrap_or(false);
                        if is_eff_call {
                            let saved = self.pending_callee_return_k.take();
                            self.pending_callee_return_k = self.current_return_k.clone();
                            let result = self.lower_expr(body);
                            self.pending_callee_return_k = saved;
                            result
                        } else {
                            let body_ce = self.lower_expr(body);
                            self.apply_return_k(body_ce)
                        }
                    }
                } else {
                    self.lower_expr(body)
                };
                self.current_handler_params = saved_handler_params;
                self.current_return_k = saved_return_k;
                // If lambda has complex params (tuples, constructors), wrap
                // the body in a case expression for destructuring.
                let body_ce = if !all_simple {
                    let scrutinee = if param_vars.len() == 1 {
                        CExpr::Var(param_vars[0].clone())
                    } else {
                        CExpr::Tuple(param_vars.iter().map(|v| CExpr::Var(v.clone())).collect())
                    };
                    let pat = if params.len() == 1 {
                        lower_pat(&params[0], &self.record_fields, &self.constructor_modules)
                    } else {
                        CPat::Tuple(
                            params
                                .iter()
                                .map(|p| lower_pat(p, &self.record_fields, &self.constructor_modules))
                                .collect(),
                        )
                    };
                    CExpr::Case(
                        Box::new(scrutinee),
                        vec![CArm {
                            pat,
                            guard: None,
                            body: body_ce,
                        }],
                    )
                } else {
                    body_ce
                };
                CExpr::Fun(param_vars, Box::new(body_ce))
            }

            Expr::Case {
                scrutinee, arms, ..
            } => {
                let scrut_var = self.fresh();
                let scrut_ce = self.lower_expr(scrutinee);
                let arms_ce = self.lower_case_arms(&scrut_var, arms);
                CExpr::Let(
                    scrut_var.clone(),
                    Box::new(scrut_ce),
                    Box::new(CExpr::Case(Box::new(CExpr::Var(scrut_var)), arms_ce)),
                )
            }

            Expr::Tuple { elements, .. } => self.lower_tuple_elems(elements),

            Expr::QualifiedName { module, name, .. } => {
                // Dict.empty is a value, not a function -- emit maps:new()
                if module == "Dict" && name == "empty" {
                    return cerl_call("maps", "new", vec![]);
                }

                // When used as a bare reference (not in application position),
                // emit a FunRef if it's a known imported function, otherwise a Var.
                let qualified = format!("{}.{}", module, name);
                if let Some(&arity) = self.top_level_funs.get(&qualified) {
                    let erlang_module = self
                        .module_aliases
                        .get(module.as_str())
                        .cloned()
                        .unwrap_or_else(|| module.to_lowercase());
                    // In Core Erlang, referencing an external function as a value
                    // is done with: fun 'module':'name'/arity
                    CExpr::Call(
                        "erlang".to_string(),
                        "make_fun".to_string(),
                        vec![
                            CExpr::Lit(CLit::Atom(erlang_module)),
                            CExpr::Lit(CLit::Atom(name.clone())),
                            CExpr::Lit(CLit::Int(arity as i64)),
                        ],
                    )
                } else {
                    CExpr::Var(core_var(name))
                }
            }

            Expr::RecordCreate { name, fields, .. } => {
                let order = self.record_fields.get(name).cloned().unwrap_or_default();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &order {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in RecordCreate");
                    let ce = self.lower_expr(e);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                let atom = util::mangle_ctor_atom(name, &self.constructor_modules);
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            Expr::FieldAccess { expr, field, .. } => {
                let record_name =
                    field_access_record_name(expr).or_else(|| self.find_record_by_field(field));
                let idx = record_name
                    .and_then(|rname| self.record_fields.get(rname))
                    .and_then(|fields| fields.iter().position(|f| f == field))
                    .map(|pos| pos + 2) // +1 for tag, +1 for 1-based
                    .unwrap_or(2) as i64;
                let v = self.fresh();
                let ce = self.lower_expr(expr);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(cerl_call(
                        "erlang",
                        "element",
                        vec![CExpr::Lit(CLit::Int(idx)), CExpr::Var(v)],
                    )),
                )
            }

            Expr::RecordUpdate { record, fields, .. } => {
                let rec_var = self.fresh();
                let rec_ce = self.lower_expr(record);
                let update_field_names: Vec<String> =
                    fields.iter().map(|(n, _)| n.clone()).collect();
                let record_name = field_access_record_name(record)
                    .or_else(|| self.find_record_by_fields(&update_field_names));
                let order = record_name
                    .and_then(|rname| self.record_fields.get(rname))
                    .cloned()
                    .unwrap_or_default();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, e)| (n.as_str(), e)).collect();

                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for (pos, field_name) in order.iter().enumerate() {
                    let v = self.fresh();
                    let ce = if let Some(new_expr) = field_map.get(field_name.as_str()) {
                        self.lower_expr(new_expr)
                    } else {
                        let idx = (pos + 2) as i64;
                        cerl_call(
                            "erlang",
                            "element",
                            vec![CExpr::Lit(CLit::Int(idx)), CExpr::Var(rec_var.clone())],
                        )
                    };
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                // Preserve the tag via element(1, rec)
                let tag_var = self.fresh();
                let tag_ce = cerl_call(
                    "erlang",
                    "element",
                    vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(rec_var.clone())],
                );
                let mut elems = vec![CExpr::Var(tag_var.clone())];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                let inner = bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                });
                let with_tag = CExpr::Let(tag_var, Box::new(tag_ce), Box::new(inner));
                CExpr::Let(rec_var, Box::new(rec_ce), Box::new(with_tag))
            }

            Expr::Do {
                bindings,
                success,
                else_arms,
                ..
            } => self.lower_do(bindings, success, else_arms),

            // --- Elaboration-only constructs ---
            Expr::DictMethodAccess {
                dict, method_index, ..
            } => {
                // Lower to: let D = <dict> in element(idx+1, D)
                let dict_var = self.fresh();
                let dict_ce = self.lower_expr(dict);
                let extract_method = cerl_call(
                    "erlang",
                    "element",
                    vec![
                        CExpr::Lit(CLit::Int(*method_index as i64 + 1)),
                        CExpr::Var(dict_var.clone()),
                    ],
                );
                CExpr::Let(dict_var, Box::new(dict_ce), Box::new(extract_method))
            }

            Expr::ForeignCall {
                module, func, args, ..
            } => {
                let mut vars = Vec::new();
                let mut bindings = Vec::new();
                for arg in args {
                    let v = self.fresh();
                    let ce = self.lower_expr(arg);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                // float_to_list/1 -> float_to_list/2 with [short] option
                let call = if module == "erlang" && func == "float_to_list" && vars.len() == 1 {
                    let opts = CExpr::Cons(
                        Box::new(CExpr::Lit(CLit::Atom("short".into()))),
                        Box::new(CExpr::Nil),
                    );
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vec![CExpr::Var(vars[0].clone()), opts],
                    )
                } else {
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                    )
                };
                bindings.into_iter().rev().fold(call, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            Expr::DictRef { name, .. } => {
                if let Some((erl_mod, erl_name)) = self.imported_names.get(name.as_str()) {
                    // Cross-module dict constructor
                    let arity = self.top_level_funs.get(name.as_str()).copied().unwrap_or(0);
                    if arity == 0 {
                        CExpr::Call(erl_mod.clone(), erl_name.clone(), vec![])
                    } else {
                        CExpr::Call(
                            "erlang".to_string(),
                            "make_fun".to_string(),
                            vec![
                                CExpr::Lit(CLit::Atom(erl_mod.clone())),
                                CExpr::Lit(CLit::Atom(erl_name.clone())),
                                CExpr::Lit(CLit::Int(arity as i64)),
                            ],
                        )
                    }
                } else if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
                    if arity == 0 {
                        // Nullary dict constructor: call it to get the dict tuple
                        CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), 0)), vec![])
                    } else {
                        // Parameterized dict constructor: reference it
                        CExpr::FunRef(name.clone(), arity)
                    }
                } else {
                    // Dict param variable (passed as function argument)
                    CExpr::Var(core_var(name))
                }
            }

            // --- Effect system (CPS transform) ---

            // `log! "hello"` -- standalone effect call (not in a block).
            // When an effect call appears as a bare expression (not in a block where
            // we can capture the continuation), we call the handler with an identity
            // continuation that just returns the value.
            Expr::EffectCall {
                name,
                qualifier,
                args,
                ..
            } => self.lower_effect_call(name, qualifier.as_deref(), args, None),

            // `expr with handler` -- attaches handler(s) to a computation
            Expr::With { expr, handler, .. } => self.lower_with(expr, handler),

            // `resume value` -- inside a handler arm, calls the continuation K
            Expr::Resume { value, .. } => {
                let k_name = self
                    .current_handler_k
                    .clone()
                    .expect("resume used outside handler");
                let v = self.fresh();
                let ce = self.lower_expr(value);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(k_name)),
                        vec![CExpr::Var(v)],
                    )),
                )
            }

            // StringInterpolation should be desugared before reaching the lowerer,
            // but keep a fallback just in case.
            #[allow(unreachable_patterns)]
            other => CExpr::Lit(CLit::Atom(format!(
                "todo_{:?}",
                std::mem::discriminant(other)
            ))),
        }
    }

    /// Lower a qualified function call like `Math.abs x` to `call 'math':'abs'(X)`.
    /// For effectful imported functions, handler params and _ReturnK are threaded.
    fn lower_qualified_call(&mut self, module: &str, func_name: &str, args: &[&Expr]) -> CExpr {
        // Builtin conversion functions
        if let Some(ce) = self.lower_builtin_conversion(module, func_name, args) {
            return ce;
        }

        // Dict builtins
        if let Some(ce) = self.lower_builtin_dict(module, func_name, args) {
            return ce;
        }

        let erlang_module = self
            .module_aliases
            .get(module)
            .cloned()
            .unwrap_or_else(|| module.to_lowercase());

        let qualified = format!("{}.{}", module, func_name);
        let callee_effects = self.fun_effects.get(&qualified).cloned();
        let effect_count = callee_effects.as_ref().map_or(0, |e| e.len());

        // Filter out unit literal args
        let non_unit_args: Vec<&&Expr> = args
            .iter()
            .filter(|a| {
                !matches!(
                    a,
                    Expr::Lit {
                        value: ast::Lit::Unit,
                        ..
                    }
                )
            })
            .collect();

        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();

        for arg in &non_unit_args {
            let v = self.fresh();
            let ce = self.lower_expr(arg);
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }

        // Append handler params for effectful callees
        if let Some(effs) = &callee_effects {
            for eff in effs {
                if let Some(param) = self.current_handler_params.get(eff) {
                    arg_vars.push(param.clone());
                } else {
                    panic!(
                        "qualified call '{}.{}' needs effect '{}' but no handler param in scope",
                        module, func_name, eff
                    );
                }
            }
            // Pass _ReturnK
            let return_k = self.pending_callee_return_k.take().unwrap_or_else(|| {
                let p = self.fresh();
                CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
            });
            let rk_var = self.fresh();
            bindings.push((rk_var.clone(), return_k));
            arg_vars.push(rk_var);
        }

        let _ = effect_count; // used implicitly through callee_effects

        let call = CExpr::Call(
            erlang_module,
            func_name.to_string(),
            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
        );

        bindings.into_iter().rev().fold(call, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }
}
