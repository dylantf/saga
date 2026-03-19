mod builtins;
mod effects;
mod exprs;
mod init;
mod pats;
mod util;

use crate::ast::{self, Decl, Expr, ExprKind, HandlerArm, Pat};
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use crate::typechecker::ModuleCodegenInfo;
use std::collections::HashMap;

use init::PendingAnnotation;
use pats::{lower_params, lower_pat};
use util::{
    cerl_call, collect_ctor_call, collect_effect_call, collect_fun_call, collect_qualified_call,
    core_var, field_access_record_name, has_nested_effect_call, lower_lit,
};

type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);

/// Count how many lambda params can be absorbed from the body of a top-level
/// function definition. Peels nested lambdas so `fun x -> fun y -> body` counts 2.
fn count_lambda_params(body: &Expr) -> usize {
    match &body.kind {
        ExprKind::Lambda { params, body, .. } => params.len() + count_lambda_params(body),
        _ => 0,
    }
}

/// Stored handler definition for CPS inlining at `with` sites.
struct HandlerInfo {
    effects: Vec<String>,
    arms: Vec<HandlerArm>,
    return_clause: Option<Box<HandlerArm>>,
    /// The module this handler was defined in (e.g. "Std.Actor").
    /// Used to identify BEAM-native handlers that need special lowering.
    source_module: Option<String>,
}

/// Stored effect definition: maps op_name -> number of parameters.
#[allow(dead_code)]
struct EffectInfo {
    /// op_name -> param count
    ops: HashMap<String, usize>,
}

/// All information about a top-level function needed by the lowerer.
/// A single struct replaces separate `top_level_funs`, `fun_effects`,
/// `param_absorbed_effects`, and `imported_names` maps.
#[derive(Debug, Clone, Default)]
struct FunInfo {
    /// Exported arity (including handler params). 0 if not yet known (set by FunBinding).
    arity: usize,
    /// Effect names from `needs` clause (sorted).
    effects: Vec<String>,
    /// For EffArrow params: param_index -> absorbed effects.
    param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// If imported: (erlang_module, original_name).
    import_origin: Option<(String, String)>,
}

pub struct Lowerer<'a> {
    counter: usize,
    /// Codegen info for imported modules (from typechecker cache).
    codegen_info: &'a HashMap<String, ModuleCodegenInfo>,
    /// Elaborated programs per module, for cross-module handler lookup.
    elaborated_modules: &'a HashMap<String, ast::Program>,
    /// Maps module alias/name used in source -> Erlang module atom name.
    module_aliases: HashMap<String, String>,
    /// Names declared as `pub` in the current module (for export filtering).
    pub_names: std::collections::HashSet<String>,
    /// Maps record name -> ordered field names (from RecordDef declarations).
    record_fields: HashMap<String, Vec<String>>,
    /// All top-level function info: name -> FunInfo.
    fun_info: HashMap<String, FunInfo>,
    /// Maps effect name -> EffectInfo (op names and param counts).
    effect_defs: HashMap<String, EffectInfo>,
    /// Maps handler name -> handler arms + return clause.
    handler_defs: HashMap<String, HandlerInfo>,
    /// Maps op_name -> effect name (reverse lookup).
    op_to_effect: HashMap<String, String>,
    /// When lowering inside an effectful function, maps effect name -> handler param var name.
    current_handler_params: HashMap<String, String>,
    /// Set of "effect.op" keys whose current handler arm never calls resume.
    /// Used to pass a cheap atom instead of a real continuation closure at the call site,
    /// avoiding the Erlang "a term is constructed but never used" warning.
    no_resume_ops: std::collections::HashSet<String>,
    /// When lowering inside a function, maps local variable name -> effects it absorbs.
    /// Set from FunInfo.param_absorbed_effects for the current function.
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
    /// e.g. "Circle" -> "shapes", "Just" -> "std_maybe".
    /// Constructors not in this map are prelude builtins and are not mangled.
    constructor_modules: HashMap<String, String>,
    /// Maps external function name -> (erlang_module, erlang_func, arity).
    /// Populated from `Decl::ExternalFun` declarations.
    external_funs: HashMap<String, (String, String, usize)>,
}

impl<'a> Lowerer<'a> {
    pub fn new(
        codegen_info: &'a HashMap<String, ModuleCodegenInfo>,
        elaborated_modules: &'a HashMap<String, ast::Program>,
    ) -> Self {
        Lowerer {
            counter: 0,
            codegen_info,
            elaborated_modules,
            module_aliases: HashMap::new(),
            pub_names: std::collections::HashSet::new(),
            record_fields: HashMap::new(),
            fun_info: HashMap::new(),
            effect_defs: HashMap::new(),
            handler_defs: HashMap::new(),
            op_to_effect: HashMap::new(),
            current_handler_params: HashMap::new(),
            no_resume_ops: std::collections::HashSet::new(),
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

    /// Known BEAM-native handlers: (module, handler_name) pairs.
    /// These handlers' effects are lowered to direct BEAM calls instead of CPS.
    const BEAM_NATIVE_HANDLERS: &'static [(&'static str, &'static str)] =
        &[("Std.Actor", "beam_actor")];

    /// Check if a handler is BEAM-native (should be lowered to direct BEAM calls).
    pub(super) fn is_beam_native_handler(&self, name: &str) -> bool {
        self.handler_defs
            .get(name)
            .and_then(|info| info.source_module.as_deref())
            .is_some_and(|module| {
                Self::BEAM_NATIVE_HANDLERS
                    .iter()
                    .any(|(m, h)| *m == module && *h == name)
            })
    }

    /// Given a list of effect names (from a `needs` clause), return all
    /// (effect_name, op_name) pairs. This is the single source of truth for
    /// what handler params a function needs.
    pub(super) fn effect_handler_ops(&self, effects: &[String]) -> Vec<(String, String)> {
        let mut ops = Vec::new();
        for eff_name in effects {
            if let Some(info) = self.effect_defs.get(eff_name) {
                // Sort op names for deterministic ordering
                let mut op_names: Vec<&String> = info.ops.keys().collect();
                op_names.sort();
                for op_name in op_names {
                    ops.push((eff_name.clone(), op_name.clone()));
                }
            }
        }
        ops
    }

    /// Generate the handler param variable name for a specific effect op.
    /// e.g. ("Process", "spawn") -> "_Handle_Process_spawn"
    pub(super) fn handler_param_name(effect: &str, op: &str) -> String {
        format!("_Handle_{}_{}", effect, op)
    }

    /// Compute the expanded arity for a function with the given base arity
    /// and effect requirements. Accounts for one handler param per op plus
    /// a _ReturnK param if there are any effects.
    pub(super) fn expanded_arity(&self, base_arity: usize, effects: &[String]) -> usize {
        let ops = self.effect_handler_ops(effects);
        let op_count = ops.len();
        base_arity + op_count + if op_count > 0 { 1 } else { 0 }
    }

    /// Check if a function is effectful.
    fn is_effectful(&self, name: &str) -> bool {
        self.fun_info
            .get(name)
            .is_some_and(|f| !f.effects.is_empty())
    }

    /// Get a function's arity.
    fn fun_arity(&self, name: &str) -> Option<usize> {
        self.fun_info.get(name).map(|f| f.arity)
    }

    /// Get a function's effects.
    fn fun_effects(&self, name: &str) -> Option<&Vec<String>> {
        self.fun_info
            .get(name)
            .map(|f| &f.effects)
            .filter(|e| !e.is_empty())
    }

    /// Get a function's import origin (erlang_module, original_name).
    fn import_origin(&self, name: &str) -> Option<&(String, String)> {
        self.fun_info
            .get(name)
            .and_then(|f| f.import_origin.as_ref())
    }

    /// Get a function's param absorbed effects.
    fn param_absorbed_effects(&self, name: &str) -> Option<&HashMap<usize, Vec<String>>> {
        self.fun_info
            .get(name)
            .map(|f| &f.param_absorbed_effects)
            .filter(|m| !m.is_empty())
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
        let mut pending_annotations = self.init_module(module_name, program);

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
                    let PendingAnnotation {
                        effects,
                        param_absorbed_effects,
                    } = pending_annotations
                        .remove(name.as_str())
                        .unwrap_or(PendingAnnotation {
                            effects: Vec::new(),
                            param_absorbed_effects: HashMap::new(),
                        });
                    let base_arity =
                        lower_params(params).len() + count_lambda_params(body);
                    let arity = self.expanded_arity(base_arity, &effects);
                    if let Some(group) = clause_groups.iter_mut().find(|(n, _, _)| n == name) {
                        // Additional clause: just add to existing group
                        group.2.push((params, guard, body));
                    } else {
                        // First clause: register fun_info (overrides any pre-registration)
                        self.fun_info.insert(
                            name.clone(),
                            FunInfo {
                                arity,
                                effects,
                                param_absorbed_effects,
                                import_origin: None,
                            },
                        );
                        clause_groups.push((name.clone(), arity, vec![(params, guard, body)]));
                    }
                }
                Decl::DictConstructor {
                    name,
                    dict_params,
                    methods,
                    ..
                } => {
                    self.fun_info.insert(
                        name.clone(),
                        FunInfo {
                            arity: dict_params.len(),
                            ..Default::default()
                        },
                    );
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

            // Set up handler param context for effectful functions.
            // One handler param per op (e.g. _Handle_Process_spawn, _Handle_Process_send).
            let effects = self.fun_effects(&name).cloned().unwrap_or_default();
            let handler_ops = self.effect_handler_ops(&effects);
            let handler_params: Vec<String> = handler_ops
                .iter()
                .map(|(eff, op)| Self::handler_param_name(eff, op))
                .collect();
            let saved_handler_params = std::mem::take(&mut self.current_handler_params);
            for ((eff, op), param) in handler_ops.iter().zip(handler_params.iter()) {
                // Key by "Effect.op" for unambiguous lookup from lower_effect_call
                let key = format!("{}.{}", eff, op);
                self.current_handler_params.insert(key, param.clone());
            }
            // Set up effectful variable tracking for HOF absorption.
            // Map param indices to param names from the first clause's patterns.
            let saved_effectful_vars = std::mem::take(&mut self.current_effectful_vars);
            if let Some(param_effs) = self.param_absorbed_effects(&name).cloned() {
                let first_clause_params = clauses[0].0;
                for (idx, effs) in &param_effs {
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
                // Absorb nested lambda params into the function's param list.
                // e.g. `f dict = fun x -> body` becomes `f(dict, x) = body`
                let mut body = body;
                while let ExprKind::Lambda {
                    params: lam_params,
                    body: lam_body,
                    ..
                } = &body.kind
                {
                    params_ce.extend(lower_params(lam_params));
                    body = lam_body;
                }
                params_ce.extend(handler_params.iter().cloned());
                if has_effects {
                    params_ce.push("_ReturnK".to_string());
                }
                // For non-block bodies, lower_block didn't run, so apply return_k.
                // Special case: if the body is a terminal effect call, pass _ReturnK
                // directly as K so abort-style handlers skip the rest (proper CPS).
                let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
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
                                self.is_effectful(name)
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
                        let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
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
        match &expr.kind {
            ExprKind::Lit { value, .. } => CExpr::Lit(lower_lit(value)),

            ExprKind::Var { name, .. } => {
                // If it's an imported name used bare, emit an external fun ref.
                if let Some((erl_mod, erl_name)) = self.import_origin(name).cloned() {
                    if let Some(arity) = self.fun_arity(name) {
                        CExpr::Call(
                            "erlang".to_string(),
                            "make_fun".to_string(),
                            vec![
                                CExpr::Lit(CLit::Atom(erl_mod)),
                                CExpr::Lit(CLit::Atom(erl_name)),
                                CExpr::Lit(CLit::Int(arity as i64)),
                            ],
                        )
                    } else {
                        CExpr::Var(core_var(name))
                    }
                } else if let Some(arity) = self.fun_arity(name) {
                    // If referenced bare (not in application position), emit a FunRef
                    // so it can be passed as a value.
                    CExpr::FunRef(name.clone(), arity)
                } else {
                    CExpr::Var(core_var(name))
                }
            }

            ExprKind::App { .. } => {
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

                // Lower print/println/eprint/eprintln to io:format, dbg to stderr+passthrough
                if let Some((func_name, args)) = collect_fun_call(expr) {
                    let lowered = match func_name {
                        "print" => self.lower_builtin_print(&args, false, false),
                        "println" => self.lower_builtin_print(&args, false, true),
                        "eprint" => self.lower_builtin_print(&args, true, false),
                        "eprintln" => self.lower_builtin_print(&args, true, true),
                        "dbg" => self.lower_builtin_dbg(&args),
                        _ => None,
                    };
                    if let Some(ce) = lowered {
                        return ce;
                    }
                }

                // Lower `panic msg` / `todo msg` to stderr print + erlang:halt(1)
                if let Some((func_name, args)) = collect_fun_call(expr)
                    && (func_name == "panic" || func_name == "todo")
                    && args.len() == 1
                {
                    let prefix = if func_name == "panic" {
                        "panic: "
                    } else {
                        "todo: "
                    };
                    let arg = self.lower_expr(args[0]);
                    let v = self.fresh();
                    let prefixed = self.fresh();
                    let dummy = self.fresh();
                    // Prepend "panic: " / "todo: " to the message
                    let prepend = cerl_call(
                        "erlang",
                        "++",
                        vec![
                            CExpr::Lit(CLit::Str(prefix.into())),
                            CExpr::Var(v.clone()),
                        ],
                    );
                    // io:format(standard_error, "~ts~n", [Msg])
                    let print_stderr = cerl_call(
                        "io",
                        "format",
                        vec![
                            CExpr::Lit(CLit::Atom("standard_error".into())),
                            CExpr::Lit(CLit::Str("~ts~n".into())),
                            CExpr::Cons(
                                Box::new(CExpr::Var(prefixed.clone())),
                                Box::new(CExpr::Nil),
                            ),
                        ],
                    );
                    let halt = cerl_call("erlang", "halt", vec![CExpr::Lit(CLit::Int(1))]);
                    return CExpr::Let(
                        v,
                        Box::new(arg),
                        Box::new(CExpr::Let(
                            prefixed,
                            Box::new(prepend),
                            Box::new(CExpr::Let(dummy, Box::new(print_stderr), Box::new(halt))),
                        )),
                    );
                }

                // Check for a saturated call to a known top-level function.
                // e.g. `add 3 4` -> App(App(Var("add"), 3), 4)
                // For effectful functions, the user provides N args but the function
                // takes N+M where M is the number of handler params. We thread
                // the caller's handler params through automatically.
                if let Some((func_name, args)) = collect_fun_call(expr) {
                    let callee_effects = self.fun_effects(func_name).cloned();
                    let callee_ops = callee_effects.as_ref()
                        .map(|effs| self.effect_handler_ops(effs))
                        .unwrap_or_default();
                    let effect_count = callee_ops.len();
                    let total_arity = self.fun_arity(func_name);

                    // Filter out unit literal args (they don't count toward arity)
                    let non_unit_args: Vec<&Expr> = args
                        .into_iter()
                        .filter(|a| {
                            !matches!(
                                a.kind,
                                ExprKind::Lit {
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
                        let callee_param_effs = self.param_absorbed_effects(func_name).cloned();
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
                        // Append per-op handler params for effectful callees
                        if !callee_ops.is_empty() {
                            for (eff, op) in &callee_ops {
                                let key = format!("{}.{}", eff, op);
                                if let Some(param) = self.current_handler_params.get(&key) {
                                    arg_vars.push(param.clone());
                                } else {
                                    panic!(
                                        "function '{}' needs handler for '{}.{}' but no handler param in scope",
                                        func_name, eff, op
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
                        } else if let Some((erl_mod, erl_name)) = self.import_origin(func_name) {
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
                                a.kind,
                                ExprKind::Lit {
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
                    // Append per-op handler params for absorbed effects
                    let absorbed_ops = self.effect_handler_ops(&absorbed);
                    for (eff, op) in &absorbed_ops {
                        let key = format!("{}.{}", eff, op);
                        if let Some(param) = self.current_handler_params.get(&key) {
                            arg_vars.push(param.clone());
                        } else {
                            panic!(
                                "effectful variable '{}' needs handler for '{}.{}' but no handler param in scope",
                                var_name, eff, op
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
                while let ExprKind::App { func, arg, .. } = &callee.kind {
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
                    // Skip unit literal args (they don't exist at the BEAM level)
                    if matches!(
                        arg.kind,
                        ExprKind::Lit {
                            value: ast::Lit::Unit,
                            ..
                        }
                    ) {
                        continue;
                    }
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

            ExprKind::Constructor { name, .. } => match name.as_str() {
                "Nil" => CExpr::Nil,
                // Booleans are bare atoms to match Erlang's native true/false
                "True" => CExpr::Lit(CLit::Atom("true".to_string())),
                "False" => CExpr::Lit(CLit::Atom("false".to_string())),
                // ExitReason constructors are bare atoms to match Erlang exit reasons
                "Normal" => CExpr::Lit(CLit::Atom("normal".to_string())),
                "Shutdown" => CExpr::Lit(CLit::Atom("shutdown".to_string())),
                "Killed" => CExpr::Lit(CLit::Atom("killed".to_string())),
                "Noproc" => CExpr::Lit(CLit::Atom("noproc".to_string())),
                _ => {
                    let atom = util::mangle_ctor_atom(name, &self.constructor_modules);
                    // Wrap in a 1-tuple to match pattern representation and avoid atom collisions
                    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(atom))])
                }
            },

            ExprKind::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right),

            ExprKind::UnaryMinus { expr, .. } => {
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

            ExprKind::If {
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

            ExprKind::Block { stmts, .. } => self.lower_block(stmts),

            ExprKind::Lambda { params, body, .. } => {
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
                    let lambda_ops = self.effect_handler_ops(&effects);
                    for (eff, op) in &lambda_ops {
                        let handler_var = Self::handler_param_name(eff, op);
                        param_vars.push(handler_var.clone());
                        let key = format!("{}.{}", eff, op);
                        self.current_handler_params.insert(key, handler_var);
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
                let body_ce = if is_effectful_lambda && !matches!(body.kind, ExprKind::Block { .. }) {
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
                                self.is_effectful(name)
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
                                .map(|p| {
                                    lower_pat(p, &self.record_fields, &self.constructor_modules)
                                })
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

            ExprKind::Case {
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

            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                // Lower arms: same pattern/guard/body as case, but for receive
                // there is no scrutinee variable to fall through to.
                let lowered_arms: Vec<CArm> = arms
                    .iter()
                    .map(|arm| {
                        // System message patterns: bind a raw reason variable
                        // and wrap the body with a conversion case.
                        let (pat, reason_wrapper) = if let Pat::Constructor { name, args, .. } =
                            &arm.pattern
                        {
                            if matches!(name.as_str(), "Down" | "Exit") && args.len() == 2 {
                                // Check if reason arg is a variable that needs conversion
                                let (reason_pat, wrapper) =
                                    if let Pat::Var { name: var_name, .. } = &args[1] {
                                        let raw = self.fresh();
                                        (CPat::Var(raw.clone()), Some((core_var(var_name), raw)))
                                    } else {
                                        (
                                            lower_pat(
                                                &args[1],
                                                &self.record_fields,
                                                &self.constructor_modules,
                                            ),
                                            None,
                                        )
                                    };

                                let tuple_pat = if name == "Down" {
                                    // {'DOWN', _Ref, 'process', Pid, Reason}
                                    CPat::Tuple(vec![
                                        CPat::Lit(CLit::Atom("DOWN".into())),
                                        CPat::Wildcard,
                                        CPat::Lit(CLit::Atom("process".into())),
                                        lower_pat(
                                            &args[0],
                                            &self.record_fields,
                                            &self.constructor_modules,
                                        ),
                                        reason_pat,
                                    ])
                                } else {
                                    // {'EXIT', Pid, Reason}
                                    CPat::Tuple(vec![
                                        CPat::Lit(CLit::Atom("EXIT".into())),
                                        lower_pat(
                                            &args[0],
                                            &self.record_fields,
                                            &self.constructor_modules,
                                        ),
                                        reason_pat,
                                    ])
                                };
                                (tuple_pat, wrapper)
                            } else {
                                (
                                    lower_pat(
                                        &arm.pattern,
                                        &self.record_fields,
                                        &self.constructor_modules,
                                    ),
                                    None,
                                )
                            }
                        } else {
                            (
                                lower_pat(
                                    &arm.pattern,
                                    &self.record_fields,
                                    &self.constructor_modules,
                                ),
                                None,
                            )
                        };
                        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
                        let raw_body = self.lower_expr(&arm.body);
                        // Convert raw Erlang exit reason to ExitReason type
                        let body = if let Some((user_var, raw_var)) = reason_wrapper {
                            let cm = &self.constructor_modules;
                            let normal = util::mangle_ctor_atom("Normal", cm);
                            let shutdown = util::mangle_ctor_atom("Shutdown", cm);
                            let killed = util::mangle_ctor_atom("Killed", cm);
                            let noproc = util::mangle_ctor_atom("Noproc", cm);
                            let error = util::mangle_ctor_atom("Error", cm);
                            let other = util::mangle_ctor_atom("Other", cm);
                            // case RawReason of
                            //   'normal' -> Normal
                            //   'shutdown' -> Shutdown
                            //   'killed' -> Killed
                            //   'noproc' -> Noproc
                            //   {'error', Msg, _} -> Error(Msg)
                            //   Other -> Other(lists:flatten(io_lib:format("~p", [Other])))
                            let other_var = self.fresh();
                            let fmt_var = self.fresh();
                            let stringify = CExpr::Call(
                                "lists".into(),
                                "flatten".into(),
                                vec![CExpr::Call(
                                    "io_lib".into(),
                                    "format".into(),
                                    vec![
                                        CExpr::Lit(CLit::Str("~p".into())),
                                        CExpr::Cons(
                                            Box::new(CExpr::Var(other_var.clone())),
                                            Box::new(CExpr::Nil),
                                        ),
                                    ],
                                )],
                            );
                            let error_msg_var = self.fresh();
                            let conversion = CExpr::Case(
                                Box::new(CExpr::Var(raw_var)),
                                vec![
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("normal".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(normal.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("shutdown".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(shutdown.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("killed".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(killed.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("noproc".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(noproc.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Tuple(vec![
                                            CPat::Var(error_msg_var.clone()),
                                            CPat::Wildcard, // stacktrace
                                        ]),
                                        guard: None,
                                        body: CExpr::Tuple(vec![
                                            CExpr::Lit(CLit::Atom(error.clone())),
                                            CExpr::Var(error_msg_var),
                                        ]),
                                    },
                                    CArm {
                                        pat: CPat::Var(other_var.clone()),
                                        guard: None,
                                        body: CExpr::Let(
                                            fmt_var.clone(),
                                            Box::new(stringify),
                                            Box::new(CExpr::Tuple(vec![
                                                CExpr::Lit(CLit::Atom(other.clone())),
                                                CExpr::Var(fmt_var),
                                            ])),
                                        ),
                                    },
                                ],
                            );
                            CExpr::Let(user_var, Box::new(conversion), Box::new(raw_body))
                        } else {
                            raw_body
                        };
                        CArm { pat, guard, body }
                    })
                    .collect();

                let (timeout, timeout_body) = if let Some((t, b)) = after_clause {
                    (self.lower_expr(t), self.lower_expr(b))
                } else {
                    (
                        CExpr::Lit(CLit::Atom("infinity".into())),
                        CExpr::Lit(CLit::Atom("true".into())),
                    )
                };

                CExpr::Receive(lowered_arms, Box::new(timeout), Box::new(timeout_body))
            }

            ExprKind::Tuple { elements, .. } => self.lower_tuple_elems(elements),

            ExprKind::QualifiedName { module, name, .. } => {
                // Dict.empty is a value, not a function -- emit maps:new()
                if module == "Dict" && name == "empty" {
                    return cerl_call("maps", "new", vec![]);
                }

                // When used as a bare reference (not in application position),
                // emit a FunRef if it's a known imported function, otherwise a Var.
                let qualified = format!("{}.{}", module, name);
                if let Some(arity) = self.fun_arity(&qualified) {
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

            ExprKind::RecordCreate { name, fields, .. } => {
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

            ExprKind::FieldAccess { expr, field, .. } => {
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

            ExprKind::RecordUpdate { record, fields, .. } => {
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

            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => self.lower_do(bindings, success, else_arms),

            // --- Elaboration-only constructs ---
            ExprKind::DictMethodAccess {
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

            ExprKind::ForeignCall {
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
                // erlang:monitor/1 -> erlang:monitor/2 with 'process' atom
                let call = if module == "erlang" && func == "monitor" && vars.len() == 1 {
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vec![
                            CExpr::Lit(CLit::Atom("process".into())),
                            CExpr::Var(vars[0].clone()),
                        ],
                    )
                // float_to_list/1 -> float_to_list/2 with [short] option
                } else if module == "erlang" && func == "float_to_list" && vars.len() == 1 {
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

            ExprKind::DictRef { name, .. } => {
                if let Some((erl_mod, erl_name)) = self.import_origin(name).cloned() {
                    // Cross-module dict constructor
                    let arity = self.fun_arity(name).unwrap_or(0);
                    if arity == 0 {
                        CExpr::Call(erl_mod, erl_name, vec![])
                    } else {
                        CExpr::Call(
                            "erlang".to_string(),
                            "make_fun".to_string(),
                            vec![
                                CExpr::Lit(CLit::Atom(erl_mod)),
                                CExpr::Lit(CLit::Atom(erl_name)),
                                CExpr::Lit(CLit::Int(arity as i64)),
                            ],
                        )
                    }
                } else if let Some(arity) = self.fun_arity(name) {
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
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
                ..
            } => self.lower_effect_call(name, qualifier.as_deref(), args, None),

            // `expr with handler` -- attaches handler(s) to a computation
            ExprKind::With { expr, handler, .. } => self.lower_with(expr, handler),

            // `resume value` -- inside a handler arm, calls the continuation K
            ExprKind::Resume { value, .. } => {
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

        // String builtins
        if let Some(ce) = self.lower_builtin_string(module, func_name, args) {
            return ce;
        }

        // Regex builtins
        if let Some(ce) = self.lower_builtin_regex(module, func_name, args) {
            return ce;
        }

        let erlang_module = self
            .module_aliases
            .get(module)
            .cloned()
            .unwrap_or_else(|| module.to_lowercase());

        let qualified = format!("{}.{}", module, func_name);
        let callee_effects = self.fun_effects(&qualified).cloned();
        let callee_ops = callee_effects.as_ref()
            .map(|effs| self.effect_handler_ops(effs))
            .unwrap_or_default();

        // Filter out unit literal args
        let non_unit_args: Vec<&&Expr> = args
            .iter()
            .filter(|a| {
                !matches!(
                    a.kind,
                    ExprKind::Lit {
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

        // Append per-op handler params for effectful callees
        if !callee_ops.is_empty() {
            for (eff, op) in &callee_ops {
                let key = format!("{}.{}", eff, op);
                if let Some(param) = self.current_handler_params.get(&key) {
                    arg_vars.push(param.clone());
                } else {
                    panic!(
                        "qualified call '{}.{}' needs handler for '{}.{}' but no handler param in scope",
                        module, func_name, eff, op
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
