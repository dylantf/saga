mod exprs;
mod pats;
mod util;

use crate::ast::{self, Decl, Expr, HandlerArm, Pat};
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use std::collections::HashMap;

use pats::{lower_params, lower_pat};
use util::{
    cerl_call, collect_ctor_call, collect_effect_call, collect_fun_call, collect_type_effects,
    core_var, field_access_record_name, lower_lit,
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

pub struct Lowerer {
    counter: usize,
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
}

impl Lowerer {
    pub fn new() -> Self {
        Lowerer {
            counter: 0,
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
        }
    }

    pub(super) fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("_Cor{}", n)
    }

    pub fn lower_module(&mut self, module_name: &str, program: &ast::Program) -> CModule {
        // Collect record field orders, effect definitions, handler definitions,
        // and function effect requirements.
        for decl in program {
            match decl {
                Decl::RecordDef { name, fields, .. } => {
                    let field_names = fields.iter().map(|(n, _)| n.clone()).collect();
                    self.record_fields.insert(name.clone(), field_names);
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
                            effects: effects.clone(),
                            arms: arms.clone(),
                            return_clause: return_clause.clone(),
                        },
                    );
                }
                Decl::FunAnnotation {
                    name,
                    effects,
                    params,
                    ..
                } => {
                    if !effects.is_empty() {
                        let mut sorted = effects.clone();
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
                        self.param_absorbed_effects
                            .insert(name.clone(), param_effs);
                    }
                }
                _ => {}
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
                    let arity = base_arity + effect_count;
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

        for (name, arity, clauses) in clause_groups {
            exports.push((name.clone(), arity));

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
                    if let Some(pat) = first_clause_params.get(*idx) {
                        if let Pat::Var { name: src_name, .. } = pat {
                            self.current_effectful_vars
                                .insert(src_name.clone(), effs.clone());
                        }
                    }
                }
            }

            let base_arity = arity - handler_params.len();

            let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() {
                // Single clause, no guard: emit directly without a case wrapper.
                let (params, _, body) = clauses[0];
                let mut params_ce = lower_params(params);
                params_ce.extend(handler_params.iter().cloned());
                let body_ce = self.lower_expr(body);
                CExpr::Fun(params_ce, Box::new(body_ce))
            } else {
                // Multi-clause or single clause with a guard: generate fresh arg vars
                // and case-match on them using proper Core Erlang values syntax.
                let mut arg_vars: Vec<String> =
                    (0..base_arity).map(|i| format!("_Arg{}", i)).collect();
                arg_vars.extend(handler_params.iter().cloned());

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
                            lower_pat(non_unit_pats[0], &self.record_fields)
                        } else if base_arity == 0 {
                            // No user params to match on -- use wildcard
                            CPat::Wildcard
                        } else {
                            CPat::Values(
                                non_unit_pats
                                    .iter()
                                    .map(|p| lower_pat(p, &self.record_fields))
                                    .collect(),
                            )
                        };
                        let guard_ce = guard.as_deref().map(|g| self.lower_expr(g));
                        let body_ce = self.lower_expr(body);
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
                // If referenced bare (not in application position), emit a FunRef
                // so it can be passed as a value.
                if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
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

                    if let Some(arity) = total_arity
                        && non_unit_args.len() + effect_count == arity
                    {
                        // Saturated call: apply fun 'name'/N(arg1, ..., argN, handler1, ...)
                        let mut arg_vars: Vec<String> = Vec::new();
                        let mut bindings: Vec<(String, CExpr)> = Vec::new();
                        let callee_param_effs =
                            self.param_absorbed_effects.get(func_name).cloned();
                        for (i, arg) in non_unit_args.iter().enumerate() {
                            let v = self.fresh();
                            // If this arg position has absorbed effects, set context
                            // so lambdas at this position get handler params added.
                            let saved_ctx = self.lambda_effect_context.take();
                            if let Some(ref pe) = callee_param_effs {
                                if let Some(effs) = pe.get(&i) {
                                    self.lambda_effect_context = Some(effs.clone());
                                }
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
                        }
                        let call = CExpr::Apply(
                            Box::new(CExpr::FunRef(func_name.to_string(), arity)),
                            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                        );
                        return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                            CExpr::Let(var, Box::new(val), Box::new(body))
                        });
                    }
                }

                // Check for call to an effectful variable (HOF absorption).
                // e.g. `computation ()` where computation absorbs Fail
                if let Some((var_name, args)) = collect_fun_call(expr) {
                    if let Some(absorbed) = self.current_effectful_vars.get(var_name).cloned() {
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
                        let call = CExpr::Apply(
                            Box::new(CExpr::Var(core_var(var_name))),
                            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                        );
                        return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                            CExpr::Let(var, Box::new(val), Box::new(body))
                        });
                    }
                }

                let (func, arg) = match expr {
                    Expr::App { func, arg, .. } => (func, arg),
                    _ => unreachable!(),
                };
                // General curried application (partial application or unknown function)
                let func_var = self.fresh();
                let arg_var = self.fresh();
                let func_ce = self.lower_expr(func);
                let arg_ce = self.lower_expr(arg);
                CExpr::Let(
                    func_var.clone(),
                    Box::new(func_ce),
                    Box::new(CExpr::Let(
                        arg_var.clone(),
                        Box::new(arg_ce),
                        Box::new(CExpr::Apply(
                            Box::new(CExpr::Var(func_var)),
                            vec![CExpr::Var(arg_var)],
                        )),
                    )),
                )
            }

            Expr::Constructor { name, .. } => {
                if name == "Nil" {
                    CExpr::Nil
                } else {
                    CExpr::Lit(CLit::Atom(name.clone()))
                }
            }

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
                let mut param_vars = lower_params(params);
                let saved_handler_params = self.current_handler_params.clone();
                // If a lambda_effect_context is set (from being passed to an
                // effectful HOF parameter), add handler params for those effects.
                // This ensures both pure and effectful lambdas have the right arity.
                if let Some(effects) = self.lambda_effect_context.take() {
                    for eff in &effects {
                        let handler_var = format!("_Handle{}", eff);
                        param_vars.push(handler_var.clone());
                        self.current_handler_params
                            .insert(eff.clone(), handler_var);
                    }
                } else {
                    // Not in a HOF context, but check if the body uses effects
                    // directly (e.g. lambda defined in a block that already has
                    // handler params in scope -- those are captured, not parameterized).
                }
                let body_ce = self.lower_expr(body);
                self.current_handler_params = saved_handler_params;
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

            Expr::QualifiedName { name, .. } => CExpr::Var(core_var(name)),

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
                let mut elems = vec![CExpr::Lit(CLit::Atom(name.clone()))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            Expr::FieldAccess { expr, field, .. } => {
                let record_name = field_access_record_name(expr);
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
                let record_name = field_access_record_name(record);
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
                let call = CExpr::Call(
                    module.clone(),
                    func.clone(),
                    vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                );
                bindings.into_iter().rev().fold(call, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            Expr::DictRef { name, .. } => {
                if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
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
                let v = self.fresh();
                let ce = self.lower_expr(value);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var("_K".to_string())),
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
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}
