mod exprs;
mod pats;
mod util;

use crate::ast::{self, Decl, Expr, Pat};
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use std::collections::HashMap;

use pats::{lower_params, lower_pat};
use util::{
    cerl_call, collect_ctor_call, collect_fun_call, core_var, field_access_record_name, lower_lit,
};

type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);

pub struct Lowerer {
    counter: usize,
    /// Maps record name -> ordered field names (from RecordDef declarations).
    record_fields: HashMap<String, Vec<String>>,
    /// Maps top-level function name -> its exported arity (0 or 1).
    /// All multi-arg functions are curried to arity 1.
    top_level_funs: HashMap<String, usize>,
}

impl Lowerer {
    pub fn new() -> Self {
        Lowerer {
            counter: 0,
            record_fields: HashMap::new(),
            top_level_funs: HashMap::new(),
        }
    }

    pub(super) fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("_Cor{}", n)
    }

    pub fn lower_module(&mut self, module_name: &str, program: &ast::Program) -> CModule {
        // Collect record field orders so we can lower field access by position.
        for decl in program {
            if let Decl::RecordDef { name, fields, .. } = decl {
                let field_names = fields.iter().map(|(n, _)| n.clone()).collect();
                self.record_fields.insert(name.clone(), field_names);
            }
        }

        // Group FunBindings by name, preserving declaration order, and simultaneously
        // populate top_level_funs. lower_params is called once per clause here.
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
                    let arity = lower_params(params).len();
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
                    self.top_level_funs
                        .insert(name.clone(), dict_params.len());
                    dict_constructors.push((name, dict_params, methods));
                }
                _ => {}
            }
        }

        let mut exports = Vec::new();
        let mut fun_defs = Vec::new();

        for (name, arity, clauses) in clause_groups {
            exports.push((name.clone(), arity));

            let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() {
                // Single clause, no guard: emit directly without a case wrapper.
                let (params, _, body) = clauses[0];
                let params_ce = lower_params(params);
                let body_ce = self.lower_expr(body);
                CExpr::Fun(params_ce, Box::new(body_ce))
            } else {
                // Multi-clause or single clause with a guard: generate fresh arg vars
                // and case-match on them using proper Core Erlang values syntax.
                let arg_vars: Vec<String> = (0..arity).map(|i| format!("_Arg{}", i)).collect();

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
                        let pat = if arity == 1 {
                            lower_pat(non_unit_pats[0], &self.record_fields)
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

                // Scrutinee: bare variable for arity==1, Values expression otherwise.
                let scrut_ce = if arity == 1 {
                    CExpr::Var(arg_vars[0].clone())
                } else {
                    CExpr::Values(arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect())
                };
                let case_ce = CExpr::Case(Box::new(scrut_ce), arms);
                CExpr::Fun(arg_vars, Box::new(case_ce))
            };

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
            let method_exprs: Vec<CExpr> =
                methods.iter().map(|m| self.lower_expr(m)).collect();
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

            Expr::Var { name, .. } => match name.as_str() {
                "print" | "show" => CExpr::Var(format!("__builtin_{}", name)),
                _ => {
                    // If referenced bare (not in application position), emit a FunRef
                    // so it can be passed as a value.
                    if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
                        CExpr::FunRef(name.clone(), arity)
                    } else {
                        CExpr::Var(core_var(name))
                    }
                }
            },

            Expr::App { .. } => {
                if let Some((ctor_name, args)) = collect_ctor_call(expr) {
                    return self.lower_ctor(ctor_name, args);
                }

                // Check for a saturated call to a known top-level function.
                // e.g. `add 3 4` -> App(App(Var("add"), 3), 4)
                // Peel the App chain; if the head is a known function with matching arity,
                // emit a single multi-arg apply instead of nested one-arg applies.
                if let Some((func_name, args)) = collect_fun_call(expr)
                    && let Some(&arity) = self.top_level_funs.get(func_name)
                    && args.len() == arity
                {
                    // Saturated call: apply fun 'name'/N(arg1, ..., argN)
                    let mut arg_vars: Vec<String> = Vec::new();
                    let mut bindings: Vec<(String, CExpr)> = Vec::new();
                    for arg in args {
                        let v = self.fresh();
                        let ce = self.lower_expr(arg);
                        arg_vars.push(v.clone());
                        bindings.push((v, ce));
                    }
                    let call = CExpr::Apply(
                        Box::new(CExpr::FunRef(func_name.to_string(), arity)),
                        arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                    );
                    return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                        CExpr::Let(var, Box::new(val), Box::new(body))
                    });
                }

                let (func, arg) = match expr {
                    Expr::App { func, arg, .. } => (func, arg),
                    _ => unreachable!(),
                };
                // Special case: print builtin
                if let Expr::Var { name, .. } = func.as_ref()
                    && name == "print"
                {
                    let arg_var = self.fresh();
                    let arg_ce = self.lower_expr(arg);
                    return CExpr::Let(
                        arg_var.clone(),
                        Box::new(arg_ce),
                        Box::new(CExpr::Call(
                            "io".to_string(),
                            "format".to_string(),
                            vec![
                                CExpr::Lit(CLit::Str("~s~n".to_string())),
                                CExpr::Cons(Box::new(CExpr::Var(arg_var)), Box::new(CExpr::Nil)),
                            ],
                        )),
                    );
                }
                // Special case: show builtin -> io_lib:format("~w", [x])
                if let Expr::Var { name, .. } = func.as_ref()
                    && name == "show"
                {
                    let arg_var = self.fresh();
                    let arg_ce = self.lower_expr(arg);
                    return CExpr::Let(
                        arg_var.clone(),
                        Box::new(arg_ce),
                        Box::new(CExpr::Call(
                            "io_lib".to_string(),
                            "format".to_string(),
                            vec![
                                CExpr::Lit(CLit::Str("~w".to_string())),
                                CExpr::Cons(Box::new(CExpr::Var(arg_var)), Box::new(CExpr::Nil)),
                            ],
                        )),
                    );
                }
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
                let param_vars = lower_params(params);
                let body_ce = self.lower_expr(body);
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
                dict,
                method_index,
                ..
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
                CExpr::Let(
                    dict_var,
                    Box::new(dict_ce),
                    Box::new(extract_method),
                )
            }

            Expr::DictRef { name, .. } => {
                if let Some(&arity) = self.top_level_funs.get(name.as_str()) {
                    if arity == 0 {
                        // Nullary dict constructor: call it to get the dict tuple
                        CExpr::Apply(
                            Box::new(CExpr::FunRef(name.clone(), 0)),
                            vec![],
                        )
                    } else {
                        // Parameterized dict constructor: reference it
                        CExpr::FunRef(name.clone(), arity)
                    }
                } else {
                    // Dict param variable (passed as function argument)
                    CExpr::Var(core_var(name))
                }
            }

            _ => CExpr::Lit(CLit::Atom(format!(
                "todo_{:?}",
                std::mem::discriminant(expr)
            ))),
        }
    }
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}
