/// Expression-lowering helper methods on Lowerer.
/// These are the implementations for specific expression forms, split out of
/// mod.rs to keep file sizes manageable. Effects go in effects.rs, traits in
/// traits.rs, etc.
use crate::ast::{BinOp, CaseArm, Expr, Handler, HandlerArm, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::Lowerer;
use super::pats::lower_pat;
use super::util::{binop_call, collect_effect_call, core_var, pat_binding_var};

/// Returns true if `expr` is a valid Core Erlang guard expression:
/// comparisons, arithmetic, boolean ops, unary minus, and literals/variables.
/// Any function application (user-defined or unknown BIF) returns false.
fn is_guard_safe(expr: &Expr) -> bool {
    match expr {
        Expr::Lit { .. } | Expr::Var { .. } => true,
        Expr::BinOp { left, right, .. } => is_guard_safe(left) && is_guard_safe(right),
        Expr::UnaryMinus { expr, .. } => is_guard_safe(expr),
        // No App, Constructor, Block, If, Case, etc. -- too complex for a guard
        _ => false,
    }
}

impl Lowerer {
    /// Lower a list of case arms, handling complex guards by desugaring them
    /// into conditional expressions inside the arm body.
    ///
    /// A "complex" guard (one containing a function call) can't be emitted
    /// directly in Core Erlang. Instead we transform:
    ///   `Pat if complex_guard -> body`
    /// into:
    ///   `Pat -> if complex_guard then body else case scrut_var of <remaining arms>`
    pub(super) fn lower_case_arms(&mut self, scrut_var: &str, arms: &[CaseArm]) -> Vec<CArm> {
        let mut result = Vec::new();

        for (i, arm) in arms.iter().enumerate() {
            let pat = lower_pat(&arm.pattern, &self.record_fields);

            match &arm.guard {
                None => {
                    result.push(CArm {
                        pat,
                        guard: None,
                        body: self.lower_expr(&arm.body),
                    });
                }
                Some(guard) if is_guard_safe(guard) => {
                    result.push(CArm {
                        pat,
                        guard: Some(self.lower_expr(guard)),
                        body: self.lower_expr(&arm.body),
                    });
                }
                Some(guard) => {
                    // Complex guard: desugar into the arm body.
                    // Remaining arms become the fallthrough.
                    let remaining = &arms[i + 1..];
                    let fallthrough = if remaining.is_empty() {
                        CExpr::Call(
                            "erlang".to_string(),
                            "error".to_string(),
                            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
                        )
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.to_string())),
                            self.lower_case_arms(scrut_var, remaining),
                        )
                    };

                    let guard_ce = self.lower_expr(guard);
                    let body_ce = self.lower_expr(&arm.body);
                    let complex_body = CExpr::Case(
                        Box::new(guard_ce),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: body_ce,
                            },
                            CArm {
                                pat: CPat::Wildcard,
                                guard: None,
                                body: fallthrough,
                            },
                        ],
                    );
                    result.push(CArm {
                        pat,
                        guard: None,
                        body: complex_body,
                    });
                    // Remaining arms are consumed into the fallthrough above.
                    break;
                }
            }
        }

        result
    }

    /// Lower a saturated constructor call to the appropriate Core Erlang form.
    pub(super) fn lower_ctor(&mut self, name: &str, args: Vec<&Expr>) -> CExpr {
        match name {
            "Nil" => CExpr::Nil,
            "Cons" if args.len() == 2 => {
                let head_var = self.fresh();
                let tail_var = self.fresh();
                let head_ce = self.lower_expr(args[0]);
                let tail_ce = self.lower_expr(args[1]);
                CExpr::Let(
                    head_var.clone(),
                    Box::new(head_ce),
                    Box::new(CExpr::Let(
                        tail_var.clone(),
                        Box::new(tail_ce),
                        Box::new(CExpr::Cons(
                            Box::new(CExpr::Var(head_var)),
                            Box::new(CExpr::Var(tail_var)),
                        )),
                    )),
                )
            }
            _ => {
                // ADT constructor: tagged tuple {name, arg1, arg2, ...}
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for arg in &args {
                    let var = self.fresh();
                    let val = self.lower_expr(arg);
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let mut elems = vec![CExpr::Lit(CLit::Atom(name.to_string()))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
        }
    }

    pub(super) fn lower_binop(&mut self, op: &BinOp, left: &Expr, right: &Expr) -> CExpr {
        match op {
            BinOp::And => return self.lower_short_circuit(left, right, true),
            BinOp::Or => return self.lower_short_circuit(left, right, false),
            _ => {}
        }

        let left_var = self.fresh();
        let right_var = self.fresh();
        let left_ce = self.lower_expr(left);
        let right_ce = self.lower_expr(right);
        let call = binop_call(op, &left_var, &right_var);

        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Let(
                right_var.clone(),
                Box::new(right_ce),
                Box::new(call),
            )),
        )
    }

    /// `a && b` -> `case a of true -> b; false -> false end`
    /// `a || b` -> `case a of true -> true; false -> b end`
    fn lower_short_circuit(&mut self, left: &Expr, right: &Expr, and: bool) -> CExpr {
        let left_var = self.fresh();
        let left_ce = self.lower_expr(left);
        let right_ce = self.lower_expr(right);
        let short_val = CExpr::Lit(CLit::Atom(if and { "false" } else { "true" }.to_string()));
        let (true_arm, false_arm) = if and {
            (right_ce, short_val)
        } else {
            (short_val, right_ce)
        };
        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(left_var)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: true_arm,
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: false_arm,
                    },
                ],
            )),
        )
    }

    pub(super) fn lower_block(&mut self, stmts: &[Stmt]) -> CExpr {
        match stmts {
            [] => CExpr::Tuple(vec![]), // unit
            [Stmt::Expr(e)] => self.lower_expr(e),
            [Stmt::Let { pattern, value, .. }] => {
                let var = pat_binding_var(pattern).unwrap_or_else(|| self.fresh());
                let val_ce = self.lower_expr(value);
                CExpr::Let(var.clone(), Box::new(val_ce), Box::new(CExpr::Var(var)))
            }
            [first, rest @ ..] => {
                // Check if the first statement contains an effect call -- if so, CPS transform:
                // everything in `rest` becomes the continuation closure K.
                // Effect calls may be bare (EffectCall) or wrapped in App nodes
                // (App(EffectCall, arg1), arg2, ...).
                let effect_info = match first {
                    Stmt::Expr(e) => {
                        collect_effect_call(e).map(|(name, qual, args)| (None, name, qual, args))
                    }
                    Stmt::Let { pattern, value, .. } => collect_effect_call(value)
                        .map(|(name, qual, args)| (Some(pattern), name, qual, args)),
                };

                if let Some((pat, op_name, qualifier, args)) = effect_info {
                    let rest_ce = self.lower_block(rest);
                    let k_param = match pat {
                        Some(p) => pat_binding_var(p).unwrap_or_else(|| self.fresh()),
                        None => self.fresh(), // expression position: unused param
                    };
                    let k = CExpr::Fun(vec![k_param], Box::new(rest_ce));
                    // We need to own the args for lower_effect_call
                    let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                    self.lower_effect_call(op_name, qualifier, &args_owned, Some(k))
                } else {
                    // Normal (non-effect) statement
                    let (var, val_ce) = match first {
                        Stmt::Let { pattern, value, .. } => {
                            let var = pat_binding_var(pattern).unwrap_or_else(|| self.fresh());
                            (var, self.lower_expr(value))
                        }
                        Stmt::Expr(e) => {
                            let var = self.fresh();
                            (var, self.lower_expr(e))
                        }
                    };
                    let rest_ce = self.lower_block(rest);
                    CExpr::Let(var, Box::new(val_ce), Box::new(rest_ce))
                }
            }
        }
    }

    /// Bind each element to a fresh variable, then build a tuple.
    /// Used for both tuple literals and record/constructor field lists.
    /// Lower a `do { Pat <- expr ... success } else { arms }` expression.
    ///
    /// Desugars to nested case expressions: each binding is a case on the
    /// scrutinee; a successful pattern match continues to the next binding,
    /// a mismatch routes the raw value to the else arms.
    pub(super) fn lower_do(
        &mut self,
        bindings: &[(Pat, Expr)],
        success: &Expr,
        else_arms: &[CaseArm],
    ) -> CExpr {
        // Pre-lower the else arms once; clone them at each failure point.
        let else_arms_ce: Vec<CArm> = else_arms
            .iter()
            .map(|arm| CArm {
                pat: lower_pat(&arm.pattern, &self.record_fields),
                guard: arm.guard.as_ref().map(|g| self.lower_expr(g)),
                body: self.lower_expr(&arm.body),
            })
            .collect();

        // Build from the innermost binding outward.
        let mut inner = self.lower_expr(success);

        for (pat, expr) in bindings.iter().rev() {
            let scrut_var = self.fresh();
            let fail_var = self.fresh();
            let val_ce = self.lower_expr(expr);

            let case_expr = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat: lower_pat(pat, &self.record_fields),
                        guard: None,
                        body: inner,
                    },
                    CArm {
                        pat: CPat::Var(fail_var.clone()),
                        guard: None,
                        body: CExpr::Case(Box::new(CExpr::Var(fail_var)), else_arms_ce.clone()),
                    },
                ],
            );
            inner = CExpr::Let(scrut_var, Box::new(val_ce), Box::new(case_expr));
        }

        inner
    }

    pub(super) fn lower_tuple_elems(&mut self, elems: &[Expr]) -> CExpr {
        let mut vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for elem in elems {
            let var = self.fresh();
            let val = self.lower_expr(elem);
            vars.push(var.clone());
            bindings.push((var, val));
        }
        let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
        bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    // --- Effect system (CPS transform) ---

    /// Lower an effect call: `op! args`.
    ///
    /// Emits: `apply Handler('op', arg1, ..., argN, K)`
    ///
    /// If `continuation` is Some, it's the pre-built K closure. If None
    /// (standalone effect call not in a block), we use an identity continuation.
    pub(super) fn lower_effect_call(
        &mut self,
        op_name: &str,
        qualifier: Option<&str>,
        args: &[Expr],
        continuation: Option<CExpr>,
    ) -> CExpr {
        // Find which effect this op belongs to
        let effect_name = if let Some(q) = qualifier {
            q.to_string()
        } else {
            self.op_to_effect
                .get(op_name)
                .unwrap_or_else(|| panic!("unknown effect operation: {}", op_name))
                .clone()
        };

        // Find the handler param variable for this effect
        let handler_var = self
            .current_handler_params
            .get(&effect_name)
            .unwrap_or_else(|| {
                panic!(
                    "effect '{}' used but no handler param in scope (op: {})",
                    effect_name, op_name
                )
            })
            .clone();

        // Build: apply Handler('op', arg1, ..., argN, K)
        let mut call_args = vec![CExpr::Lit(CLit::Atom(op_name.to_string()))];
        let mut bindings = Vec::new();
        for arg in args {
            let v = self.fresh();
            let ce = self.lower_expr(arg);
            bindings.push((v.clone(), ce));
            call_args.push(CExpr::Var(v));
        }

        // Append continuation
        let k = continuation.unwrap_or_else(|| {
            // Identity continuation for standalone effect calls
            let param = self.fresh();
            CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)))
        });
        call_args.push(k);

        let apply = CExpr::Apply(Box::new(CExpr::Var(handler_var)), call_args);

        // Wrap with let-bindings for args
        bindings.into_iter().rev().fold(apply, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    /// Lower a `with` expression: `expr with handler`.
    ///
    /// Builds handler function(s) from the handler definition and passes them
    /// as extra parameters to the effectful computation.
    pub(super) fn lower_with(&mut self, expr: &Expr, handler: &Handler) -> CExpr {
        // Resolve all handler arms, return clause, and which effects are handled
        let (all_arms, return_clause, handled_effects) = self.resolve_handler(handler);

        // Build a handler function for each effect.
        // Group arms by their effect.
        let mut effect_arms: std::collections::HashMap<String, Vec<&HandlerArm>> =
            std::collections::HashMap::new();
        for arm in &all_arms {
            let eff = self
                .op_to_effect
                .get(&arm.op_name)
                .unwrap_or_else(|| panic!("unknown effect op in handler: {}", arm.op_name))
                .clone();
            effect_arms.entry(eff).or_default().push(arm);
        }

        // For each handled effect, build a handler function and bind it.
        // Two passes: first set up all handler param names (so handler arm bodies
        // that use effects from sibling handlers can find them via closure capture),
        // then build the handler functions.
        let saved_handler_params = self.current_handler_params.clone();

        // Pass 1: register all handler param variables
        let mut handler_vars: Vec<(String, String)> = Vec::new(); // (effect_name, var_name)
        for effect_name in &handled_effects {
            let handler_var = format!("_Handle{}", effect_name);
            self.current_handler_params
                .insert(effect_name.clone(), handler_var.clone());
            handler_vars.push((effect_name.clone(), handler_var));
        }

        // Pass 2: build handler functions (arm bodies can now reference any handler param)
        let mut handler_bindings: Vec<(String, CExpr)> = Vec::new();
        for (effect_name, handler_var) in &handler_vars {
            let arms = effect_arms.get(effect_name).cloned().unwrap_or_default();
            let handler_fun = self.build_handler_fun(&arms);
            handler_bindings.push((handler_var.clone(), handler_fun));
        }

        // Lower the inner expression with the handler params in scope
        let inner_ce = self.lower_expr(expr);

        // Apply return clause wrapper if present.
        // NOTE: This wraps unconditionally, which means handler aborts also
        // pass through the return clause. A proper fix would integrate the
        // return clause into the CPS continuation chain so aborts bypass it.
        let result = if let Some(ret) = &return_clause {
            let ret_var = self.fresh();
            let param = if ret.params.is_empty() {
                self.fresh()
            } else {
                core_var(&ret.params[0])
            };
            let ret_body = self.lower_expr(&ret.body);
            let ret_fn = CExpr::Fun(vec![param], Box::new(ret_body));
            CExpr::Let(
                ret_var.clone(),
                Box::new(inner_ce),
                Box::new(CExpr::Apply(Box::new(ret_fn), vec![CExpr::Var(ret_var)])),
            )
        } else {
            inner_ce
        };

        self.current_handler_params = saved_handler_params;

        // Wrap with handler bindings
        handler_bindings
            .into_iter()
            .rev()
            .fold(result, |body, (var, val)| {
                CExpr::Let(var, Box::new(val), Box::new(body))
            })
    }

    /// Build a handler function from a set of arms for a single effect.
    ///
    /// Produces: `fun (Op, Arg1, ..., K) -> case Op of 'op1' -> ...; 'op2' -> ... end`
    fn build_handler_fun(&mut self, arms: &[&HandlerArm]) -> CExpr {
        if arms.is_empty() {
            // Shouldn't happen, but degenerate case
            let k_param = "_K".to_string();
            return CExpr::Fun(
                vec!["_Op".to_string(), k_param.clone()],
                Box::new(CExpr::Apply(
                    Box::new(CExpr::Var(k_param)),
                    vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
                )),
            );
        }

        // Find the maximum param count across all arms
        let max_params = arms.iter().map(|a| a.params.len()).max().unwrap_or(0);

        // Handler function params: Op, Param1, ..., ParamN, K
        let op_var = "_Op".to_string();
        let k_var = "_K".to_string();
        let param_vars: Vec<String> = (0..max_params).map(|i| format!("_HArg{}", i)).collect();

        let mut fun_params = vec![op_var.clone()];
        fun_params.extend(param_vars.iter().cloned());
        fun_params.push(k_var);

        // Build case arms on the op atom
        let case_arms: Vec<CArm> = arms
            .iter()
            .map(|arm| {
                // Bind arm params from handler arg vars
                let mut body_ce = self.lower_expr(&arm.body);
                // Bind arm's named params to the positional handler args
                for (i, param_name) in arm.params.iter().enumerate().rev() {
                    body_ce = CExpr::Let(
                        core_var(param_name),
                        Box::new(CExpr::Var(param_vars[i].clone())),
                        Box::new(body_ce),
                    );
                }
                CArm {
                    pat: CPat::Lit(CLit::Atom(arm.op_name.clone())),
                    guard: None,
                    body: body_ce,
                }
            })
            .collect();

        let case_expr = CExpr::Case(Box::new(CExpr::Var(op_var)), case_arms);
        CExpr::Fun(fun_params, Box::new(case_expr))
    }

    /// Resolve a Handler into a flat list of arms, optional return clause,
    /// and the set of handled effects.
    fn resolve_handler(
        &self,
        handler: &Handler,
    ) -> (Vec<HandlerArm>, Option<Box<HandlerArm>>, Vec<String>) {
        match handler {
            Handler::Named(name) => {
                let info = self
                    .handler_defs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown handler: {}", name));
                (
                    info.arms.clone(),
                    info.return_clause.clone(),
                    info.effects.clone(),
                )
            }
            Handler::Inline {
                named,
                arms,
                return_clause,
            } => {
                let mut all_arms = Vec::new();
                let mut resolved_return = return_clause.clone();
                let mut handled_effects = Vec::new();

                for name in named {
                    let info = self
                        .handler_defs
                        .get(name)
                        .unwrap_or_else(|| panic!("unknown handler: {}", name));
                    all_arms.extend(info.arms.iter().cloned());
                    handled_effects.extend(info.effects.iter().cloned());
                    if resolved_return.is_none() {
                        resolved_return = info.return_clause.clone();
                    }
                }

                all_arms.extend(arms.iter().cloned());

                // Determine effects from inline arms
                for arm in arms {
                    if let Some(eff) = self.op_to_effect.get(&arm.op_name)
                        && !handled_effects.contains(eff)
                    {
                        handled_effects.push(eff.clone());
                    }
                }

                (all_arms, resolved_return, handled_effects)
            }
        }
    }
}
