pub(crate) mod builtins;
pub(crate) mod module;
pub(crate) mod value;

pub use module::ModuleLoader;
pub use value::{ClosureArm, EvalError, EvalResult, HandlerVal, Value};

use crate::ast::*;
use builtins::{parse_prelude, register_builtins};
use module::load_module;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use value::{Continuation, Env};

// --- Expressions ---

pub fn eval_expr(expr: &Expr, env: &Env) -> EvalResult {
    match expr {
        Expr::Lit { value, .. } => match value {
            Lit::Int(n) => EvalResult::Ok(Value::Int(*n)),
            Lit::Float(n) => EvalResult::Ok(Value::Float(*n)),
            Lit::String(s) => EvalResult::Ok(Value::String(s.clone())),
            Lit::Bool(b) => EvalResult::Ok(Value::Bool(*b)),
            Lit::Unit => EvalResult::Ok(Value::Unit),
        },

        Expr::Var { name, .. } => match env.get(name) {
            Some(value) => EvalResult::Ok(value),
            None => EvalResult::error(format!("Undefined variable: {}", name)),
        },

        Expr::BinOp {
            op, left, right, ..
        } => {
            let op = op.clone();
            let right = right.clone();
            let env = env.clone();
            eval_expr(left, &env).then(move |left_val| {
                eval_expr(&right, &env).then(move |right_val| eval_binop(&op, left_val, right_val))
            })
        }

        Expr::App { func, arg, .. } => {
            let arg = arg.clone();
            let env = env.clone();
            eval_expr(func, &env).then(move |f| eval_expr(&arg, &env).then(move |a| apply(f, a)))
        }

        Expr::UnaryMinus { expr, .. } => eval_expr(expr, env).then(|val| match val {
            Value::Int(n) => EvalResult::Ok(Value::Int(-n)),
            Value::Float(n) => EvalResult::Ok(Value::Float(-n)),
            _ => EvalResult::error("Unary minus requires a number"),
        }),

        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            let then_branch = then_branch.clone();
            let else_branch = else_branch.clone();
            let env = env.clone();
            eval_expr(cond, &env).then(move |cond_val| match cond_val {
                Value::Bool(true) => eval_expr(&then_branch, &env),
                Value::Bool(false) => eval_expr(&else_branch, &env),
                other => EvalResult::error(format!(
                    "If condition must evaluate to a Boolean, got: {}",
                    other
                )),
            })
        }

        Expr::Constructor { name, .. } => match env.get(name) {
            Some(val) => EvalResult::Ok(val),
            None => EvalResult::error(format!("undefined constructor: {}", name)),
        },

        Expr::Lambda { params, body, .. } => EvalResult::Ok(Value::Closure(vec![ClosureArm {
            params: params.clone(),
            body: *body.clone(),
            guard: None,
            env: env.clone(),
        }])),

        // Evaluate each expression in sequence in a new scope
        Expr::Block { stmts, .. } => {
            let block_env = env.extend();
            let stmts = stmts.clone();
            eval_block_stmts(&stmts, 0, &block_env)
        }

        Expr::Case {
            scrutinee, arms, ..
        } => {
            let arms = arms.clone();
            let env = env.clone();
            eval_expr(scrutinee, &env).then(move |val| eval_case_arms(&arms, &val, &env, 0))
        }

        Expr::FieldAccess { expr, field, .. } => {
            let field = field.clone();
            eval_expr(expr, env).then(move |val| match val {
                Value::Record { fields, .. } => match fields.get(&field) {
                    Some(val) => EvalResult::Ok(val.clone()),
                    None => EvalResult::error(format!("Record has no field '{}'", field)),
                },
                other => EvalResult::error(format!("Cannot access field '{}' on {}", field, other)),
            })
        }

        Expr::RecordCreate { name, fields, .. } => {
            let name = name.clone();
            let fields = fields.clone();
            let env = env.clone();
            eval_record_fields(&fields, 0, HashMap::new(), &env, move |record_fields| {
                EvalResult::Ok(Value::Record {
                    name,
                    fields: record_fields,
                })
            })
        }

        Expr::RecordUpdate { record, fields, .. } => {
            let fields = fields.clone();
            let env = env.clone();
            eval_expr(record, &env).then(move |val| match val {
                Value::Record {
                    name,
                    fields: mut record_fields,
                } => eval_record_fields(&fields, 0, HashMap::new(), &env, move |new_fields| {
                    record_fields.extend(new_fields);
                    EvalResult::Ok(Value::Record {
                        name,
                        fields: record_fields,
                    })
                }),
                other => EvalResult::error(format!("Cannot update fields on {}", other)),
            })
        }

        Expr::EffectCall { name, args, .. } => {
            let func = match env.get(name) {
                Some(f) => f,
                None => {
                    return EvalResult::error(format!("Unknown effect operation: {}", name));
                }
            };
            let args = args.clone();
            let env = env.clone();
            eval_effect_args(func, &args, 0, &env)
        }

        Expr::With { expr, handler, .. } => {
            // Resolve the handler to its registered value
            let handler_val = match handler.as_ref() {
                Handler::Named(name) => match env.get(name) {
                    Some(Value::Handler(h)) => h,
                    _ => return EvalResult::error(format!("Unknown handler: {}", name)),
                },
                Handler::Inline {
                    arms,
                    return_clause,
                    ..
                } => HandlerVal {
                    arms: arms.clone(),
                    return_clause: return_clause.clone(),
                    env: env.clone(),
                },
            };

            // Deep handler: intercept effects, re-installing the handler after resume
            handle_effect(eval_expr(expr, env), &handler_val)
        }

        Expr::Resume { value, .. } => {
            let env = env.clone();
            let value = value.clone();
            eval_expr(&value, &env).then(move |val| match env.get("resume") {
                Some(Value::Continuation(cont)) => match cont.borrow_mut().take() {
                    Some(k) => k(val),
                    None => EvalResult::error("resume called more than once!"),
                },
                _ => EvalResult::error("resume used outside of a handler"),
            })
        }

        Expr::Tuple { elements, .. } => {
            let elements = elements.clone();
            let env = env.clone();
            eval_exprs(&elements, 0, Vec::new(), &env, |vals| {
                let arity = vals.len();
                EvalResult::Ok(Value::Constructor {
                    name: "Tuple".into(),
                    arity,
                    args: vals,
                })
            })
        }

        Expr::QualifiedName { module, name, .. } => {
            let key = format!("{}.{}", module, name);
            match env.get(&key) {
                Some(val) => EvalResult::Ok(val),
                None => EvalResult::error(format!("unknown qualified name '{}'", key)),
            }
        }

        Expr::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let bindings = bindings.clone();
            let success = success.clone();
            let else_arms = else_arms.clone();
            let env = env.clone();
            eval_do_expr(&bindings, 0, &success, &else_arms, &env)
        }
    }
}

// Deep handler: dispatches an effect to the matching handler arm, and wraps the
// continuation so the handler is re-installed when computation resumes.
fn handle_effect(result: EvalResult, handler_val: &HandlerVal) -> EvalResult {
    match result {
        EvalResult::Ok(val) => {
            // Apply return clause if present
            if let Some(ret_arm) = &handler_val.return_clause {
                let ret_env = handler_val.env.extend();
                if let Some(param_name) = ret_arm.params.first() {
                    ret_env.set(param_name.clone(), val);
                }
                eval_expr(&ret_arm.body, &ret_env)
            } else {
                EvalResult::Ok(val)
            }
        }
        EvalResult::Error(e) => EvalResult::Error(e),
        EvalResult::Effect {
            name,
            qualifier,
            args,
            continuation,
        } => {
            for arm in &handler_val.arms {
                if arm.op_name == name {
                    let handler_env = handler_val.env.extend();
                    for (param, arg) in arm.params.iter().zip(args.iter()) {
                        handler_env.set(param.clone(), arg.clone());
                    }

                    // Wrap the raw continuation so the handler is re-installed
                    // around the rest of the computation after resume
                    let hv = handler_val.clone();
                    let wrapped_k: Continuation =
                        Box::new(move |val| handle_effect(continuation(val), &hv));

                    let cont = Rc::new(RefCell::new(Some(wrapped_k)));
                    handler_env.set("resume".to_string(), Value::Continuation(cont));

                    return eval_expr(&arm.body, &handler_env);
                }
            }
            // No matching arm -- re-raise with continuation intact
            EvalResult::Effect {
                name,
                qualifier,
                args,
                continuation,
            }
        }
    }
}

// Helper: evaluate do...else bindings sequentially.
// When all bindings succeed, evaluate and return the success expression.
// On pattern mismatch, dispatch to else_arms like a case expression.
fn eval_do_expr(
    bindings: &[(Pat, Expr)],
    index: usize,
    success: &Expr,
    else_arms: &[CaseArm],
    env: &Env,
) -> EvalResult {
    if index >= bindings.len() {
        return eval_expr(success, env);
    }

    let (pat, expr) = &bindings[index];
    let pat = pat.clone();
    let bindings = bindings.to_vec();
    let success = success.clone();
    let else_arms = else_arms.to_vec();
    let env = env.clone();

    eval_expr(expr, &env).then(move |val| {
        if let Some(bound) = match_pattern(&pat, &val) {
            for (name, v) in bound {
                env.set(name, v);
            }
            eval_do_expr(&bindings, index + 1, &success, &else_arms, &env)
        } else {
            // Pattern mismatch: bail to else arms
            eval_case_arms(&else_arms, &val, &env, 0)
        }
    })
}

// Helper: evaluate block statements sequentially, threading effects through continuations
fn eval_block_stmts(stmts: &[Stmt], index: usize, env: &Env) -> EvalResult {
    if index >= stmts.len() {
        return EvalResult::Ok(Value::Unit);
    }

    let is_last = index == stmts.len() - 1;

    match &stmts[index] {
        Stmt::Let { pattern, value, .. } => {
            let pattern = pattern.clone();
            let stmts = stmts.to_vec();
            let env = env.clone();
            eval_expr(value, &env).then(move |val| {
                if let Some(bindings) = match_pattern(&pattern, &val) {
                    for (name, val) in bindings {
                        env.set(name, val);
                    }
                }
                eval_block_stmts(&stmts, index + 1, &env)
            })
        }
        Stmt::Expr(expr) => {
            if is_last {
                eval_expr(expr, env)
            } else {
                let stmts = stmts.to_vec();
                let env = env.clone();
                eval_expr(expr, &env).then(move |_| eval_block_stmts(&stmts, index + 1, &env))
            }
        }
    }
}

// Helper: evaluate record fields sequentially
fn eval_record_fields(
    fields: &[(String, Expr)],
    index: usize,
    mut acc: HashMap<String, Value>,
    env: &Env,
    finish: impl FnOnce(HashMap<String, Value>) -> EvalResult + 'static,
) -> EvalResult {
    if index >= fields.len() {
        return finish(acc);
    }

    let field_name = fields[index].0.clone();
    let fields = fields.to_vec();
    let env = env.clone();
    eval_expr(&fields[index].1, &env).then(move |val| {
        acc.insert(field_name, val);
        eval_record_fields(&fields, index + 1, acc, &env, finish)
    })
}

// Helper: evaluate a list of expressions into a Vec<Value>
fn eval_exprs(
    exprs: &[Expr],
    index: usize,
    mut acc: Vec<Value>,
    env: &Env,
    finish: impl FnOnce(Vec<Value>) -> EvalResult + 'static,
) -> EvalResult {
    if index >= exprs.len() {
        return finish(acc);
    }
    let exprs = exprs.to_vec();
    let env = env.clone();
    eval_expr(&exprs[index], &env).then(move |val| {
        acc.push(val);
        eval_exprs(&exprs, index + 1, acc, &env, finish)
    })
}

// Helper: evaluate effect call args sequentially and apply
fn eval_effect_args(func: Value, args: &[Expr], index: usize, env: &Env) -> EvalResult {
    if index >= args.len() {
        return EvalResult::Ok(func);
    }

    let args = args.to_vec();
    let env = env.clone();
    eval_expr(&args[index], &env).then(move |val| {
        apply(func, val).then(move |result| eval_effect_args(result, &args, index + 1, &env))
    })
}

// --- Function application ---

fn apply(func: Value, arg: Value) -> EvalResult {
    match func {
        Value::Closure(closure_arms) => {
            // If still currying (more than 1 param), bind first param in all arms
            // and return a new closure with the remaining params
            if closure_arms.first().is_some_and(|a| a.params.len() > 1) {
                let mut remaining_arms = Vec::new();
                for arm in &closure_arms {
                    if let Some(bindings) = match_pattern(&arm.params[0], &arg) {
                        let env = arm.env.extend();
                        for (name, val) in bindings {
                            env.set(name, val);
                        }
                        remaining_arms.push(ClosureArm {
                            params: arm.params[1..].to_vec(),
                            body: arm.body.clone(),
                            guard: arm.guard.clone(),
                            env,
                        });
                    }
                }
                if remaining_arms.is_empty() {
                    EvalResult::error("Non-exhaustive patterns in function")
                } else {
                    EvalResult::Ok(Value::Closure(remaining_arms))
                }
            } else {
                // Last param -- try each arm until one matches (with guard)
                for arm in &closure_arms {
                    let Some(bindings) = match_pattern(&arm.params[0], &arg) else {
                        continue;
                    };

                    let local_env = arm.env.extend();
                    for (name, val) in bindings {
                        local_env.set(name, val);
                    }

                    if let Some(guard) = &arm.guard {
                        // Guards in apply can't use `then` with `continue`, so we
                        // only support pure (non-effectful) guard expressions here.
                        match eval_expr(guard, &local_env) {
                            EvalResult::Ok(Value::Bool(true)) => {}
                            EvalResult::Ok(Value::Bool(false)) => continue,
                            EvalResult::Ok(other) => {
                                return EvalResult::error(format!(
                                    "Guard must be a Bool, got: {}",
                                    other
                                ));
                            }
                            EvalResult::Error(e) => return EvalResult::Error(e),
                            EvalResult::Effect { .. } => {
                                return EvalResult::error(
                                    "Effects in function guards are not supported",
                                );
                            }
                        }
                    }
                    return eval_expr(&arm.body, &local_env);
                }

                EvalResult::error("Non-exhaustive patterns in function")
            }
        }

        Value::Constructor {
            name,
            arity,
            mut args,
        } => {
            args.push(arg);
            if args.len() > arity {
                EvalResult::error(format!(
                    "Constructor {} expects {} args, got {}.",
                    name,
                    arity,
                    args.len()
                ))
            } else {
                EvalResult::Ok(Value::Constructor { name, arity, args })
            }
        }

        Value::BuiltIn(name) => eval_builtin(&name, arg),

        Value::TraitMethod {
            trait_name,
            method_name,
            env,
        } => {
            let raw_name = value::value_type_name(&arg);
            // Constructors return their own name (e.g. "Some"), not the type name ("Option").
            // Look up __ctor_type_{name} entries stored during TypeDef eval to resolve.
            let type_name = env
                .get(&format!("__ctor_type_{}", raw_name))
                .and_then(|v| match v {
                    Value::String(s) => Some(s),
                    _ => None,
                })
                .unwrap_or(raw_name);
            let key = format!("__impl_{}_{}_{}", trait_name, type_name, method_name);
            if let Some(impl_fn) = env.get(&key) {
                apply(impl_fn, arg)
            } else if trait_name == "Show" && method_name == "print" {
                // print: call show dispatch then println the result
                apply(
                    Value::TraitMethod {
                        trait_name: "Show".into(),
                        method_name: "show".into(),
                        env: env.clone(),
                    },
                    arg,
                )
                .then(|s| {
                    if let Value::String(s) = s {
                        println!("{}", s);
                    }
                    EvalResult::Ok(Value::Unit)
                })
            } else if trait_name == "Show" && method_name == "show" {
                // Built-in Show fallback for primitives and types without a custom impl.
                EvalResult::Ok(Value::String(format!("{}", arg)))
            } else {
                EvalResult::error(format!("no impl of {} for type {}", trait_name, type_name))
            }
        }

        // Effect ops accumulate args like constructors, but fire a signal instead of returning a value
        Value::EffectFn {
            name,
            qualifier,
            arity,
            mut args,
        } => {
            args.push(arg);
            if args.len() >= arity {
                EvalResult::Effect {
                    name,
                    qualifier,
                    args,
                    continuation: Box::new(EvalResult::Ok), // identity; caller composes via .then()
                }
            } else {
                EvalResult::Ok(Value::EffectFn {
                    name,
                    qualifier,
                    arity,
                    args,
                })
            }
        }

        not_a_func => EvalResult::error(format!("Cannot call {} as a function", not_a_func)),
    }
}

// --- Declarations ---

pub fn eval_decl(decl: &Decl, env: &Env, loader: &ModuleLoader) -> EvalResult {
    match decl {
        // Ignored at runtime
        Decl::FunAnnotation { .. } => EvalResult::Ok(Value::Unit),
        Decl::ModuleDecl { .. } => EvalResult::Ok(Value::Unit),
        Decl::TraitDef { name, methods, .. } => {
            for method in methods {
                env.set(
                    method.name.clone(),
                    Value::TraitMethod {
                        trait_name: name.clone(),
                        method_name: method.name.clone(),
                        env: env.clone(),
                    },
                );
            }
            EvalResult::Ok(Value::Unit)
        }

        Decl::Let { name, value, .. } => {
            let name = name.clone();
            let env = env.clone();
            eval_expr(value, &env).then(move |val| {
                env.set(name, val);
                EvalResult::Ok(Value::Unit)
            })
        }

        Decl::FunBinding {
            name,
            params,
            guard,
            body,
            ..
        } => {
            let arm = ClosureArm {
                params: params.clone(),
                guard: guard.clone().map(|g| *g),
                body: body.clone(),
                env: env.clone(),
            };

            if let Some(Value::Closure(mut arms)) = env.get(name) {
                arms.push(arm);
                env.set(name.clone(), Value::Closure(arms));
            } else {
                env.set(name.clone(), Value::Closure(vec![arm]));
            }

            EvalResult::Ok(Value::Unit)
        }

        Decl::TypeDef { name, variants, .. } => {
            for v in variants {
                let arity = v.fields.len();
                env.set(
                    v.name.clone(),
                    Value::Constructor {
                        name: v.name.clone(),
                        arity,
                        args: Vec::new(),
                    },
                );
                // Map constructor name -> type name for trait dispatch.
                // Use set_root so TraitMethod lookups (which captured an ancestor env) can find it.
                env.set_root(
                    format!("__ctor_type_{}", v.name),
                    Value::String(name.clone()),
                );
            }
            EvalResult::Ok(Value::Unit)
        }

        // Handled at the call site
        Decl::RecordDef { .. } => EvalResult::Ok(Value::Unit),

        Decl::EffectDef {
            name, operations, ..
        } => {
            for op in operations {
                let val = Value::EffectFn {
                    name: op.name.clone(),
                    qualifier: Some(name.clone()),
                    arity: op.params.len(),
                    args: vec![],
                };
                env.set(op.name.clone(), val);
            }
            EvalResult::Ok(Value::Unit)
        }

        Decl::HandlerDef {
            name,
            arms,
            return_clause,
            ..
        } => {
            let handler = HandlerVal {
                arms: arms.clone(),
                return_clause: return_clause.clone(),
                env: env.clone(),
            };
            env.set(name.clone(), Value::Handler(handler));
            EvalResult::Ok(Value::Unit)
        }

        Decl::ImplDef {
            trait_name,
            target_type,
            methods,
            ..
        } => {
            for (method_name, params, body) in methods {
                // Store as a closure under a mangled name: __impl_Show_User_show
                let key = format!("__impl_{}_{}_{}", trait_name, target_type, method_name);
                let arm = ClosureArm {
                    params: params.clone(),
                    guard: None,
                    body: body.clone(),
                    env: env.clone(),
                };
                // Use set_root so TraitMethod lookups that captured an ancestor
                // env (e.g. the built-in `show`) can find this impl.
                env.set_root(key, Value::Closure(vec![arm]));
            }
            EvalResult::Ok(Value::Unit)
        }

        Decl::Import {
            module_path,
            alias,
            exposing,
            ..
        } => load_module(
            module_path,
            alias.as_deref(),
            exposing.as_deref(),
            env,
            loader,
        ),
    }
}

// --- Builtin functions ---

fn eval_builtin(name: &str, arg: Value) -> EvalResult {
    match name {
        "print" => {
            println!("{}", arg);
            EvalResult::Ok(Value::Unit)
        }
        "show" => EvalResult::Ok(Value::String(format!("{}", arg))),
        "panic" => EvalResult::error(format!("panic: {}", arg)),
        "todo" => EvalResult::error(format!("not implemented: {}", arg)),
        _ => EvalResult::error(format!("Unknown builtin {}", name)),
    }
}

// --- Binary operators ---

fn eval_binop(op: &BinOp, left: Value, right: Value) -> EvalResult {
    match (op, &left, &right) {
        // Boolean operators
        (BinOp::And, Value::Bool(false), _) => EvalResult::Ok(Value::Bool(false)),
        (BinOp::And, Value::Bool(true), Value::Bool(true)) => EvalResult::Ok(Value::Bool(true)),
        (BinOp::And, Value::Bool(_), Value::Bool(_)) => EvalResult::Ok(Value::Bool(false)),

        (BinOp::Or, Value::Bool(true), _) => EvalResult::Ok(Value::Bool(true)),
        (BinOp::Or, _, Value::Bool(true)) => EvalResult::Ok(Value::Bool(true)),
        (BinOp::Or, Value::Bool(_), Value::Bool(_)) => EvalResult::Ok(Value::Bool(false)),

        // Integer arithmetic
        (BinOp::Add, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Int(a + b)),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Int(a - b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Int(a * b)),
        (BinOp::Div, Value::Int(_), Value::Int(0)) => EvalResult::error("division by zero"),
        (BinOp::Div, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Int(a / b)),
        (BinOp::Mod, Value::Int(_), Value::Int(0)) => EvalResult::error("modulo by zero"),
        (BinOp::Mod, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Int(a % b)),

        // Integer comparison
        (BinOp::Eq, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Bool(a == b)),
        (BinOp::NotEq, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Bool(a != b)),
        (BinOp::Lt, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Bool(a < b)),
        (BinOp::Gt, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Bool(a > b)),
        (BinOp::LtEq, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Bool(a <= b)),
        (BinOp::GtEq, Value::Int(a), Value::Int(b)) => EvalResult::Ok(Value::Bool(a >= b)),

        // Float arithmetic
        (BinOp::Add, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Float(a + b)),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Float(a - b)),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Float(a * b)),
        (BinOp::Div, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Float(a / b)),

        // Float comparison
        (BinOp::Eq, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Bool(a == b)),
        (BinOp::NotEq, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Bool(a != b)),
        (BinOp::Lt, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Bool(a < b)),
        (BinOp::Gt, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Bool(a > b)),
        (BinOp::LtEq, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Bool(a <= b)),
        (BinOp::GtEq, Value::Float(a), Value::Float(b)) => EvalResult::Ok(Value::Bool(a >= b)),

        // String equality
        (BinOp::Eq, Value::String(a), Value::String(b)) => EvalResult::Ok(Value::Bool(a == b)),
        (BinOp::NotEq, Value::String(a), Value::String(b)) => EvalResult::Ok(Value::Bool(a != b)),

        // String concatenation
        (BinOp::Concat, Value::String(a), Value::String(b)) => {
            EvalResult::Ok(Value::String(format!("{}{}", a, b)))
        }

        _ => EvalResult::error(format!("cannot apply {:?} to {} and {}", op, left, right)),
    }
}

fn eval_case_arms(arms: &[CaseArm], val: &Value, env: &Env, start: usize) -> EvalResult {
    for i in start..arms.len() {
        let arm = &arms[i];
        if let Some(bindings) = match_pattern(&arm.pattern, val) {
            let case_env = env.extend();
            for (name, value) in bindings {
                case_env.set(name, value);
            }

            if let Some(guard) = &arm.guard {
                let arm_body = arm.body.clone();
                let case_env2 = case_env.clone();
                let arms = arms.to_vec();
                let val = val.clone();
                let env = env.clone();
                return eval_expr(guard, &case_env).then(move |guard_val| match guard_val {
                    Value::Bool(true) => eval_expr(&arm_body, &case_env2),
                    Value::Bool(false) => eval_case_arms(&arms, &val, &env, i + 1),
                    other => {
                        EvalResult::error(format!("Guard must evaluate to a Bool, got: {}", other))
                    }
                });
            }

            return eval_expr(&arm.body, &case_env);
        }
    }

    EvalResult::error(format!("No pattern matched for {}", val))
}

pub(crate) fn match_pattern(pattern: &Pat, value: &Value) -> Option<HashMap<String, Value>> {
    match pattern {
        Pat::Wildcard { .. } => Some(HashMap::new()),

        Pat::Var { name, .. } => Some(HashMap::from([(name.clone(), value.clone())])),

        Pat::Lit { value: lit, .. } => match (lit, value) {
            (Lit::Unit, Value::Unit) => Some(HashMap::new()),
            (Lit::Int(n1), Value::Int(n2)) if n1 == n2 => Some(HashMap::new()),
            // Pattern matching uses structural equality, not IEEE numeric equality.
            // NaN patterns match NaN values even though NaN != NaN in expressions.
            (Lit::Float(n1), Value::Float(n2)) if n1 == n2 || (n1.is_nan() && n2.is_nan()) => {
                Some(HashMap::new())
            }
            (Lit::Bool(b1), Value::Bool(b2)) if b1 == b2 => Some(HashMap::new()),
            (Lit::String(s1), Value::String(s2)) if s1 == s2 => Some(HashMap::new()),
            _ => None,
        },

        Pat::Constructor {
            name: pname,
            args: pargs,
            ..
        } => match value {
            Value::Constructor {
                name: vname,
                args: vargs,
                ..
            } => {
                // Strip module prefix from pattern name: `Shapes.Circle` matches value `Circle`
                let pbase = pname.rsplit('.').next().unwrap_or(pname);
                if pbase != vname || pargs.len() != vargs.len() {
                    return None;
                }

                let mut all_bindings = HashMap::new();
                for (pat, val) in pargs.iter().zip(vargs.iter()) {
                    let bindings = match_pattern(pat, val)?;
                    all_bindings.extend(bindings);
                }
                Some(all_bindings)
            }
            _ => None,
        },

        Pat::Record {
            name: pname,
            fields: pfields,
            ..
        } => match value {
            Value::Record {
                name: vname,
                fields: vfields,
            } if pname == vname => {
                let mut all_bindings = HashMap::new();
                for (field_name, maybe_pat) in pfields {
                    let field_value = vfields.get(field_name)?;
                    let bindings = match maybe_pat {
                        None => HashMap::from([(field_name.clone(), field_value.clone())]),
                        Some(pat) => match_pattern(pat, field_value)?,
                    };
                    all_bindings.extend(bindings);
                }
                Some(all_bindings)
            }
            _ => None,
        },

        Pat::Tuple { elements, .. } => match value {
            Value::Constructor { name, args, .. }
                if name == "Tuple" && args.len() == elements.len() =>
            {
                let mut all_bindings = HashMap::new();
                for (pat, val) in elements.iter().zip(args.iter()) {
                    let bindings = match_pattern(pat, val)?;
                    all_bindings.extend(bindings);
                }
                Some(all_bindings)
            }
            _ => None,
        },
    }
}

// Helper to run eval_decl for a list of declarations
pub(crate) fn eval_decls(
    decls: &[Decl],
    index: usize,
    env: &Env,
    loader: &ModuleLoader,
) -> EvalResult {
    if index >= decls.len() {
        return EvalResult::Ok(Value::Unit);
    }
    let env = env.clone();
    let loader = loader.clone();
    let decls_vec: Vec<Decl> = decls.to_vec();
    eval_decl(&decls_vec[index], &env, &loader)
        .then(move |_| eval_decls(&decls_vec, index + 1, &env, &loader))
}

pub fn eval_program(program: &Program, loader: &ModuleLoader) -> EvalResult {
    let base_env = Env::new();
    register_builtins(&base_env);

    let prelude = parse_prelude();
    let program = program.clone();
    let loader = loader.clone();
    eval_decls(&prelude, 0, &base_env, &loader).then(move |_| {
        // Cache base_env in the loader so imported modules extend it instead
        // of re-evaluating builtins + prelude from scratch.
        loader.0.borrow_mut().base_env = base_env.clone();

        // Main program gets its own child frame so its bindings don't
        // leak into imported modules (which share the same base_env).
        let main_env = base_env.extend();
        eval_decls(&program, 0, &main_env, &loader).then(move |_| match main_env.get("main") {
            Some(main_val @ Value::Closure(_)) => apply(main_val, Value::Unit),
            Some(_) => EvalResult::error("`main` must be a function"),
            None => EvalResult::error("No main function defined"),
        })
    })
}
