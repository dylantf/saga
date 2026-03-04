use crate::ast::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

#[derive(Clone)]
pub struct ClosureArm {
    pub params: Vec<Pat>,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub env: Env, // starts as definition-time env, grows as each arg is applied
}

#[derive(Clone)]
pub struct HandlerVal {
    pub arms: Vec<crate::ast::HandlerArm>,
    pub return_clause: Option<Box<crate::ast::HandlerArm>>,
    pub env: Env,
}

impl fmt::Display for HandlerVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<handler>")
    }
}

#[derive(Clone)]
pub enum Value {
    Unit,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),

    Closure(Vec<ClosureArm>),

    // ADT value constructor
    // E.g. Some(5) would be Constructor { name: "Some", arity: 1, args: [Int(5)]}
    Constructor {
        name: String,
        arity: usize,
        args: Vec<Value>,
    },

    Record {
        name: String,
        fields: HashMap<String, Value>,
    },

    EffectFn {
        name: String,
        qualifier: Option<String>,
        arity: usize,
        args: Vec<Value>,
    },

    Handler(HandlerVal),

    BuiltIn(String),
}

fn is_list_value(v: &Value) -> bool {
    match v {
        Value::Constructor { name, args, .. } if name == "Nil" && args.is_empty() => true,
        Value::Constructor { name, args, .. } if name == "Cons" && args.len() == 2 => {
            is_list_value(&args[1])
        }
        _ => false,
    }
}

fn fmt_list_elements(v: &Value, f: &mut fmt::Formatter<'_>, first: bool) -> fmt::Result {
    match v {
        Value::Constructor { name, args, .. } if name == "Nil" && args.is_empty() => Ok(()),
        Value::Constructor { name, args, .. } if name == "Cons" && args.len() == 2 => {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", args[0])?;
            fmt_list_elements(&args[1], f, false)
        }
        _ => Ok(()),
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Float(v) => write!(f, "{}", v),
            Value::String(s) => write!(f, "{}", s),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Unit => write!(f, "()"),
            Value::Closure { .. } => write!(f, "<function>"),
            Value::BuiltIn(name) => write!(f, "<built-in: {}>", name),
            Value::Constructor { name, args, .. } => {
                if name == "Nil" && args.is_empty() {
                    write!(f, "[]")
                } else if name == "Cons" && args.len() == 2 && is_list_value(self) {
                    write!(f, "[")?;
                    fmt_list_elements(self, f, true)?;
                    write!(f, "]")
                } else if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}(", name)?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")
                }
            }
            Value::Record { name, fields } => {
                write!(f, "{} {{", name)?;
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, " {}: {}", k, v)?;
                }
                write!(f, " }}")
            }
            Value::EffectFn { name, .. } => write!(f, "<effect-fn: {}>", name),
            Value::Handler(h) => write!(f, "{}", h),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

// --- Environment ---

#[derive(Clone)]
pub struct Env(Rc<RefCell<EnvInner>>);

struct EnvInner {
    bindings: HashMap<String, Value>,
    parent: Option<Env>,
}

impl Env {
    fn new() -> Self {
        Env(Rc::new(RefCell::new(EnvInner {
            bindings: HashMap::new(),
            parent: None,
        })))
    }

    fn extend(&self) -> Self {
        Env(Rc::new(RefCell::new(EnvInner {
            bindings: HashMap::new(),
            parent: Some(self.clone()),
        })))
    }

    fn get(&self, name: &str) -> Option<Value> {
        let inner = self.0.borrow();
        if let Some(val) = inner.bindings.get(name) {
            Some(val.clone())
        } else if let Some(parent) = &inner.parent {
            parent.get(name)
        } else {
            None
        }
    }

    fn set(&self, name: String, value: Value) {
        self.0.borrow_mut().bindings.insert(name, value);
    }
}

// --- Errors ---

#[derive(Debug)]
pub struct EvalError {
    pub message: String,
}

pub enum EvalSignal {
    Error(EvalError),
    Effect {
        name: String,
        qualifier: Option<String>,
        args: Vec<Value>,
    },
}

impl From<EvalError> for EvalSignal {
    fn from(e: EvalError) -> Self {
        EvalSignal::Error(e)
    }
}

impl EvalSignal {
    fn error(message: impl Into<String>) -> EvalSignal {
        EvalSignal::Error(EvalError {
            message: message.into(),
        })
    }
}

// --- Expressions ---

pub fn eval_expr(expr: &Expr, env: &Env) -> Result<Value, EvalSignal> {
    match expr {
        Expr::Lit { value, .. } => match value {
            Lit::Int(n) => Ok(Value::Int(*n)),
            Lit::Float(n) => Ok(Value::Float(*n)),
            Lit::String(s) => Ok(Value::String(s.clone())),
            Lit::Bool(b) => Ok(Value::Bool(*b)),
            Lit::Unit => Ok(Value::Unit),
        },

        Expr::Var { name, .. } => match env.get(name) {
            Some(value) => Ok(value),
            None => Err(EvalSignal::error(format!("Undefined variable: {}", name))),
        },

        Expr::BinOp {
            op, left, right, ..
        } => {
            let left_value = eval_expr(left, env)?;
            let right_value = eval_expr(right, env)?;
            eval_binop(op, left_value, right_value)
        }

        Expr::App { func, arg, .. } => {
            let f = eval_expr(func, env)?;
            let arg = eval_expr(arg, env)?;
            apply(f, arg)
        }

        Expr::UnaryMinus { expr, .. } => match eval_expr(expr, env)? {
            Value::Int(n) => Ok(Value::Int(-n)),
            Value::Float(n) => Ok(Value::Float(-n)),
            _ => Err(EvalSignal::error(
                "Unary minus requires a number".to_string(),
            )),
        },

        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => match eval_expr(cond, env)? {
            Value::Bool(true) => eval_expr(then_branch, env),
            Value::Bool(false) => eval_expr(else_branch, env),
            other => Err(EvalSignal::error(format!(
                "If condition must evaluate to a Boolean, got: {}",
                other
            ))),
        },

        Expr::Constructor { name, .. } => env
            .get(name)
            .ok_or_else(|| EvalSignal::error(format!("undefined constructor: {}", name))),

        Expr::Lambda { params, body, .. } => Ok(Value::Closure(vec![ClosureArm {
            params: params.clone(),
            body: *body.clone(),
            guard: None,
            env: env.clone(),
        }])),

        // Evaluate each expression in sequence in a new scope
        Expr::Block { stmts, .. } => {
            let block_env = env.extend();
            let mut result = Value::Unit;
            for stmt in stmts {
                result = match stmt {
                    Stmt::Let { name, value, .. } => {
                        let binding_value = eval_expr(value, &block_env)?;
                        block_env.set(name.clone(), binding_value);
                        Value::Unit // let-bindings don't evaluate to anything themselves
                    }
                    Stmt::Expr(expr) => eval_expr(expr, &block_env)?,
                }
            }
            Ok(result)
        }

        Expr::Case {
            scrutinee, arms, ..
        } => {
            let val = eval_expr(scrutinee, env)?;
            for arm in arms {
                if let Some(bindings) = match_pattern(&arm.pattern, &val) {
                    let case_env = env.extend();
                    for (name, value) in bindings {
                        case_env.set(name, value);
                    }

                    if let Some(guard) = &arm.guard {
                        match eval_expr(guard, &case_env)? {
                            Value::Bool(true) => {} // passed guard
                            Value::Bool(false) => continue,
                            other => {
                                return Err(EvalSignal::error(format!(
                                    "Guard must evaluate to a Bool, got: {}",
                                    other
                                )));
                            }
                        }
                    }

                    return eval_expr(&arm.body, &case_env);
                }
            }

            Err(EvalSignal::error(format!("No pattern matched for {}", val)))
        }

        Expr::FieldAccess { expr, field, .. } => match eval_expr(expr, env)? {
            Value::Record { fields, .. } => fields
                .get(field)
                .cloned()
                .ok_or_else(|| EvalSignal::error(format!("Record has no field '{}'", field))),
            other => Err(EvalSignal::error(format!(
                "Cannot access field '{}' on {}",
                field, other
            ))),
        },

        Expr::RecordCreate { name, fields, .. } => {
            let mut record_fields = HashMap::new();
            for (field_name, field_expr) in fields {
                record_fields.insert(field_name.clone(), eval_expr(field_expr, env)?);
            }
            Ok(Value::Record {
                name: name.clone(),
                fields: record_fields,
            })
        }

        Expr::RecordUpdate { record, fields, .. } => match eval_expr(record, env)? {
            Value::Record {
                name,
                fields: mut record_fields,
            } => {
                for (field_name, field_expr) in fields {
                    record_fields.insert(field_name.clone(), eval_expr(field_expr, env)?);
                }
                Ok(Value::Record {
                    name,
                    fields: record_fields,
                })
            }
            other => Err(EvalSignal::error(format!(
                "Cannot update fields on {}",
                other
            ))),
        },

        Expr::EffectCall { name, args, .. } => {
            let func = env
                .get(name)
                .ok_or_else(|| EvalSignal::error(format!("Unknown effect operation: {}", name)))?;

            let mut result = func;
            for arg in args {
                let val = eval_expr(arg, env)?;
                result = apply(result, val)?;
            }
            Ok(result)
        }

        Expr::With { expr, handler, .. } => {
            // Resolve the handler to its registered value
            let handler_val = match handler.as_ref() {
                Handler::Named(name) => match env.get(name) {
                    Some(Value::Handler(h)) => h,
                    _ => return Err(EvalSignal::error(format!("Unknown handler: {}", name))),
                },
                Handler::Inline { arms, .. } => HandlerVal {
                    arms: arms.clone(),
                    return_clause: None,
                    env: env.clone(),
                },
            };

            // Catch effect signals and bubble up to the right handler arm
            match eval_expr(expr, env) {
                Ok(val) => Ok(val),
                Err(EvalSignal::Effect { name, args, .. }) => {
                    for arm in &handler_val.arms {
                        if arm.op_name == name {
                            let handler_env = handler_val.env.extend();
                            for (param, arg) in arm.params.iter().zip(args.iter()) {
                                handler_env.set(param.clone(), arg.clone());
                            }
                            return eval_expr(&arm.body, &handler_env);
                        }
                    }
                    // No handler, just re-raise the signal
                    Err(EvalSignal::Effect {
                        name,
                        qualifier: None,
                        args,
                    })
                }
                Err(e) => {
                    // Regular errors just pass through
                    Err(e)
                }
            }
        }

        Expr::Resume { .. } => Err(EvalSignal::error(
            "resume not supported yet, abort-only mode :(",
        )),
    }
}

// --- Function application

fn apply(func: Value, arg: Value) -> Result<Value, EvalSignal> {
    match func {
        Value::Closure(closure_arms) => {
            // If still currying (more than 1 param), bind first param in all arms
            // and return a new closure with the remaining params
            if closure_arms.first().map_or(false, |a| a.params.len() > 1) {
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
                    Err(EvalSignal::error("Non-exhaustive patterns in function"))
                } else {
                    Ok(Value::Closure(remaining_arms))
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
                        match eval_expr(guard, &local_env)? {
                            Value::Bool(true) => {}
                            Value::Bool(false) => continue,
                            other => {
                                return Err(EvalSignal::error(format!(
                                    "Guard must be a Bool, got: {}",
                                    other
                                )));
                            }
                        }
                    }
                    return eval_expr(&arm.body, &local_env);
                }

                Err(EvalSignal::error("Non-exhaustive patterns in function"))
            }
        }

        Value::Constructor {
            name,
            arity,
            mut args,
        } => {
            args.push(arg);
            if args.len() > arity {
                Err(EvalSignal::error(format!(
                    "Constructor {} expects {} args, got {}.",
                    name,
                    arity,
                    args.len()
                )))
            } else {
                Ok(Value::Constructor { name, arity, args })
            }
        }

        Value::BuiltIn(name) => eval_builtin(&name, arg),

        // Effect ops accumulate args like constructors, but fire a signal instead of returning a value
        Value::EffectFn {
            name,
            qualifier,
            arity,
            mut args,
        } => {
            args.push(arg);
            if args.len() == arity {
                Err(EvalSignal::Effect {
                    name,
                    qualifier,
                    args,
                })
            } else {
                Ok(Value::EffectFn {
                    name,
                    qualifier,
                    arity,
                    args,
                })
            }
        }

        not_a_func => Err(EvalSignal::error(format!(
            "Cannot call {} as a function",
            not_a_func
        ))),
    }
}

// --- Declarations ---

pub fn eval_decl(decl: &Decl, env: &Env) -> Result<(), EvalSignal> {
    match decl {
        // Ignored at runtime
        Decl::FunAnnotation { .. } => Ok(()),
        Decl::ModuleDecl { .. } => Ok(()),
        Decl::TraitDef { .. } => Ok(()),

        Decl::Let { name, value, .. } => {
            let val = eval_expr(value, env)?;
            env.set(name.clone(), val);
            Ok(())
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

            Ok(())
        }

        Decl::TypeDef { variants, .. } => {
            for v in variants {
                let arity = v.fields.len();
                env.set(
                    v.name.clone(),
                    Value::Constructor {
                        name: v.name.clone(),
                        arity,
                        args: Vec::new(),
                    },
                )
            }
            Ok(())
        }

        // Handled at the call site
        Decl::RecordDef { .. } => Ok(()),

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
            Ok(())
        }

        Decl::HandlerDef { name, arms, .. } => {
            let handler = HandlerVal {
                arms: arms.clone(),
                return_clause: None,
                env: env.clone(),
            };
            env.set(name.clone(), Value::Handler(handler));
            Ok(())
        }

        Decl::ImplDef { .. } => todo!(),

        Decl::Import { .. } => todo!(),
    }
}

// --- Builtin functions

fn eval_builtin(name: &str, arg: Value) -> Result<Value, EvalSignal> {
    match name {
        "print" => {
            println!("{}", arg);
            Ok(Value::Unit)
        }
        "show" => Ok(Value::String(format!("{}", arg))),
        _ => Err(EvalSignal::error(format!("Unknown builtin {}", name))),
    }
}

// --- Binary operators

fn eval_binop(op: &BinOp, left: Value, right: Value) -> Result<Value, EvalSignal> {
    match (op, &left, &right) {
        // Boolean operators
        (BinOp::And, Value::Bool(false), _) => Ok(Value::Bool(false)),
        (BinOp::And, Value::Bool(true), Value::Bool(true)) => Ok(Value::Bool(true)),
        (BinOp::And, Value::Bool(_), Value::Bool(_)) => Ok(Value::Bool(false)),

        (BinOp::Or, Value::Bool(true), _) => Ok(Value::Bool(true)),
        (BinOp::Or, _, Value::Bool(true)) => Ok(Value::Bool(true)),
        (BinOp::Or, Value::Bool(_), Value::Bool(_)) => Ok(Value::Bool(false)),

        // Integer arithmetic
        (BinOp::Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
        (BinOp::Div, Value::Int(_), Value::Int(0)) => Err(EvalSignal::error("division by zero")),
        (BinOp::Div, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
        (BinOp::Mod, Value::Int(_), Value::Int(0)) => Err(EvalSignal::error("modulo by zero")),
        (BinOp::Mod, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a % b)),

        // Integer comparison
        (BinOp::Eq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a == b)),
        (BinOp::NotEq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a != b)),
        (BinOp::Lt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
        (BinOp::Gt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
        (BinOp::LtEq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
        (BinOp::GtEq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),

        // Float arithmetic
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
        (BinOp::Div, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
        (BinOp::Mod, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a % b)),

        // String concatenation
        (BinOp::Concat, Value::String(a), Value::String(b)) => {
            Ok(Value::String(format!("{}{}", a, b)))
        }

        _ => Err(EvalSignal::error(format!(
            "cannot apply {:?} to {} and {}",
            op, left, right
        ))),
    }
}

fn match_pattern(pattern: &Pat, value: &Value) -> Option<HashMap<String, Value>> {
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
                if pname != vname || pargs.len() != vargs.len() {
                    return None;
                }

                let mut all_bindings = HashMap::new();
                for (pat, val) in pargs.iter().zip(vargs.iter()) {
                    // TODO: checker should catch duplicate bindings (e.g. Pair(x, x))
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
    }
}

pub fn eval_program(program: &Program) -> Result<(), EvalSignal> {
    let env = Env::new();

    // Register builtins
    env.set("print".to_string(), Value::BuiltIn("print".to_string()));
    env.set("show".to_string(), Value::BuiltIn("show".to_string()));

    // Register built-in list constructors
    env.set(
        "Nil".to_string(),
        Value::Constructor {
            name: "Nil".to_string(),
            arity: 0,
            args: vec![],
        },
    );
    env.set(
        "Cons".to_string(),
        Value::Constructor {
            name: "Cons".to_string(),
            arity: 2,
            args: vec![],
        },
    );

    // Load and evaluate the standard prelude (written in dylang)
    let prelude_src = include_str!("prelude.dy");
    let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
        .lex()
        .map_err(|e| EvalError {
            message: format!("Prelude lex error: {}", e.message),
        })?;
    let prelude_program = crate::parser::Parser::new(prelude_tokens)
        .parse_program()
        .map_err(|e| EvalError {
            message: format!("Prelude parse error: {}", e.message),
        })?;
    for decl in &prelude_program {
        eval_decl(decl, &env)?;
    }

    // First pass: register all declarations
    // Since env is registered as an Rc, any closures captured will see bindings added later
    // This allows for mutual recursion
    for decl in program {
        eval_decl(decl, &env)?;
    }

    // Run main function
    match env.get("main") {
        Some(main_val @ Value::Closure(_)) => {
            apply(main_val, Value::Unit)?;
            Ok(())
        }
        Some(_) => Err(EvalSignal::error("`main` must be a function")),
        None => Err(EvalSignal::error("No main function defined")),
    }
}
