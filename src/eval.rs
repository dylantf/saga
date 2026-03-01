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

    BuiltIn(String),
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
                if args.is_empty() {
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

// --- Expressions ---

pub fn eval_expr(expr: &Expr, env: &Env) -> Result<Value, EvalError> {
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
            None => Err(EvalError {
                message: format!("Undefined variable: {}", name),
            }),
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
            _ => Err(EvalError {
                message: "Unary minus requires a number".to_string(),
            }),
        },

        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => match eval_expr(cond, env)? {
            Value::Bool(true) => eval_expr(then_branch, env),
            Value::Bool(false) => eval_expr(else_branch, env),
            other => Err(EvalError {
                message: format!("If condition must evaluate to a Boolean, got: {}", other),
            }),
        },

        Expr::Constructor { name, .. } => env.get(name).ok_or_else(|| EvalError {
            message: format!("undefined constructor: {}", name),
        }),

        // Expr::Pipe { lhs, rhs, .. } => {
        //     let arg = eval_expr(lhs, env)?;
        //     let func = eval_expr(rhs, env)?;
        //     apply(func, arg)
        // }
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
                                return Err(EvalError {
                                    message: format!(
                                        "Guard must evaluate to a Bool, got: {}",
                                        other
                                    ),
                                });
                            }
                        }
                    }

                    return eval_expr(&arm.body, &case_env);
                }
            }

            Err(EvalError {
                message: format!("No pattern matched for {}", val),
            })
        }

        Expr::FieldAccess { expr, field, .. } => match eval_expr(expr, env)? {
            Value::Record { fields, .. } => fields.get(field).cloned().ok_or_else(|| EvalError {
                message: format!("Record has no field '{}'", field),
            }),
            other => Err(EvalError {
                message: format!("Cannot access field '{}' on {}", field, other),
            }),
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
            other => Err(EvalError {
                message: format!("Cannot update fields on {}", other),
            }),
        },
    }
}

// --- Function application

fn apply(func: Value, arg: Value) -> Result<Value, EvalError> {
    match func {
        Value::Closure(closure_arms) => {
            for arm in &closure_arms {
                let Some(bindings) = match_pattern(&arm.params[0], &arg) else {
                    continue;
                };

                let local_env = arm.env.extend();
                for (name, val) in bindings {
                    local_env.set(name, val);
                }

                // Only one param to be applied, try to evaluate
                if arm.params.len() == 1 {
                    // Check guard expr if present
                    if let Some(guard) = &arm.guard {
                        match eval_expr(guard, &local_env)? {
                            Value::Bool(true) => {}
                            Value::Bool(false) => continue, // Guard failed
                            other => {
                                return Err(EvalError {
                                    message: format!("Guard must be a Bool, got: {}", other),
                                });
                            }
                        }
                    }
                    return eval_expr(&arm.body, &local_env);
                } else {
                    // More params to be applied, return a new closure with current env
                    return Ok(Value::Closure(vec![ClosureArm {
                        params: arm.params[1..].to_vec(),
                        body: arm.body.clone(),
                        guard: arm.guard.clone(),
                        env: local_env,
                    }]));
                }
            }

            // No arm matched
            Err(EvalError {
                message: "Non-exhaustive patterns in function".to_string(),
            })
        }

        Value::Constructor {
            name,
            arity,
            mut args,
        } => {
            args.push(arg);
            if args.len() > arity {
                Err(EvalError {
                    message: format!(
                        "Constructor {} expects {} args, got {}.",
                        name,
                        arity,
                        args.len()
                    ),
                })
            } else {
                Ok(Value::Constructor { name, arity, args })
            }
        }

        Value::BuiltIn(name) => eval_builtin(&name, arg),

        not_a_func => Err(EvalError {
            message: format!("Cannot call {} as a function", not_a_func),
        }),
    }
}

// --- Declarations ---

pub fn eval_decl(decl: &Decl, env: &Env) -> Result<(), EvalError> {
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

        // TODO, the whole algebraic effect system lol
        Decl::EffectDef { .. } => todo!(),
        Decl::HandlerDef { .. } => todo!(),
        Decl::ImplDef { .. } => todo!(),

        Decl::Import { .. } => todo!(),
    }
}

// --- Builtin functions

fn eval_builtin(name: &str, arg: Value) -> Result<Value, EvalError> {
    match name {
        "print" => {
            println!("{}", arg);
            Ok(Value::Unit)
        }
        "show" => Ok(Value::String(format!("{}", arg))),
        _ => Err(EvalError {
            message: format!("Unknown builtin {}", name),
        }),
    }
}

// --- Binary operators

fn eval_binop(op: &BinOp, left: Value, right: Value) -> Result<Value, EvalError> {
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
        (BinOp::Div, Value::Int(_), Value::Int(0)) => Err(EvalError {
            message: "division by zero".into(),
        }),
        (BinOp::Div, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
        (BinOp::Mod, Value::Int(_), Value::Int(0)) => Err(EvalError {
            message: "modulo by zero".into(),
        }),
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

        _ => Err(EvalError {
            message: format!("cannot apply {:?} to {} and {}", op, left, right),
        }),
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

pub fn eval_program(program: &Program) -> Result<(), EvalError> {
    let env = Env::new();

    // Register builins
    env.set("print".to_string(), Value::BuiltIn("print".to_string()));
    env.set("show".to_string(), Value::BuiltIn("show".to_string()));

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
        Some(_) => Err(EvalError {
            message: "`main` must be a function".to_string(),
        }),
        None => Err(EvalError {
            message: "No main function defined".to_string(),
        }),
    }
}
