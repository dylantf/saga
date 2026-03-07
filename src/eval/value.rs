use crate::ast::{Expr, HandlerArm, Pat};
use std::{cell::RefCell, collections::HashMap, fmt, rc::Rc};

#[derive(Clone)]
pub struct ClosureArm {
    pub params: Vec<Pat>,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub env: Env,
}

#[derive(Clone)]
pub struct HandlerVal {
    pub arms: Vec<HandlerArm>,
    pub return_clause: Option<Box<HandlerArm>>,
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

    TraitMethod {
        trait_name: String,
        method_name: String,
        env: Env,
    },

    Continuation(Rc<RefCell<Option<Continuation>>>),
}

pub(crate) fn value_type_name(v: &Value) -> String {
    match v {
        Value::Int(_) => "Int".into(),
        Value::Float(_) => "Float".into(),
        Value::String(_) => "String".into(),
        Value::Bool(_) => "Bool".into(),
        Value::Unit => "Unit".into(),
        Value::Record { name, .. } => name.clone(),
        Value::Constructor { name, .. } => name.clone(),
        _ => "<unknown>".into(),
    }
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
            Value::TraitMethod { method_name, .. } => {
                write!(f, "<trait-method: {}>", method_name)
            }
            Value::Constructor { name, args, .. } => {
                if name == "Tuple" {
                    write!(f, "(")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")
                } else if name == "Nil" && args.is_empty() {
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
            Value::Continuation(_) => write!(f, "<continuation>"),
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
    pub(crate) fn new() -> Self {
        Env(Rc::new(RefCell::new(EnvInner {
            bindings: HashMap::new(),
            parent: None,
        })))
    }

    pub(crate) fn extend(&self) -> Self {
        Env(Rc::new(RefCell::new(EnvInner {
            bindings: HashMap::new(),
            parent: Some(self.clone()),
        })))
    }

    pub(crate) fn get(&self, name: &str) -> Option<Value> {
        let inner = self.0.borrow();
        if let Some(val) = inner.bindings.get(name) {
            Some(val.clone())
        } else if let Some(parent) = &inner.parent {
            parent.get(name)
        } else {
            None
        }
    }

    pub(crate) fn set(&self, name: String, value: Value) {
        self.0.borrow_mut().bindings.insert(name, value);
    }
}

// --- Eval result with continuations ---

#[derive(Debug)]
pub struct EvalError {
    pub message: String,
}

pub(crate) type Continuation = Box<dyn FnOnce(Value) -> EvalResult>;

pub enum EvalResult {
    Ok(Value),
    Error(EvalError),
    Effect {
        name: String,
        qualifier: Option<String>,
        args: Vec<Value>,
        continuation: Continuation,
    },
}

impl EvalResult {
    pub(crate) fn then(self, f: impl FnOnce(Value) -> EvalResult + 'static) -> EvalResult {
        match self {
            EvalResult::Ok(v) => f(v),
            EvalResult::Error(e) => EvalResult::Error(e),
            EvalResult::Effect {
                name,
                qualifier,
                args,
                continuation,
            } => EvalResult::Effect {
                name,
                qualifier,
                args,
                continuation: Box::new(move |v| continuation(v).then(f)),
            },
        }
    }

    pub(crate) fn error(message: impl Into<String>) -> EvalResult {
        EvalResult::Error(EvalError {
            message: message.into(),
        })
    }
}
