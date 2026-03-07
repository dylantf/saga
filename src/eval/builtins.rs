use super::value::{Env, Value};
use crate::ast::Program;

pub(super) fn register_builtins(env: &Env) {
    env.set("print".to_string(), Value::BuiltIn("print".to_string()));
    env.set("show".to_string(), Value::BuiltIn("show".to_string()));
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
}

pub(super) fn parse_prelude() -> Program {
    let src = include_str!("../prelude.dy");
    let tokens = crate::lexer::Lexer::new(src)
        .lex()
        .expect("prelude lex error");
    crate::parser::Parser::new(tokens)
        .parse_program()
        .expect("prelude parse error")
}
