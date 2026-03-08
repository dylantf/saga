use super::value::{Env, Value};
use crate::ast::Program;

pub(crate) fn register_builtins(env: &Env) {
    env.set(
        "print".to_string(),
        Value::TraitMethod {
            trait_name: "Show".to_string(),
            method_name: "print".to_string(),
            env: env.clone(),
        },
    );
    env.set(
        "show".to_string(),
        Value::TraitMethod {
            trait_name: "Show".to_string(),
            method_name: "show".to_string(),
            env: env.clone(),
        },
    );
    env.set(
        "panic".to_string(),
        Value::BuiltIn {
            name: "panic".to_string(),
            arity: 1,
            args: vec![],
        },
    );
    env.set(
        "todo".to_string(),
        Value::BuiltIn {
            name: "todo".to_string(),
            arity: 1,
            args: vec![],
        },
    );
    // Dict builtins
    env.set("Dict.empty".to_string(), Value::Dict(vec![]));
    for (name, arity) in [
        ("Dict.get", 2),
        ("Dict.put", 3),
        ("Dict.remove", 2),
        ("Dict.keys", 1),
        ("Dict.values", 1),
        ("Dict.size", 1),
        ("Dict.from_list", 1),
        ("Dict.to_list", 1),
        ("Dict.member", 2),
    ] {
        env.set(
            name.to_string(),
            Value::BuiltIn {
                name: name.to_string(),
                arity,
                args: vec![],
            },
        );
    }

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
    let src = include_str!("../prelude/prelude.dy");
    let tokens = crate::lexer::Lexer::new(src)
        .lex()
        .expect("prelude lex error");
    crate::parser::Parser::new(tokens)
        .parse_program()
        .expect("prelude parse error")
}
