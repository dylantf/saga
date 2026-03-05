mod ast;
mod eval;
mod lexer;
mod parser;
mod token;
mod typechecker;

use std::env;
use std::fs;

fn byte_offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: dylang <file>.dy");
        std::process::exit(1);
    }

    let source = fs::read_to_string(&args[1]).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", args[1], e);
        std::process::exit(1);
    });

    let mut lexer = lexer::Lexer::new(&source);
    let tokens = match lexer.lex() {
        Ok(tokens) => tokens,
        Err(e) => {
            eprintln!("Lex error at byte {}: {}", e.pos, e.message);
            std::process::exit(1);
        }
    };

    let mut parser = parser::Parser::new(tokens);
    let program = match parser.parse_program() {
        Ok(program) => program,
        Err(e) => {
            eprintln!(
                "Parse error at {}..{}: {}",
                e.span.start, e.span.end, e.message
            );
            std::process::exit(1);
        }
    };

    let mut checker = typechecker::Checker::new();

    // Type-check the prelude first
    let prelude_src = include_str!("prelude.dy");
    let prelude_tokens = lexer::Lexer::new(prelude_src).lex().expect("prelude lex error");
    let prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    if let Err(e) = checker.check_program(&prelude_program) {
        eprintln!("Prelude type error: {}", e);
        std::process::exit(1);
    }

    if let Err(e) = checker.check_program(&program) {
        if let Some(span) = e.span {
            let (line, col) = byte_offset_to_line_col(&source, span.start);
            eprintln!("Type error at {}:{}:{}: {}", args[1], line, col, e);
        } else {
            eprintln!("Type error: {}", e);
        }
        std::process::exit(1);
    }

    match eval::eval_program(&program) {
        eval::EvalResult::Ok(_) => {}
        eval::EvalResult::Error(err) => {
            eprintln!("Runtime error: {}", err.message);
            std::process::exit(1);
        }
        eval::EvalResult::Effect { name, .. } => {
            eprintln!("Unhandled effect: {}", name);
            std::process::exit(1);
        }
    }
}
