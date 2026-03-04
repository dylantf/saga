mod ast;
mod eval;
mod lexer;
mod parser;
mod token;

use std::env;
use std::fs;

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

    if let Err(e) = eval::eval_program(&program) {
        match e {
            eval::EvalSignal::Error(err) => eprintln!("Runtime error: {}", err.message),
            eval::EvalSignal::Effect { name, .. } => eprintln!("Unhandled effect: {}", name),
        };
        std::process::exit(1);
    }
}
