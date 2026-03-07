use super::*;
use crate::token::Token::*;

fn toks(source: &str) -> Vec<Token> {
    Lexer::new(source)
        .lex()
        .unwrap()
        .into_iter()
        .map(|s| s.token)
        .collect()
}

// --- Literals ---

#[test]
fn integer() {
    assert_eq!(toks("42"), vec![Int(42), Eof]);
}

#[test]
fn float() {
    assert_eq!(toks("3.144"), vec![Float(3.144), Eof]);
}

#[test]
fn integer_then_dot_ident() {
    // 3.foo should be int, dot, ident — not a float
    assert_eq!(toks("3.foo"), vec![Int(3), Dot, Ident("foo".into()), Eof]);
}

#[test]
fn string_simple() {
    assert_eq!(toks(r#""hello""#), vec![String("hello".into()), Eof]);
}

#[test]
fn string_escape_sequences() {
    assert_eq!(toks(r#""\n\t\\\"""#), vec![String("\n\t\\\"".into()), Eof]);
}

#[test]
fn string_unterminated() {
    let result = Lexer::new(r#""oops"#).lex();
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message, "unterminated string");
}

// --- Keywords ---

#[test]
fn keywords() {
    assert_eq!(toks("let"), vec![Let, Eof]);
    assert_eq!(toks("type"), vec![Type, Eof]);
    assert_eq!(toks("case"), vec![Case, Eof]);
    assert_eq!(toks("if"), vec![If, Eof]);
    assert_eq!(toks("then"), vec![Then, Eof]);
    assert_eq!(toks("else"), vec![Else, Eof]);
    assert_eq!(toks("fun"), vec![Fun, Eof]);
    assert_eq!(toks("pub"), vec![Pub, Eof]);
    assert_eq!(toks("record"), vec![Record, Eof]);
    assert_eq!(toks("effect"), vec![Effect, Eof]);
    assert_eq!(toks("handler"), vec![Handler, Eof]);
    assert_eq!(toks("with"), vec![With, Eof]);
    assert_eq!(toks("where"), vec![Where, Eof]);
    assert_eq!(toks("import"), vec![Import, Eof]);
    assert_eq!(toks("module"), vec![Module, Eof]);
    assert_eq!(toks("trait"), vec![Trait, Eof]);
    assert_eq!(toks("impl"), vec![Impl, Eof]);
    assert_eq!(toks("return"), vec![Return, Eof]);
    assert_eq!(toks("resume"), vec![Resume, Eof]);
}

#[test]
fn true_false_are_keywords() {
    assert_eq!(toks("True"), vec![True, Eof]);
    assert_eq!(toks("False"), vec![False, Eof]);
}

// --- Identifiers ---

#[test]
fn lower_ident() {
    assert_eq!(toks("foo"), vec![Ident("foo".into()), Eof]);
}

#[test]
fn upper_ident() {
    assert_eq!(toks("Option"), vec![UpperIdent("Option".into()), Eof]);
}

#[test]
fn ident_with_primes_and_underscores() {
    assert_eq!(toks("x'"), vec![Ident("x'".into()), Eof]);
    assert_eq!(toks("my_var"), vec![Ident("my_var".into()), Eof]);
    assert_eq!(toks("_unused"), vec![Ident("_unused".into()), Eof]);
}

#[test]
fn keyword_prefix_is_ident() {
    // "letter" starts with "let" but should be an ident
    assert_eq!(toks("letter"), vec![Ident("letter".into()), Eof]);
    assert_eq!(toks("iff"), vec![Ident("iff".into()), Eof]);
}

// --- Two-character operators ---

#[test]
fn two_char_operators() {
    assert_eq!(toks("->"), vec![Arrow, Eof]);
    assert_eq!(toks("|>"), vec![Pipe, Eof]);
    assert_eq!(toks("<-"), vec![ArrowBack, Eof]);
    assert_eq!(toks("<>"), vec![Concat, Eof]);
    assert_eq!(toks("<|"), vec![PipeBack, Eof]);
    assert_eq!(toks("=="), vec![EqEq, Eof]);
    assert_eq!(toks("!="), vec![NotEq, Eof]);
    assert_eq!(toks("<="), vec![LtEq, Eof]);
    assert_eq!(toks(">="), vec![GtEq, Eof]);
    assert_eq!(toks("&&"), vec![And, Eof]);
    assert_eq!(toks("||"), vec![Or, Eof]);
    assert_eq!(toks(".."), vec![DotDot, Eof]);
    assert_eq!(toks("::"), vec![DoubleColon, Eof]);
}

#[test]
fn less_than_disambiguation() {
    // Bare < when next char doesn't form a two-char op
    assert_eq!(toks("< x"), vec![Lt, Ident("x".into()), Eof]);
}

// --- Single-character tokens ---

#[test]
fn single_char_operators() {
    assert_eq!(
        toks("+ - * / %"),
        vec![Plus, Minus, Star, Slash, Modulo, Eof]
    );
    assert_eq!(toks("= < >"), vec![Eq, Lt, Gt, Eof]);
}

#[test]
fn delimiters() {
    assert_eq!(
        toks("( ) { } , : ."),
        vec![LParen, RParen, LBrace, RBrace, Comma, Colon, Dot, Eof]
    );
}

#[test]
fn backslash() {
    assert_eq!(toks("\\"), vec![Backslash, Eof]);
}

#[test]
fn unexpected_character() {
    let result = Lexer::new("@").lex();
    assert!(result.is_err());
}

// --- Comments ---

#[test]
fn comment_skipped() {
    assert_eq!(toks("# this is a comment"), vec![Eof]);
}

#[test]
fn comment_before_code() {
    assert_eq!(toks("# comment\n42"), vec![Int(42), Eof]);
}

#[test]
fn inline_comment_after_code() {
    // "42" then newline-after-comment triggers terminator
    assert_eq!(toks("42 # comment\n"), vec![Int(42), Terminator, Eof]);
}

// --- Terminators ---

#[test]
fn terminator_after_expression_ending_tokens() {
    assert_eq!(toks("42\n"), vec![Int(42), Terminator, Eof]);
    assert_eq!(toks("3.144\n"), vec![Float(3.144), Terminator, Eof]);
    assert_eq!(toks("\"hi\"\n"), vec![String("hi".into()), Terminator, Eof]);
    assert_eq!(toks("True\n"), vec![True, Terminator, Eof]);
    assert_eq!(toks("False\n"), vec![False, Terminator, Eof]);
    assert_eq!(toks("foo\n"), vec![Ident("foo".into()), Terminator, Eof]);
    assert_eq!(
        toks("Foo\n"),
        vec![UpperIdent("Foo".into()), Terminator, Eof]
    );
}

#[test]
fn terminator_after_closing_delimiters() {
    assert_eq!(toks("()\n"), vec![LParen, RParen, Terminator, Eof]);
    assert_eq!(toks("}\n"), vec![RBrace, Terminator, Eof]);
}

#[test]
fn no_terminator_after_operators() {
    assert_eq!(toks("+\n42"), vec![Plus, Int(42), Eof]);
    assert_eq!(toks("=\n42"), vec![Eq, Int(42), Eof]);
    assert_eq!(toks("->\nInt"), vec![Arrow, UpperIdent("Int".into()), Eof]);
}

#[test]
fn no_terminator_after_keywords() {
    assert_eq!(toks("let\nx"), vec![Let, Ident("x".into()), Eof]);
    assert_eq!(toks("if\nx"), vec![If, Ident("x".into()), Eof]);
}

#[test]
fn no_terminator_after_opening_delimiters() {
    assert_eq!(toks("(\n42\n)"), vec![LParen, Int(42), RParen, Eof]);
}

#[test]
fn no_terminator_inside_parens() {
    assert_eq!(
        toks("(foo\nbar)"),
        vec![
            LParen,
            Ident("foo".into()),
            Ident("bar".into()),
            RParen,
            Eof
        ]
    );
}

#[test]
fn nested_parens_suppress_terminators() {
    assert_eq!(
        toks("((x\ny))"),
        vec![
            LParen,
            LParen,
            Ident("x".into()),
            Ident("y".into()),
            RParen,
            RParen,
            Eof
        ]
    );
}

#[test]
fn multiple_blank_lines_single_terminator() {
    // After a terminator, more newlines shouldn't produce more terminators
    assert_eq!(toks("42\n\n\n"), vec![Int(42), Terminator, Eof]);
}

#[test]
fn leading_newlines_no_terminator() {
    assert_eq!(toks("\n\n42"), vec![Int(42), Eof]);
}

// --- Multi-statement programs ---

#[test]
fn two_statements() {
    assert_eq!(
        toks("let x = 1\nlet y = 2"),
        vec![
            Let,
            Ident("x".into()),
            Eq,
            Int(1),
            Terminator,
            Let,
            Ident("y".into()),
            Eq,
            Int(2),
            Eof,
        ]
    );
}

#[test]
fn function_definition() {
    assert_eq!(
        toks("pub fun add (a: Int) (b: Int) -> Int"),
        vec![
            Pub,
            Fun,
            Ident("add".into()),
            LParen,
            Ident("a".into()),
            Colon,
            UpperIdent("Int".into()),
            RParen,
            LParen,
            Ident("b".into()),
            Colon,
            UpperIdent("Int".into()),
            RParen,
            Arrow,
            UpperIdent("Int".into()),
            Eof,
        ]
    );
}

#[test]
fn pipe_expression() {
    assert_eq!(
        toks("x |> f |> g"),
        vec![
            Ident("x".into()),
            Pipe,
            Ident("f".into()),
            Pipe,
            Ident("g".into()),
            Eof,
        ]
    );
}

// --- Spans ---

#[test]
fn spans_are_correct() {
    let tokens = Lexer::new("ab cd").lex().unwrap();
    assert_eq!(tokens[0].span, Span { start: 0, end: 2 });
    assert_eq!(tokens[1].span, Span { start: 3, end: 5 });
}
