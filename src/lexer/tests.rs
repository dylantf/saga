use super::*;
use crate::token::StringKind;
use crate::token::Token::*;
use crate::token::Trivia;

fn toks(source: &str) -> Vec<Token> {
    Lexer::new(source)
        .lex()
        .unwrap()
        .into_iter()
        .map(|s| s.token)
        .collect()
}

fn lex(source: &str) -> Vec<Spanned> {
    Lexer::new(source).lex().unwrap()
}

// --- Literals ---

#[test]
fn integer() {
    assert_eq!(toks("42"), vec![Int("42".into(), 42), Eof]);
}

#[test]
fn float() {
    assert_eq!(toks("3.144"), vec![Float("3.144".into(), 3.144), Eof]);
}

#[test]
fn integer_with_separators() {
    assert_eq!(toks("1_000_000"), vec![Int("1_000_000".into(), 1_000_000), Eof]);
    assert_eq!(toks("1_0"), vec![Int("1_0".into(), 10), Eof]);
}

#[test]
fn float_with_separators() {
    assert_eq!(toks("1_000.000_1"), vec![Float("1_000.000_1".into(), 1_000.000_1), Eof]);
}

#[test]
fn trailing_underscore_is_not_separator() {
    // 42_ should lex as int 42 then ident _foo
    assert_eq!(toks("42_foo"), vec![Int("42".into(), 42), Ident("_foo".into()), Eof]);
}

#[test]
fn multiple_consecutive_underscores() {
    assert_eq!(toks("1__0"), vec![Int("1__0".into(), 10), Eof]);
    assert_eq!(toks("1___000"), vec![Int("1___000".into(), 1000), Eof]);
}

#[test]
fn leading_underscore_is_ident() {
    assert_eq!(toks("_100"), vec![Ident("_100".into()), Eof]);
}

#[test]
fn integer_then_dot_ident() {
    // 3.foo should be int, dot, ident - not a float
    assert_eq!(toks("3.foo"), vec![Int("3".into(), 3), Dot, Ident("foo".into()), Eof]);
}

#[test]
fn string_simple() {
    assert_eq!(toks(r#""hello""#), vec![String("hello".into(), StringKind::Normal), Eof]);
}

#[test]
fn string_escape_sequences() {
    assert_eq!(toks(r#""\n\t\\\"""#), vec![String("\n\t\\\"".into(), StringKind::Normal), Eof]);
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
    assert_eq!(toks("handle"), vec![Handle, Eof]);
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
fn at_sign() {
    assert_eq!(toks("@"), vec![At, Eof]);
}

#[test]
fn unexpected_character() {
    let result = Lexer::new("~").lex();
    assert!(result.is_err());
}

// --- Comments as trivia ---

#[test]
fn comment_on_own_line_is_leading_trivia() {
    let tokens = lex("# comment\n42");
    // Only significant tokens: Int("42".into(), 42), Eof
    assert_eq!(tokens.len(), 2);
    assert_eq!(tokens[0].token, Int("42".into(), 42));
    assert_eq!(tokens[0].leading_trivia, vec![Trivia::Comment("comment".into())]);
}

#[test]
fn inline_comment_is_trailing() {
    let tokens = lex("42 # comment\n");
    assert_eq!(tokens[0].token, Int("42".into(), 42));
    assert_eq!(tokens[0].trailing_comment, Some("comment".into()));
}

#[test]
fn doc_comment_is_leading_trivia() {
    let tokens = lex("#@ This is a doc comment\nfun");
    assert_eq!(tokens[0].token, Fun);
    assert_eq!(
        tokens[0].leading_trivia,
        vec![Trivia::DocComment("This is a doc comment".into())]
    );
}

#[test]
fn comment_at_end_of_file_is_eof_leading_trivia() {
    let tokens = lex("# comment");
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].token, Eof);
    assert_eq!(tokens[0].leading_trivia, vec![Trivia::Comment("comment".into())]);
}

// --- Newlines produce no tokens (no Terminator) ---

#[test]
fn newlines_produce_no_extra_tokens() {
    // Only significant tokens remain in the stream
    assert_eq!(toks("42\n"), vec![Int("42".into(), 42), Eof]);
    assert_eq!(toks("3.144\n"), vec![Float("3.144".into(), 3.144), Eof]);
    assert_eq!(toks("\"hi\"\n"), vec![String("hi".into(), StringKind::Normal), Eof]);
    assert_eq!(toks("True\n"), vec![True, Eof]);
    assert_eq!(toks("foo\n"), vec![Ident("foo".into()), Eof]);
}

#[test]
fn no_extra_tokens_after_operators() {
    assert_eq!(toks("+\n42"), vec![Plus, Int("42".into(), 42), Eof]);
    assert_eq!(toks("=\n42"), vec![Eq, Int("42".into(), 42), Eof]);
    assert_eq!(toks("->\nInt"), vec![Arrow, UpperIdent("Int".into()), Eof]);
}

#[test]
fn no_extra_tokens_after_keywords() {
    assert_eq!(toks("let\nx"), vec![Let, Ident("x".into()), Eof]);
    assert_eq!(toks("if\nx"), vec![If, Ident("x".into()), Eof]);
}

#[test]
fn no_extra_tokens_inside_parens() {
    assert_eq!(toks("(\n42\n)"), vec![LParen, Int("42".into(), 42), RParen, Eof]);
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

// --- Blank lines as trivia ---

#[test]
fn blank_lines_are_leading_trivia() {
    let tokens = lex("42\n\n\n");
    // Int("42".into(), 42), Eof
    assert_eq!(tokens.len(), 2);
    assert_eq!(tokens[0].token, Int("42".into(), 42));
    // The blank lines are leading trivia on the Eof token
    assert_eq!(tokens[1].token, Eof);
    assert_eq!(tokens[1].leading_trivia, vec![Trivia::BlankLines(2)]);
}

#[test]
fn leading_newlines_no_extra_tokens() {
    assert_eq!(toks("\n\n42"), vec![Int("42".into(), 42), Eof]);
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
            Int("1".into(), 1),
            Let,
            Ident("y".into()),
            Eq,
            Int("2".into(), 2),
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
    let tokens = lex("ab cd");
    assert_eq!(tokens[0].span, Span { start: 0, end: 2 });
    assert_eq!(tokens[1].span, Span { start: 3, end: 5 });
}

#[test]
fn spans_are_byte_offsets() {
    // "小明" is 6 bytes (2 chars x 3 bytes each), so the token after it
    // should start at byte offset 9 (quote + 6 bytes + quote + space).
    let src = "\"小明\" ab";
    let tokens = lex(src);
    // String token: bytes 0..8 (quote + 6 bytes + quote)
    assert_eq!(tokens[0].span, Span { start: 0, end: 8 });
    // Ident "ab": bytes 9..11
    assert_eq!(tokens[1].span, Span { start: 9, end: 11 });
    // Verify spans can slice the source correctly
    assert_eq!(&src[tokens[1].span.start..tokens[1].span.end], "ab");
}

// --- Raw strings ---

#[test]
fn raw_string_simple() {
    assert_eq!(toks(r#"@"hello""#), vec![String("hello".into(), StringKind::Raw), Eof]);
}

#[test]
fn raw_string_no_escapes() {
    // \n and \t should be literal backslash + letter, not escape sequences
    assert_eq!(
        toks(r#"@"hello\nworld\t""#),
        vec![String("hello\\nworld\\t".into(), StringKind::Raw), Eof]
    );
}

#[test]
fn raw_string_empty() {
    assert_eq!(toks(r#"@"""#), vec![String("".into(), StringKind::Raw), Eof]);
}

#[test]
fn raw_string_unterminated() {
    let result = Lexer::new(r#"@"oops"#).lex();
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message, "unterminated raw string");
}

// --- Multiline strings ---

#[test]
fn multiline_string_basic() {
    let src = "\"\"\"\n    hello\n    world\n    \"\"\"";
    assert_eq!(toks(src), vec![String("hello\nworld".into(), StringKind::Multiline), Eof]);
}

#[test]
fn multiline_string_empty() {
    assert_eq!(toks("\"\"\"\"\"\""), vec![String("".into(), StringKind::Multiline), Eof]);
}

#[test]
fn multiline_string_single_line() {
    assert_eq!(
        toks("\"\"\"hello\"\"\""),
        vec![String("hello".into(), StringKind::Multiline), Eof]
    );
}

#[test]
fn multiline_string_escapes() {
    // Multiline strings store raw content - escapes preserved as-is
    let src = "\"\"\"\n    hello\\tworld\n    \"\"\"";
    assert_eq!(
        toks(src),
        vec![String("hello\\tworld".into(), StringKind::Multiline), Eof]
    );
}

#[test]
fn multiline_string_unterminated() {
    let result = Lexer::new("\"\"\"oops").lex();
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message, "unterminated multiline string");
}

#[test]
fn multiline_string_preserves_relative_indent() {
    // Content indented more than closing """ should keep the extra indent
    let src = "\"\"\"\n        deep\n    shallow\n    \"\"\"";
    assert_eq!(
        toks(src),
        vec![String("    deep\nshallow".into(), StringKind::Multiline), Eof]
    );
}

#[test]
fn multiline_string_blank_lines() {
    let src = "\"\"\"\n    hello\n\n    world\n    \"\"\"";
    assert_eq!(
        toks(src),
        vec![String("hello\n\nworld".into(), StringKind::Multiline), Eof]
    );
}

#[test]
fn multiline_string_no_extra_tokens_for_inner_newlines() {
    // Newlines inside the multiline string should not produce extra tokens
    let src = "\"\"\"\n    hello\n    world\n    \"\"\"";
    let tokens = toks(src);
    // Should just be String + Eof
    assert_eq!(tokens.len(), 2);
    assert_eq!(tokens[0], String("hello\nworld".into(), StringKind::Multiline));
}

// --- Raw multiline strings ---

#[test]
fn raw_multiline_string_basic() {
    let src = "@\"\"\"\n    hello\\nworld\n    \"\"\"";
    // \n should be literal backslash-n, not a newline
    assert_eq!(
        toks(src),
        vec![String("hello\\nworld".into(), StringKind::RawMultiline), Eof]
    );
}

#[test]
fn raw_multiline_string_empty() {
    assert_eq!(toks("@\"\"\"\"\"\""), vec![String("".into(), StringKind::RawMultiline), Eof]);
}

#[test]
fn raw_multiline_string_unterminated() {
    let result = Lexer::new("@\"\"\"oops").lex();
    assert!(result.is_err());
    assert_eq!(
        result.unwrap_err().message,
        "unterminated raw multiline string"
    );
}

// --- Multiline interpolated strings ---

#[test]
fn multiline_interp_basic() {
    let src = "$\"\"\"\n    hello {name}\n    \"\"\"";
    let tokens = toks(src);
    // Should produce InterpolatedString with stripped indentation
    assert!(matches!(&tokens[0], InterpolatedString(_, _)));
    if let InterpolatedString(parts, _) = &tokens[0] {
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0], InterpPart::Literal("hello ".into()));
        // parts[1] is a Hole containing the `name` tokens
        if let InterpPart::Hole(hole_tokens) = &parts[1] {
            assert_eq!(hole_tokens.len(), 1);
            assert_eq!(hole_tokens[0].token, Ident("name".into()));
        } else {
            panic!("expected Hole");
        }
    }
}

#[test]
fn multiline_interp_unterminated() {
    let result = Lexer::new("$\"\"\"oops {x}").lex();
    assert!(result.is_err());
    assert_eq!(
        result.unwrap_err().message,
        "unterminated multiline interpolated string"
    );
}
