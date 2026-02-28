use crate::token::{Span, Spanned, Token};

pub struct Lexer {
    source: Vec<char>,
    pos: usize,
    nesting: i32,
}

#[derive(Debug)]
pub struct LexError {
    pub message: String,
    pub pos: usize,
}

impl Lexer {
    pub fn new(source: &str) -> Self {
        Lexer {
            source: source.chars().collect(),
            pos: 0,
            nesting: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.source.get(self.pos).copied()
    }

    fn peek_next(&self) -> Option<char> {
        self.source.get(self.pos + 1).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek();
        self.pos += 1;
        ch
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == ' ' || ch == '\t' || ch == '\r' {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_comment(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                // Don't consume the newline, let next_token handle it
                break;
            } else {
                self.advance();
            }
        }
    }

    fn read_number(&mut self) -> Token {
        let mut left_hand = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                left_hand.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        if self.peek() == Some('.') && self.peek_next().is_some_and(|c| c.is_ascii_digit()) {
            self.advance(); // consume '.'
            let mut right_hand = String::new();
            while let Some(ch) = self.peek() {
                if ch.is_ascii_digit() {
                    right_hand.push(ch);
                    self.advance();
                } else {
                    break;
                }
            }
            let str = format!("{left_hand}.{right_hand}");
            Token::Float(str.parse().unwrap())
        } else {
            Token::Int(left_hand.parse().unwrap())
        }
    }

    fn read_identifier(&mut self) -> Token {
        let mut s = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' || ch == '\'' {
                s.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        match s.as_str() {
            "let" => Token::Let,
            "type" => Token::Type,
            "case" => Token::Case,
            "if" => Token::If,
            "then" => Token::Then,
            "else" => Token::Else,
            "fun" => Token::Fun,
            "pub" => Token::Pub,
            "record" => Token::Record,
            "effect" => Token::Effect,
            "handler" => Token::Handler,
            "with" => Token::With,
            "where" => Token::Where,
            "import" => Token::Import,
            "module" => Token::Module,
            "trait" => Token::Trait,
            "impl" => Token::Impl,
            "return" => Token::Return,
            "resume" => Token::Resume,
            // Lex True/False as keywords even though they are treated as types
            "True" => Token::True,
            "False" => Token::False,
            _ => {
                if s.chars().next().unwrap().is_uppercase() {
                    Token::UpperIdent(s)
                } else {
                    Token::Ident(s)
                }
            }
        }
    }

    // Read string literals (between double quotes)
    fn read_string(&mut self) -> Result<Token, LexError> {
        let start = self.pos;
        self.advance(); // Consume opening "

        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unterminated string".to_string(),
                        pos: start,
                    });
                }
                Some('"') => {
                    self.advance(); // consume closing "
                    return Ok(Token::String(s));
                }
                Some('\\') => {
                    self.advance(); // consume backslash
                    match self.advance() {
                        Some('n') => s.push('\n'),
                        Some('t') => s.push('\t'),
                        Some('\\') => s.push('\\'),
                        Some('"') => s.push('"'),
                        Some(ch) => s.push(ch),
                        None => {
                            return Err(LexError {
                                message: "unterminated escape sequence".to_string(),
                                pos: start,
                            });
                        }
                    }
                }
                // TODO: Handle ${...} interpolation
                Some(ch) => {
                    s.push(ch);
                    self.advance();
                }
            }
        }
    }

    // Should we emit a terminator token right now?
    // Only at nesting depth 0, and only after tokens that "end" an expression.
    fn should_emit_terminator(&self, prev: &Option<Token>) -> bool {
        if self.nesting > 0 {
            return false;
        }
        match prev {
            None => false,
            Some(tok) => matches!(
                tok,
                Token::Int(_)
                    | Token::Float(_)
                    | Token::String(_)
                    | Token::True
                    | Token::False
                    | Token::Ident(_)
                    | Token::UpperIdent(_)
                    | Token::RParen
                    | Token::RBrace
            ),
        }
    }

    pub fn lex(&mut self) -> Result<Vec<Spanned>, LexError> {
        let mut tokens: Vec<Spanned> = Vec::new();
        let mut prev_token: Option<Token> = None;

        loop {
            self.skip_whitespace();

            let start = self.pos;

            match self.peek() {
                None => {
                    tokens.push(Spanned {
                        token: Token::Eof,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    return Ok(tokens);
                }
                Some('\n') => {
                    self.advance();
                    if self.should_emit_terminator(&prev_token) {
                        tokens.push(Spanned {
                            token: Token::Terminator,
                            span: Span {
                                start,
                                end: self.pos,
                            },
                        });
                        prev_token = Some(Token::Terminator);
                    }
                    continue;
                }
                Some('#') => {
                    self.skip_comment();
                }
                Some('"') => {
                    let tok = self.read_string()?;
                    tokens.push(Spanned {
                        token: tok.clone(),
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(tok);
                }
                Some(ch) if ch.is_ascii_digit() => {
                    let tok = self.read_number();
                    tokens.push(Spanned {
                        token: tok.clone(),
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(tok);
                }
                Some(ch) if ch.is_alphabetic() || ch == '_' => {
                    let tok = self.read_identifier();
                    tokens.push(Spanned {
                        token: tok.clone(),
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(tok);
                }

                // Two-character operators
                Some('-') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::Arrow,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::Arrow);
                }
                Some('|') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::Pipe,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::Pipe);
                }
                Some('<') if self.peek_next() == Some('-') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::ArrowBack,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::ArrowBack);
                }
                Some('<') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::Concat,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::Concat);
                }
                Some('<') if self.peek_next() == Some('|') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::PipeBack,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::PipeBack);
                }
                Some('=') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::EqEq,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::EqEq);
                }
                Some('!') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::NotEq,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::NotEq);
                }
                Some('<') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::LtEq,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::LtEq);
                }
                Some('>') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::GtEq,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::GtEq);
                }
                Some('&') if self.peek_next() == Some('&') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::And,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::And);
                }
                Some('.') if self.peek_next() == Some('.') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::DotDot,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::DotDot);
                }
                Some('|') if self.peek_next() == Some('|') => {
                    self.advance();
                    self.advance();
                    tokens.push(Spanned {
                        token: Token::Or,
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(Token::Or);
                }

                // Single-character tokens
                Some(ch) => {
                    self.advance();
                    let tok = match ch {
                        '+' => Token::Plus,
                        '-' => Token::Minus,
                        '*' => Token::Star,
                        '/' => Token::Slash,
                        '%' => Token::Modulo,
                        '=' => Token::Eq,
                        '<' => Token::Lt,
                        '>' => Token::Gt,
                        ':' => Token::Colon,
                        '.' => Token::Dot,
                        '\\' => Token::Backslash,
                        '|' => Token::Bar,
                        ',' => Token::Comma,
                        '(' => {
                            self.nesting += 1;
                            Token::LParen
                        }
                        ')' => {
                            self.nesting -= 1;
                            Token::RParen
                        }
                        '{' => Token::LBrace,
                        '}' => Token::RBrace,
                        _ => {
                            return Err(LexError {
                                message: format!("unexpected character: {:?}", ch),
                                pos: start,
                            });
                        }
                    };
                    tokens.push(Spanned {
                        token: tok.clone(),
                        span: Span {
                            start,
                            end: self.pos,
                        },
                    });
                    prev_token = Some(tok);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
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
}
