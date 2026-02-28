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
