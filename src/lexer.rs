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

    fn emit(&self, token: Token, start: usize) -> (Spanned, Token) {
        let spanned = Spanned {
            token: token.clone(),
            span: Span {
                start,
                end: self.pos,
            },
        };
        (spanned, token)
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
            "needs" => Token::Needs,
            "for" => Token::For,
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
                    | Token::EffectCall(_)
                    | Token::RParen
                    | Token::RBrace
                    | Token::RBracket
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
                    let (spanned, _) = self.emit(Token::Eof, start);
                    tokens.push(spanned);
                    return Ok(tokens);
                }
                Some('\n') | Some(';') => {
                    self.advance();
                    if self.should_emit_terminator(&prev_token) {
                        let (spanned, tok) = self.emit(Token::Terminator, start);
                        tokens.push(spanned);
                        prev_token = Some(tok);
                    }
                    continue;
                }
                Some('#') => {
                    self.skip_comment();
                }
                Some('"') => {
                    let tok = self.read_string()?;
                    let (spanned, tok) = self.emit(tok, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some(ch) if ch.is_ascii_digit() => {
                    let tok = self.read_number();
                    let (spanned, tok) = self.emit(tok, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some(ch) if ch.is_alphabetic() || ch == '_' => {
                    let mut tok = self.read_identifier();
                    // ident! (no space) → EffectCall, but not ident!=
                    if let Token::Ident(ref name) = tok {
                        if self.peek() == Some('!') && self.peek_next() != Some('=') {
                            let name = name.clone();
                            self.advance(); // consume '!'
                            tok = Token::EffectCall(name);
                        }
                    }
                    let (spanned, tok) = self.emit(tok, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }

                // Two-character operators
                Some('-') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::Arrow, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('|') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::Pipe, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('<') if self.peek_next() == Some('-') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::ArrowBack, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('<') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::Concat, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('<') if self.peek_next() == Some('|') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::PipeBack, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('=') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::EqEq, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('!') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::NotEq, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('<') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::LtEq, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('>') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::GtEq, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('&') if self.peek_next() == Some('&') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::And, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some(':') if self.peek_next() == Some(':') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::DoubleColon, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('.') if self.peek_next() == Some('.') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::DotDot, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
                Some('|') if self.peek_next() == Some('|') => {
                    self.advance();
                    self.advance();
                    let (spanned, tok) = self.emit(Token::Or, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
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
                        '[' => {
                            self.nesting += 1;
                            Token::LBracket
                        }
                        ']' => {
                            self.nesting -= 1;
                            Token::RBracket
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
                    let (spanned, tok) = self.emit(tok, start);
                    tokens.push(spanned);
                    prev_token = Some(tok);
                }
            }
        }
    }
}

#[cfg(test)]
mod lexer_tests;
