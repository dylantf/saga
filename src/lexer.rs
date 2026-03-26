use crate::token::{InterpPart, Span, Spanned, Token, Trivia};

/// Strip leading indentation from a multiline string based on the column of the closing `"""`.
/// - The first element (empty string from newline after opening `"""`) is removed.
/// - The last element (whitespace-only line containing closing `"""`) is removed.
/// - `indent` leading spaces/tabs are stripped from each remaining line.
fn strip_indentation(s: &str, indent: usize) -> String {
    let mut lines: Vec<&str> = s.split('\n').collect();

    // Remove leading empty line (newline immediately after opening """)
    if lines.first() == Some(&"") {
        lines.remove(0);
    }

    // Remove trailing whitespace-only line (the line with closing """)
    if let Some(last) = lines.last()
        && last.chars().all(|c| c == ' ' || c == '\t')
    {
        lines.pop();
    }

    // Strip `indent` leading whitespace chars from each line
    lines
        .iter()
        .map(|line| {
            let mut chars = line.chars();
            for _ in 0..indent {
                match chars.clone().next() {
                    Some(' ') | Some('\t') => {
                        chars.next();
                    }
                    _ => break,
                }
            }
            chars.as_str()
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Apply indentation stripping to interpolated string parts.
/// Strips the leading empty line (after opening """), trailing whitespace-only line
/// (before closing """), and `indent` leading spaces from each line within literals.
fn strip_indentation_interp(parts: &mut Vec<InterpPart>, indent: usize) {
    // Concatenate all literals (using a placeholder for holes) so we can identify
    // line structure, then strip and redistribute.
    // Simpler approach: process each literal's lines, stripping indent at line starts.

    // First, remove leading newline from first literal (newline after opening """)
    if let Some(InterpPart::Literal(s)) = parts.first_mut()
        && s.starts_with('\n')
    {
        *s = s[1..].to_string();
    }

    // Remove trailing whitespace-only content from last literal (line with closing """)
    if let Some(InterpPart::Literal(s)) = parts.last_mut() {
        if let Some(last_nl) = s.rfind('\n') {
            let after = &s[last_nl + 1..];
            if after.chars().all(|c| c == ' ' || c == '\t') {
                *s = s[..last_nl].to_string();
            }
        } else if s.chars().all(|c| c == ' ' || c == '\t') {
            *s = String::new();
        }
    }

    // Strip `indent` spaces after every newline within each literal
    for part in parts.iter_mut() {
        if let InterpPart::Literal(s) = part {
            let mut result = String::new();
            let mut lines = s.split('\n');
            if let Some(first) = lines.next() {
                // First line of each literal: only strip if it's the very first part
                // We handle this by stripping from the first segment's first line below
                result.push_str(first);
            }
            for line in lines {
                result.push('\n');
                // Strip indent spaces from start of line
                let mut chars = line.chars();
                for _ in 0..indent {
                    match chars.clone().next() {
                        Some(' ') | Some('\t') => {
                            chars.next();
                        }
                        _ => break,
                    }
                }
                result.push_str(chars.as_str());
            }
            *s = result;
        }
    }

    // Strip indent from the very first literal's first line
    if let Some(InterpPart::Literal(s)) = parts.first_mut() {
        let mut chars = s.chars();
        for _ in 0..indent {
            match chars.clone().next() {
                Some(' ') | Some('\t') => {
                    chars.next();
                }
                _ => break,
            }
        }
        *s = chars.collect();
    }

    // Remove empty literals
    parts.retain(|p| !matches!(p, InterpPart::Literal(s) if s.is_empty()));
}

pub struct Lexer {
    source: String,
    pos: usize,
    nesting: i32,
    // Stack of saved nesting levels: `{` pushes and resets, `}` pops and restores.
    // This ensures blocks inside parens still get their terminators.
    nesting_stack: Vec<i32>,
}

#[derive(Debug)]
pub struct LexError {
    pub message: String,
    pub pos: usize,
}

impl Lexer {
    pub fn new(source: &str) -> Self {
        Lexer {
            source: source.to_string(),
            pos: 0,
            nesting: 0,
            nesting_stack: Vec::new(),
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.pos..].chars().next()
    }

    fn peek_next(&self) -> Option<char> {
        let mut chars = self.source[self.pos..].chars();
        chars.next();
        chars.next()
    }

    fn peek_ahead(&self, n: usize) -> Option<char> {
        self.source[self.pos..].chars().nth(n)
    }

    /// Compute the 0-based character column of `pos` (a byte offset) by counting
    /// chars from the last newline. Used for multiline string indentation stripping.
    fn column_of(&self, pos: usize) -> usize {
        let before = &self.source[..pos];
        match before.rfind('\n') {
            Some(nl) => before[nl + 1..].chars().count(),
            None => before.chars().count(),
        }
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
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

    fn emit(&self, token: Token, start: usize, leading_trivia: Vec<Trivia>, preceded_by_newline: bool) -> Spanned {
        Spanned {
            token,
            span: Span {
                start,
                end: self.pos,
            },
            leading_trivia,
            trailing_comment: None,
            preceded_by_newline,
        }
    }

    /// Read a comment body (after the `#`). Returns (text, is_doc).
    fn read_comment_text(&mut self) -> (String, bool) {
        let is_doc = self.peek() == Some('@');
        if is_doc {
            self.advance(); // skip @
        }
        let mut text = String::new();
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            } else {
                text.push(ch);
                self.advance();
            }
        }
        (text.trim().to_string(), is_doc)
    }

    fn read_number(&mut self) -> Token {
        let mut left_hand = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                left_hand.push(ch);
                self.advance();
            } else if ch == '_'
                && self
                    .peek_next()
                    .is_some_and(|c| c.is_ascii_digit() || c == '_')
            {
                self.advance(); // skip separator
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
                } else if ch == '_'
                    && self
                        .peek_next()
                        .is_some_and(|c| c.is_ascii_digit() || c == '_')
                {
                    self.advance(); // skip separator
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
            "assert" => Token::Ident("assert".into()),
            "type" => Token::Type,
            "case" => Token::Case,
            "if" => Token::If,
            "then" => Token::Then,
            "else" => Token::Else,
            "fun" => Token::Fun,
            "pub" => Token::Pub,
            "opaque" => Token::Opaque,
            "record" => Token::Record,
            "effect" => Token::Effect,
            "handler" => Token::Handler,
            "with" => Token::With,
            "where" => Token::Where,
            "import" => Token::Import,
            "module" => Token::Module,
            "as" => Token::As,
            "trait" => Token::Trait,
            "impl" => Token::Impl,
            "return" => Token::Return,
            "resume" => Token::Resume,
            "needs" => Token::Needs,
            "for" => Token::For,
            "do" => Token::Do,
            "deriving" => Token::Deriving,
            "receive" => Token::Receive,
            "after" => Token::After,
            "mut" => Token::Ident("mut".into()),
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
                        Some('x') => {
                            let hi = self.advance().and_then(|c| c.to_digit(16));
                            let lo = self.advance().and_then(|c| c.to_digit(16));
                            match (hi, lo) {
                                (Some(h), Some(l)) => s.push((h * 16 + l) as u8 as char),
                                _ => return Err(LexError {
                                    message: "invalid \\x escape: expected two hex digits".to_string(),
                                    pos: start,
                                }),
                            }
                        }
                        Some(ch) => s.push(ch),
                        None => {
                            return Err(LexError {
                                message: "unterminated escape sequence".to_string(),
                                pos: start,
                            });
                        }
                    }
                }
                Some(ch) => {
                    s.push(ch);
                    self.advance();
                }
            }
        }
    }

    // Read an interpolated string literal: $"hello {name}, age {age}"
    // Called after consuming the opening `$"`.
    fn read_interp_string(&mut self, start: usize) -> Result<Token, LexError> {
        let mut parts: Vec<InterpPart> = Vec::new();
        let mut literal = String::new();

        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unterminated interpolated string".to_string(),
                        pos: start,
                    });
                }
                Some('"') => {
                    self.advance();
                    if !literal.is_empty() {
                        parts.push(InterpPart::Literal(literal));
                    }
                    return Ok(Token::InterpolatedString(parts));
                }
                Some('\\') => {
                    self.advance();
                    match self.advance() {
                        Some('n') => literal.push('\n'),
                        Some('t') => literal.push('\t'),
                        Some('\\') => literal.push('\\'),
                        Some('"') => literal.push('"'),
                        Some('x') => {
                            let hi = self.advance().and_then(|c| c.to_digit(16));
                            let lo = self.advance().and_then(|c| c.to_digit(16));
                            match (hi, lo) {
                                (Some(h), Some(l)) => literal.push((h * 16 + l) as u8 as char),
                                _ => return Err(LexError {
                                    message: "invalid \\x escape: expected two hex digits".to_string(),
                                    pos: start,
                                }),
                            }
                        }
                        Some(ch) => literal.push(ch),
                        None => {
                            return Err(LexError {
                                message: "unterminated escape sequence".to_string(),
                                pos: start,
                            });
                        }
                    }
                }
                // `{expr}` hole
                Some('{') => {
                    self.advance(); // consume `{`
                    let hole_start = self.pos; // position of first char inside hole
                    if !literal.is_empty() {
                        parts.push(InterpPart::Literal(std::mem::take(&mut literal)));
                    }
                    // Collect raw chars until matching `}`, tracking brace depth
                    let mut hole_src = String::new();
                    let mut depth: usize = 1;
                    loop {
                        match self.peek() {
                            None => {
                                return Err(LexError {
                                    message: "unterminated interpolation hole".to_string(),
                                    pos: start,
                                });
                            }
                            Some('{') => {
                                depth += 1;
                                hole_src.push('{');
                                self.advance();
                            }
                            Some('}') => {
                                depth -= 1;
                                if depth == 0 {
                                    self.advance(); // consume closing `}`
                                    break;
                                }
                                hole_src.push('}');
                                self.advance();
                            }
                            Some(ch) => {
                                hole_src.push(ch);
                                self.advance();
                            }
                        }
                    }
                    let hole_tokens = Lexer::new(&hole_src).lex().map_err(|e| LexError {
                        message: format!("in interpolation hole: {}", e.message),
                        pos: start,
                    })?;
                    // Strip the trailing Eof and offset spans to original source positions
                    let hole_tokens: Vec<Spanned> = hole_tokens
                        .into_iter()
                        .filter(|t| t.token != Token::Eof)
                        .map(|t| Spanned {
                            token: t.token,
                            span: Span {
                                start: t.span.start + hole_start,
                                end: t.span.end + hole_start,
                            },
                            leading_trivia: t.leading_trivia,
                            trailing_comment: t.trailing_comment,
                            preceded_by_newline: t.preceded_by_newline,
                        })
                        .collect();
                    parts.push(InterpPart::Hole(hole_tokens));
                }
                Some(ch) => {
                    literal.push(ch);
                    self.advance();
                }
            }
        }
    }

    // Read a raw string: @"..." — no escape processing.
    // Called after consuming `@`. Consumes the opening `"`.
    fn read_raw_string(&mut self, start: usize) -> Result<Token, LexError> {
        self.advance(); // consume opening "
        let mut s = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    return Err(LexError {
                        message: "unterminated raw string".to_string(),
                        pos: start,
                    });
                }
                Some('"') => {
                    self.advance();
                    return Ok(Token::String(s));
                }
                Some(ch) => {
                    s.push(ch);
                    self.advance();
                }
            }
        }
    }

    // Read a raw multiline string: @"""...""" — no escape processing, with indentation stripping.
    // Called after consuming `@"""`.
    fn read_raw_multiline_string(&mut self, start: usize) -> Result<Token, LexError> {
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unterminated raw multiline string".to_string(),
                        pos: start,
                    });
                }
                Some('"') if self.peek_next() == Some('"') && self.peek_ahead(2) == Some('"') => {
                    let close_col = self.column_of(self.pos);
                    self.advance(); // "
                    self.advance(); // "
                    self.advance(); // "
                    return Ok(Token::String(strip_indentation(&s, close_col)));
                }
                Some(ch) => {
                    s.push(ch);
                    self.advance();
                }
            }
        }
    }

    // Read a multiline string: """...""" — with escape processing and indentation stripping.
    // Called after consuming the opening `"""`.
    fn read_multiline_string(&mut self, start: usize) -> Result<Token, LexError> {
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unterminated multiline string".to_string(),
                        pos: start,
                    });
                }
                Some('"') if self.peek_next() == Some('"') && self.peek_ahead(2) == Some('"') => {
                    let close_col = self.column_of(self.pos);
                    self.advance(); // "
                    self.advance(); // "
                    self.advance(); // "
                    return Ok(Token::String(strip_indentation(&s, close_col)));
                }
                Some('\\') => {
                    self.advance();
                    match self.advance() {
                        Some('n') => s.push('\n'),
                        Some('t') => s.push('\t'),
                        Some('\\') => s.push('\\'),
                        Some('"') => s.push('"'),
                        Some('x') => {
                            let hi = self.advance().and_then(|c| c.to_digit(16));
                            let lo = self.advance().and_then(|c| c.to_digit(16));
                            match (hi, lo) {
                                (Some(h), Some(l)) => s.push((h * 16 + l) as u8 as char),
                                _ => return Err(LexError {
                                    message: "invalid \\x escape: expected two hex digits".to_string(),
                                    pos: start,
                                }),
                            }
                        }
                        Some(ch) => s.push(ch),
                        None => {
                            return Err(LexError {
                                message: "unterminated escape sequence".to_string(),
                                pos: start,
                            });
                        }
                    }
                }
                Some(ch) => {
                    s.push(ch);
                    self.advance();
                }
            }
        }
    }

    // Read a multiline interpolated string: $"""..."""
    // Called after consuming `$"""`.
    fn read_multiline_interp_string(&mut self, start: usize) -> Result<Token, LexError> {
        let mut parts: Vec<InterpPart> = Vec::new();
        let mut literal = String::new();

        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unterminated multiline interpolated string".to_string(),
                        pos: start,
                    });
                }
                Some('"') if self.peek_next() == Some('"') && self.peek_ahead(2) == Some('"') => {
                    let close_col = self.column_of(self.pos);
                    self.advance(); // "
                    self.advance(); // "
                    self.advance(); // "
                    if !literal.is_empty() {
                        parts.push(InterpPart::Literal(literal));
                    }
                    // Apply indentation stripping to literal parts
                    strip_indentation_interp(&mut parts, close_col);
                    return Ok(Token::InterpolatedString(parts));
                }
                Some('\\') => {
                    self.advance();
                    match self.advance() {
                        Some('n') => literal.push('\n'),
                        Some('t') => literal.push('\t'),
                        Some('\\') => literal.push('\\'),
                        Some('"') => literal.push('"'),
                        Some('x') => {
                            let hi = self.advance().and_then(|c| c.to_digit(16));
                            let lo = self.advance().and_then(|c| c.to_digit(16));
                            match (hi, lo) {
                                (Some(h), Some(l)) => literal.push((h * 16 + l) as u8 as char),
                                _ => return Err(LexError {
                                    message: "invalid \\x escape: expected two hex digits".to_string(),
                                    pos: start,
                                }),
                            }
                        }
                        Some(ch) => literal.push(ch),
                        None => {
                            return Err(LexError {
                                message: "unterminated escape sequence".to_string(),
                                pos: start,
                            });
                        }
                    }
                }
                Some('{') => {
                    self.advance();
                    let hole_start = self.pos;
                    if !literal.is_empty() {
                        parts.push(InterpPart::Literal(std::mem::take(&mut literal)));
                    }
                    let mut hole_src = String::new();
                    let mut depth: usize = 1;
                    loop {
                        match self.peek() {
                            None => {
                                return Err(LexError {
                                    message: "unterminated interpolation hole".to_string(),
                                    pos: start,
                                });
                            }
                            Some('{') => {
                                depth += 1;
                                hole_src.push('{');
                                self.advance();
                            }
                            Some('}') => {
                                depth -= 1;
                                if depth == 0 {
                                    self.advance();
                                    break;
                                }
                                hole_src.push('}');
                                self.advance();
                            }
                            Some(ch) => {
                                hole_src.push(ch);
                                self.advance();
                            }
                        }
                    }
                    let hole_tokens = Lexer::new(&hole_src).lex().map_err(|e| LexError {
                        message: format!("in interpolation hole: {}", e.message),
                        pos: start,
                    })?;
                    let hole_tokens: Vec<Spanned> = hole_tokens
                        .into_iter()
                        .filter(|t| t.token != Token::Eof)
                        .map(|t| Spanned {
                            token: t.token,
                            span: Span {
                                start: t.span.start + hole_start,
                                end: t.span.end + hole_start,
                            },
                            leading_trivia: t.leading_trivia,
                            trailing_comment: t.trailing_comment,
                            preceded_by_newline: t.preceded_by_newline,
                        })
                        .collect();
                    parts.push(InterpPart::Hole(hole_tokens));
                }
                Some(ch) => {
                    literal.push(ch);
                    self.advance();
                }
            }
        }
    }

    pub fn lex(&mut self) -> Result<Vec<Spanned>, LexError> {
        let mut tokens: Vec<Spanned> = Vec::new();
        let mut pending_trivia: Vec<Trivia> = Vec::new();
        // Track whether we've seen a newline since the last significant token.
        // Start of file counts as "after newline" so first-line comments are leading.
        let mut seen_newline = true;
        // Track consecutive newlines for blank line detection.
        // We count "empty lines" — a newline when we already saw one counts as a blank line.
        let mut prev_was_newline = true; // start of file

        loop {
            self.skip_whitespace();

            let start = self.pos;

            match self.peek() {
                None => {
                    let spanned = self.emit(Token::Eof, start, std::mem::take(&mut pending_trivia), seen_newline && self.nesting == 0);
                    tokens.push(spanned);
                    return Ok(tokens);
                }
                Some('\n') | Some(';') => {
                    self.advance();
                    if prev_was_newline {
                        // Consecutive newline = blank line
                        // Merge with previous BlankLines trivia if present
                        if let Some(Trivia::BlankLines(n)) = pending_trivia.last_mut() {
                            *n += 1;
                        } else {
                            pending_trivia.push(Trivia::BlankLines(1));
                        }
                    }
                    seen_newline = true;
                    prev_was_newline = true;
                    continue;
                }
                Some('#') => {
                    self.advance(); // consume '#'
                    let (text, is_doc) = self.read_comment_text();

                    if !seen_newline && !tokens.is_empty() {
                        // Same line as previous token → trailing comment
                        tokens.last_mut().unwrap().trailing_comment = Some(text);
                    } else {
                        // Own line → leading trivia on next token
                        if is_doc {
                            pending_trivia.push(Trivia::DocComment(text));
                        } else {
                            pending_trivia.push(Trivia::Comment(text));
                        }
                    }

                    // Consume the trailing newline as part of the comment
                    if self.peek() == Some('\n') {
                        self.advance();
                    }
                    seen_newline = true;
                    prev_was_newline = true;
                    continue;
                }
                _ => {}
            }

            // Reset newline tracking — we're about to emit a significant token
            prev_was_newline = false;

            // Capture whether this token is preceded by a newline at top-level nesting.
            // This mirrors the old Terminator behavior: newlines at nesting depth 0
            // signal line boundaries to the parser.
            let newline_flag = seen_newline && self.nesting == 0;

            let trivia = std::mem::take(&mut pending_trivia);

            match self.peek() {
                Some('"') => {
                    let tok = if self.peek_next() == Some('"') && self.peek_ahead(2) == Some('"') {
                        self.advance(); // "
                        self.advance(); // "
                        self.advance(); // "
                        self.read_multiline_string(start)?
                    } else {
                        self.read_string()?
                    };
                    let spanned = self.emit(tok, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('$') if self.peek_next() == Some('"') => {
                    let tok = if self.peek_ahead(2) == Some('"') && self.peek_ahead(3) == Some('"')
                    {
                        self.advance(); // $
                        self.advance(); // "
                        self.advance(); // "
                        self.advance(); // "
                        self.read_multiline_interp_string(start)?
                    } else {
                        self.advance(); // $
                        self.advance(); // "
                        self.read_interp_string(start)?
                    };
                    let spanned = self.emit(tok, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some(ch) if ch.is_ascii_digit() => {
                    let tok = self.read_number();
                    let spanned = self.emit(tok, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                // @"..." raw string or @"""...""" raw multiline string
                Some('@') if self.peek_next() == Some('"') => {
                    let tok = if self.peek_ahead(2) == Some('"') && self.peek_ahead(3) == Some('"')
                    {
                        self.advance(); // @
                        self.advance(); // "
                        self.advance(); // "
                        self.advance(); // "
                        self.read_raw_multiline_string(start)?
                    } else {
                        self.advance(); // @
                        self.read_raw_string(start)?
                    };
                    let spanned = self.emit(tok, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                // Bare @ (not followed by ") — annotation marker
                Some('@') => {
                    self.advance();
                    let spanned = self.emit(Token::At, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some(ch) if ch.is_alphabetic() || ch == '_' => {
                    let mut tok = self.read_identifier();
                    // ident! (no space) → EffectCall, but not ident!=
                    if let Token::Ident(ref name) = tok
                        && self.peek() == Some('!')
                        && self.peek_next() != Some('=')
                    {
                        let name = name.clone();
                        self.advance(); // consume '!'
                        tok = Token::EffectCall(name);
                    }
                    let spanned = self.emit(tok, start, trivia, newline_flag);
                    tokens.push(spanned);
                }

                // Two-character operators
                Some('-') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::Arrow, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('|') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::Pipe, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('<') if self.peek_next() == Some('<') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::ComposeBack, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('<') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::Concat, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('<') if self.peek_next() == Some('|') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::PipeBack, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('=') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::EqEq, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('!') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::NotEq, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('<') if self.peek_next() == Some('-') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::LeftArrow, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('<') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::LtEq, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('>') if self.peek_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::ComposeForward, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('>') if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::GtEq, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('&') if self.peek_next() == Some('&') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::And, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some(':') if self.peek_next() == Some(':') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::DoubleColon, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('.') if self.peek_next() == Some('.') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::DotDot, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                Some('|') if self.peek_next() == Some('|') => {
                    self.advance();
                    self.advance();
                    let spanned = self.emit(Token::Or, start, trivia, newline_flag);
                    tokens.push(spanned);
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
                        '{' => {
                            self.nesting_stack.push(self.nesting);
                            self.nesting = 0;
                            Token::LBrace
                        }
                        '}' => {
                            self.nesting = self.nesting_stack.pop().unwrap_or(0);
                            Token::RBrace
                        }
                        _ => {
                            return Err(LexError {
                                message: format!("unexpected character: {:?}", ch),
                                pos: start,
                            });
                        }
                    };
                    let spanned = self.emit(tok, start, trivia, newline_flag);
                    tokens.push(spanned);
                }
                None => unreachable!(), // handled at top of loop
            }

            seen_newline = false;
        }
    }
}

#[cfg(test)]
mod tests;
