use super::{ParseError, Parser};
use crate::ast::*;
use crate::token::Token;

impl Parser {
    pub fn parse_pattern(&mut self) -> Result<Pat, ParseError> {
        let start = self.tokens[self.pos].span;
        let pat = self.parse_pattern_branch()?;

        // Or-pattern: A | B | C
        if matches!(self.peek(), Token::Bar) {
            let mut patterns = vec![pat];
            while matches!(self.peek(), Token::Bar) {
                self.advance(); // consume |
                patterns.push(self.parse_pattern_branch()?);
            }
            let end = patterns.last().unwrap().span();
            return Ok(Pat::Or {
                id: NodeId::fresh(),
                patterns,
                span: start.to(end),
            });
        }

        Ok(pat)
    }

    /// Parse a single pattern branch (everything except or-patterns).
    /// Or-patterns are handled by `parse_pattern` which chains branches with `|`.
    fn parse_pattern_branch(&mut self) -> Result<Pat, ParseError> {
        let start = self.tokens[self.pos].span;
        let pat = self.parse_pattern_atom()?;

        // x :: xs  -> ConsPat (desugars to Cons(x, xs) before typechecking)
        if matches!(self.peek(), Token::DoubleColon) {
            self.advance(); // consume ::
            let tail = self.parse_pattern_branch()?;
            let end = self.tokens[self.pos - 1].span;
            return Ok(Pat::ConsPat {
                id: NodeId::fresh(),
                head: Box::new(pat),
                tail: Box::new(tail),
                span: start.to(end),
            });
        }

        // "prefix" <> rest  -> StringPrefix(prefix, rest)  (right-associative)
        if matches!(self.peek(), Token::Concat) {
            self.advance(); // consume <>
            match pat {
                Pat::Lit {
                    value: Lit::String(prefix, _),
                    ..
                } => {
                    let rest = self.parse_pattern_branch()?;
                    let end = self.tokens[self.pos - 1].span;
                    return Ok(Pat::StringPrefix {
                        id: NodeId::fresh(),
                        prefix,
                        rest: Box::new(rest),
                        span: start.to(end),
                    });
                }
                _ => {
                    return Err(ParseError {
                        message: "string concat pattern requires a string literal on the left"
                            .to_string(),
                        span: start,
                    });
                }
            }
        }

        // Record as-pattern: Student as s, Student { name } as s
        if matches!(self.peek(), Token::As) {
            match pat {
                Pat::Constructor {
                    name, args, span, ..
                } if args.is_empty() => {
                    self.advance(); // consume 'as'
                    let as_ident = self.expect_ident()?;
                    let end = self.tokens[self.pos - 1].span;
                    return Ok(Pat::Record {
                        id: NodeId::fresh(),
                        name,
                        fields: vec![],
                        rest: true,
                        as_name: Some(as_ident),
                        span: span.to(end),
                    });
                }
                Pat::Record {
                    id,
                    name,
                    fields,
                    rest,
                    span,
                    ..
                } => {
                    self.advance(); // consume 'as'
                    let as_ident = self.expect_ident()?;
                    let end = self.tokens[self.pos - 1].span;
                    return Ok(Pat::Record {
                        id,
                        name,
                        fields,
                        rest,
                        as_name: Some(as_ident),
                        span: span.to(end),
                    });
                }
                _ => {
                    return Err(ParseError {
                        message: "'as' patterns are only supported on record patterns".to_string(),
                        span: start,
                    });
                }
            }
        }

        Ok(pat)
    }

    /// Check if the next token can start a pattern argument for a constructor.
    /// Used for space-separated constructor args: `Just x`, `Foo a b`.
    fn can_start_pattern_arg(&self) -> bool {
        matches!(
            self.peek(),
            Token::Ident(_)
                | Token::UpperIdent(_)
                | Token::Int(..)
                | Token::Float(..)
                | Token::String(..)
                | Token::True
                | Token::False
                | Token::LParen
                | Token::LBracket
                | Token::Minus
        )
    }

    fn parse_pattern_atom(&mut self) -> Result<Pat, ParseError> {
        let span = self.tokens[self.pos].span;

        match self.advance() {
            Token::UpperIdent(s) => {
                // Support qualified constructor patterns: `Module.Name`, `A.B.Name`, or bare `Name`
                let mut name = s;
                let mut name_end = span;
                while matches!(self.peek(), Token::Dot) {
                    self.advance(); // consume '.'
                    let segment = self.expect_upper_ident()?;
                    name_end = self.tokens[self.pos - 1].span;
                    name = format!("{}.{}", name, segment);
                }
                if matches!(self.peek(), Token::LBrace) {
                    // Record pattern: User { name, age: a } or User { name, .. }
                    self.advance(); // consume '{'
                    let mut fields = Vec::new();
                    let mut rest = false;
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        if matches!(self.peek(), Token::DotDot) {
                            self.advance();
                            rest = true;
                            // consume optional trailing comma
                            if matches!(self.peek(), Token::Comma) {
                                self.advance();
                            }
                            break;
                        }
                        let field_name = self.expect_ident()?;
                        let alias = if matches!(self.peek(), Token::Colon) {
                            self.advance();
                            Some(self.parse_pattern()?)
                        } else {
                            None
                        };
                        fields.push((field_name, alias));
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    Ok(Pat::Record {
                        id: NodeId::fresh(),
                        name,
                        fields,
                        rest,
                        as_name: None,
                        span: span.to(end),
                    })
                } else {
                    // Constructor with optional space-separated args: Just x, Foo a b
                    // Greedily consume pattern atoms until a delimiter is reached.
                    let mut args = Vec::new();
                    while self.can_start_pattern_arg() {
                        args.push(self.parse_pattern_atom()?);
                    }
                    let end = if args.is_empty() {
                        name_end
                    } else {
                        self.tokens[self.pos - 1].span
                    };
                    Ok(Pat::Constructor {
                        id: NodeId::fresh(),
                        name,
                        args,
                        span: span.to(end),
                    })
                }
            }
            Token::LBrace => {
                // Anonymous record pattern: { field, field: pat, .. }
                let mut fields = Vec::new();
                let mut rest = false;
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    if matches!(self.peek(), Token::DotDot) {
                        self.advance();
                        rest = true;
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                        break;
                    }
                    let field_name = self.expect_ident()?;
                    let alias = if matches!(self.peek(), Token::Colon) {
                        self.advance();
                        Some(self.parse_pattern()?)
                    } else {
                        None
                    };
                    fields.push((field_name, alias));
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBrace)?;
                Ok(Pat::AnonRecord {
                    id: NodeId::fresh(),
                    fields,
                    rest,
                    span: span.to(end),
                })
            }
            Token::Ident(s) if s == "_" => Ok(Pat::Wildcard {
                id: NodeId::fresh(),
                span,
            }),
            Token::Ident(s) => Ok(Pat::Var {
                id: NodeId::fresh(),
                name: s,
                span,
            }),
            Token::Minus => match self.advance() {
                Token::Int(s, n) => Ok(Pat::Lit {
                    id: NodeId::fresh(),
                    value: Lit::Int(format!("-{}", s), -n),
                    span: span.to(self.tokens[self.pos - 1].span),
                }),
                Token::Float(s, f) => Ok(Pat::Lit {
                    id: NodeId::fresh(),
                    value: Lit::Float(format!("-{}", s), -f),
                    span: span.to(self.tokens[self.pos - 1].span),
                }),
                tok => {
                    self.pos -= 1;
                    Err(ParseError {
                        message: format!("expected number after '-' in pattern, got {:?}", tok),
                        span: self.tokens[self.pos].span,
                    })
                }
            },
            Token::String(s, kind) => Ok(Pat::Lit {
                id: NodeId::fresh(),
                value: Lit::String(s, kind),
                span,
            }),
            Token::Int(s, n) => Ok(Pat::Lit {
                id: NodeId::fresh(),
                value: Lit::Int(s, n),
                span,
            }),
            Token::Float(s, f) => Ok(Pat::Lit {
                id: NodeId::fresh(),
                value: Lit::Float(s, f),
                span,
            }),
            Token::True => Ok(Pat::Lit {
                id: NodeId::fresh(),
                value: Lit::Bool(true),
                span,
            }),
            Token::False => Ok(Pat::Lit {
                id: NodeId::fresh(),
                value: Lit::Bool(false),
                span,
            }),
            Token::LParen => {
                if matches!(self.peek(), Token::RParen) {
                    self.advance();
                    Ok(Pat::Lit {
                        id: NodeId::fresh(),
                        value: Lit::Unit,
                        span,
                    })
                } else {
                    let first = self.parse_pattern()?;
                    if matches!(self.peek(), Token::Comma) {
                        // Tuple pattern: (a, b, ...)
                        let mut elements = vec![first];
                        while matches!(self.peek(), Token::Comma) {
                            self.advance();
                            if matches!(self.peek(), Token::RParen) {
                                break;
                            }
                            elements.push(self.parse_pattern()?);
                        }
                        let end = self.tokens[self.pos].span;
                        self.expect(Token::RParen)?;
                        Ok(Pat::Tuple {
                            id: NodeId::fresh(),
                            elements,
                            span: span.to(end),
                        })
                    } else {
                        self.expect(Token::RParen)?;
                        Ok(first)
                    }
                }
            }
            Token::LBracket => {
                let mut elements = Vec::new();
                while !matches!(self.peek(), Token::RBracket | Token::Eof) {
                    elements.push(self.parse_pattern()?);
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBracket)?;

                Ok(Pat::ListPat {
                    id: NodeId::fresh(),
                    elements,
                    span: span.to(end),
                })
            }
            // <<seg, seg, ...>> -- bitstring pattern
            Token::ComposeBack => {
                // <<>> -- empty bitstring pattern
                if matches!(self.peek(), Token::ComposeForward) {
                    let end = self.tokens[self.pos].span;
                    self.advance(); // consume >>
                    return Ok(Pat::BitStringPat {
                        id: NodeId::fresh(),
                        segments: vec![],
                        span: span.to(end),
                    });
                }

                let mut segments = Vec::new();
                loop {
                    let seg = self.parse_bit_segment_pat()?;
                    segments.push(seg);
                    if matches!(self.peek(), Token::Comma) {
                        self.advance(); // consume ,
                    } else {
                        break;
                    }
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::ComposeForward)?; // consume >>
                Ok(Pat::BitStringPat {
                    id: NodeId::fresh(),
                    segments,
                    span: span.to(end),
                })
            }

            tok => {
                self.pos -= 1;
                Err(ParseError {
                    message: format!("expected pattern, got {:?}", tok),
                    span: self.tokens[self.pos].span,
                })
            }
        }
    }

    /// Parse a single bitstring segment in pattern position.
    fn parse_bit_segment_pat(&mut self) -> Result<BitSegment<Pat>, ParseError> {
        let start = self.tokens[self.pos].span;
        let value = self.parse_pattern_atom()?;

        let size = if matches!(self.peek(), Token::Colon) {
            self.advance(); // consume :
            // Size is an int literal or variable name
            let size_expr = match self.peek().clone() {
                Token::Int(s, n) => {
                    let sp = self.tokens[self.pos].span;
                    self.advance();
                    Expr {
                        id: NodeId::fresh(),
                        span: sp,
                        kind: ExprKind::Lit {
                            value: Lit::Int(s, n),
                        },
                    }
                }
                Token::Ident(name) => {
                    let sp = self.tokens[self.pos].span;
                    self.advance();
                    Expr {
                        id: NodeId::fresh(),
                        span: sp,
                        kind: ExprKind::Var { name },
                    }
                }
                _ => {
                    return Err(ParseError {
                        message: "expected integer or variable for segment size".to_string(),
                        span: self.tokens[self.pos].span,
                    });
                }
            };
            Some(Box::new(size_expr))
        } else {
            None
        };

        let specs = if matches!(self.peek(), Token::Slash) {
            self.advance(); // consume /
            self.parse_bit_specs()?
        } else {
            vec![]
        };

        let end = self.tokens[self.pos - 1].span;
        Ok(BitSegment {
            value,
            size,
            specs,
            span: start.to(end),
        })
    }
}
