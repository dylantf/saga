use super::{ParseError, Parser};
use crate::ast::*;
use crate::token::Token;

impl Parser {
    pub fn parse_pattern(&mut self) -> Result<Pat, ParseError> {
        let start = self.tokens[self.pos].span;
        let pat = self.parse_pattern_atom()?;

        // x :: xs  -> ConsPat (desugars to Cons(x, xs) before typechecking)
        if matches!(self.peek(), Token::DoubleColon) {
            self.advance(); // consume ::
            let tail = self.parse_pattern()?;
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
                    let rest = self.parse_pattern()?;
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
                Pat::Constructor { name, args, span, .. } if args.is_empty() => {
                    self.advance(); // consume 'as'
                    let as_ident = self.expect_ident()?;
                    let end = self.tokens[self.pos - 1].span;
                    return Ok(Pat::Record {
                        id: NodeId::fresh(),
                        name,
                        fields: vec![],
                        as_name: Some(as_ident),
                        span: span.to(end),
                    });
                }
                Pat::Record { id, name, fields, span, .. } => {
                    self.advance(); // consume 'as'
                    let as_ident = self.expect_ident()?;
                    let end = self.tokens[self.pos - 1].span;
                    return Ok(Pat::Record {
                        id,
                        name,
                        fields,
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
                if matches!(self.peek(), Token::LParen) {
                    // Constructor with args: Some(x), Shapes.Circle(r), Ok(())
                    self.advance(); // consume '('
                    // Handle Ok(()) — unit arg
                    if matches!(self.peek(), Token::RParen) {
                        let end = self.tokens[self.pos].span;
                        self.advance(); // consume ')'
                        return Ok(Pat::Constructor {
                            id: NodeId::fresh(),
                            name,
                            args: vec![Pat::Lit {
                                id: NodeId::fresh(),
                                value: Lit::Unit,
                                span: span.to(end),
                            }],
                            span: span.to(end),
                        });
                    }
                    let mut args = vec![self.parse_pattern()?];
                    while matches!(self.peek(), Token::Comma) {
                        self.advance();
                        args.push(self.parse_pattern()?);
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RParen)?;
                    Ok(Pat::Constructor {
                        id: NodeId::fresh(),
                        name,
                        args,
                        span: span.to(end),
                    })
                } else if matches!(self.peek(), Token::LBrace) {
                    // Record pattern: User { name, age: a }
                    self.advance(); // consume '{'
                    let mut fields = Vec::new();
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
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
                // Anonymous record pattern: { field, field: pat, ... }
                let mut fields = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
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
                    span: span.to(end),
                })
            }
            Token::Ident(s) if s == "_" => Ok(Pat::Wildcard { id: NodeId::fresh(), span }),
            Token::Ident(s) => Ok(Pat::Var { id: NodeId::fresh(), name: s, span }),
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
            tok => {
                self.pos -= 1;
                Err(ParseError {
                    message: format!("expected pattern, got {:?}", tok),
                    span: self.tokens[self.pos].span,
                })
            }
        }
    }
}
