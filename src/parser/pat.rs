use super::{ParseError, Parser};
use crate::ast::*;
use crate::token::Token;

impl Parser {
    pub fn parse_pattern(&mut self) -> Result<Pat, ParseError> {
        let start = self.tokens[self.pos].span;
        let pat = self.parse_pattern_atom()?;

        // x :: xs  -> Cons(x, xs)  (right-associative: recurse into parse_pattern)
        if matches!(self.peek(), Token::DoubleColon) {
            self.advance(); // consume ::
            let tail = self.parse_pattern()?;
            let end = self.tokens[self.pos - 1].span;
            return Ok(Pat::Constructor {
                name: "Cons".to_string(),
                args: vec![pat, tail],
                span: start.to(end),
            });
        }

        Ok(pat)
    }

    fn parse_pattern_atom(&mut self) -> Result<Pat, ParseError> {
        let span = self.tokens[self.pos].span;

        match self.advance() {
            Token::UpperIdent(s) => {
                // Support qualified constructor patterns: `Module.Name` or bare `Name`
                let name = if matches!(self.peek(), Token::Dot) {
                    self.advance(); // consume '.'
                    let base = self.expect_upper_ident()?;
                    format!("{}.{}", s, base)
                } else {
                    s
                };
                if matches!(self.peek(), Token::LParen) {
                    // Constructor with args: Some(x), Shapes.Circle(r)
                    self.advance(); // consume '('
                    let mut args = vec![self.parse_pattern()?];
                    while matches!(self.peek(), Token::Comma) {
                        self.advance();
                        args.push(self.parse_pattern()?);
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RParen)?;
                    Ok(Pat::Constructor {
                        name,
                        args,
                        span: span.to(end),
                    })
                } else if matches!(self.peek(), Token::LBrace) {
                    // Record pattern: User { name, age: a }
                    self.advance(); // consume '{'
                    self.skip_terminators();
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
                        self.skip_terminators();
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    Ok(Pat::Record {
                        name,
                        fields,
                        span: span.to(end),
                    })
                } else {
                    // Bare constructor: None, or qualified: Shapes.None
                    Ok(Pat::Constructor {
                        name,
                        args: vec![],
                        span,
                    })
                }
            }
            Token::Ident(s) if s.starts_with('_') => Ok(Pat::Wildcard { span }),
            Token::Ident(s) => Ok(Pat::Var { name: s, span }),
            Token::Minus => match self.advance() {
                Token::Int(n) => Ok(Pat::Lit {
                    value: Lit::Int(-n),
                    span: span.to(self.tokens[self.pos - 1].span),
                }),
                Token::Float(f) => Ok(Pat::Lit {
                    value: Lit::Float(-f),
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
            Token::Int(n) => Ok(Pat::Lit {
                value: Lit::Int(n),
                span,
            }),
            Token::Float(f) => Ok(Pat::Lit {
                value: Lit::Float(f),
                span,
            }),
            Token::True => Ok(Pat::Lit {
                value: Lit::Bool(true),
                span,
            }),
            Token::False => Ok(Pat::Lit {
                value: Lit::Bool(false),
                span,
            }),
            Token::LParen => {
                if matches!(self.peek(), Token::RParen) {
                    self.advance();
                    Ok(Pat::Lit {
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

                // Build from right to left: Nil, then wrap each element in Cons
                let mut result = Pat::Constructor {
                    name: "Nil".to_string(),
                    args: vec![],
                    span: end,
                };
                for elem in elements.into_iter().rev() {
                    result = Pat::Constructor {
                        name: "Cons".to_string(),
                        args: vec![elem, result],
                        span: span.to(end),
                    };
                }
                Ok(result)
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
