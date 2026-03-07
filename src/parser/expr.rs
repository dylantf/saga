use crate::ast::*;
use crate::token::{Span, Token};
use super::{ParseError, Parser};

impl Parser {
    /// Pratt parser: binary operators with precedence.
    /// Precedence levels:
    ///     1 = piping |>
    ///     2 = or ||
    ///     3 = and &&
    ///     4 = comparison == != < > <= >=
    ///     5 = addition + -
    ///     6 = multiplication * /
    ///     (function application is handled separately, above all binary ops)
    pub fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        let mut left = self.parse_application()?;

        loop {
            // Allow |> to continue an expression across a newline
            if matches!(self.peek(), Token::Terminator) && matches!(self.peek_at(1), Token::Pipe) {
                self.advance(); // skip newline
            }

            let (op, bp) = match self.peek() {
                Token::Pipe => (None, 1),        // desugars to App(right, left)
                Token::PipeBack => (None, 1),    // desugars to App(left, right)
                Token::DoubleColon => (None, 1), // desugars to Cons(left, right), right-assoc
                Token::Or => (Some(BinOp::Or), 2),
                Token::And => (Some(BinOp::And), 3),
                Token::EqEq => (Some(BinOp::Eq), 4),
                Token::NotEq => (Some(BinOp::NotEq), 4),
                Token::Lt => (Some(BinOp::Lt), 5),
                Token::Gt => (Some(BinOp::Gt), 5),
                Token::LtEq => (Some(BinOp::LtEq), 5),
                Token::GtEq => (Some(BinOp::GtEq), 5),
                Token::Concat => (Some(BinOp::Concat), 6),
                Token::Plus => (Some(BinOp::Add), 6),
                Token::Minus => (Some(BinOp::Sub), 6),
                Token::Star => (Some(BinOp::Mul), 7),
                Token::Slash => (Some(BinOp::Div), 7),
                Token::Modulo => (Some(BinOp::Mod), 7),
                _ => break,
            };

            if bp < min_bp {
                break;
            }

            // Remember operator kind before consuming
            let is_backward_pipe = matches!(self.peek(), Token::PipeBack);
            let is_cons = matches!(self.peek(), Token::DoubleColon);
            self.advance(); // consume operator
            // :: is right-associative (recurse at same bp); everything else is left-associative
            let right = self.parse_expr(if is_cons { bp } else { bp + 1 })?;

            let span = left.span().to(right.span());
            left = match op {
                // x :: xs  →  Cons x xs  (right-associative)
                None if is_cons => {
                    let cons = Expr::Constructor {
                        name: "Cons".to_string(),
                        span,
                    };
                    let app1 = Expr::App {
                        func: Box::new(cons),
                        arg: Box::new(left),
                        span,
                    };
                    Expr::App {
                        func: Box::new(app1),
                        arg: Box::new(right),
                        span,
                    }
                }
                // |> forward pipe: `x |> f` becomes `App(f, x)`
                // <| backward pipe: `f <| x` becomes `App(f, x)`
                None if is_backward_pipe => Expr::App {
                    func: Box::new(left),
                    arg: Box::new(right),
                    span,
                },
                None => Expr::App {
                    func: Box::new(right),
                    arg: Box::new(left),
                    span,
                },
                Some(op) => Expr::BinOp {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                    span,
                },
            };
        }

        // `with` has lowest precedence — checked after all binary ops
        if matches!(self.peek(), Token::With) {
            self.advance();
            let handler = self.parse_handler_ref()?;
            let end = self.tokens[self.pos - 1].span;
            left = Expr::With {
                span: left.span().to(end),
                expr: Box::new(left),
                handler: Box::new(handler),
            };
        }

        Ok(left)
    }

    /// Function application: `f x y` → App(App(f, x), y)
    /// Greedily consumes arguments while the next token can start a primary.
    fn parse_application(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_postfix()?;

        while self.can_start_primary() {
            let arg = self.parse_postfix()?;
            let span = expr.span().to(arg.span());
            expr = Expr::App {
                func: Box::new(expr),
                arg: Box::new(arg),
                span,
            };
        }

        Ok(expr)
    }

    /// Postfix operators: field access `.` and qualified effect calls
    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        while matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'

            // Qualified effect call: `Cache.get! key`
            if let Token::EffectCall(name) = self.peek().clone()
                && let Expr::Constructor {
                    name: qualifier, ..
                } = &expr
            {
                let qualifier = qualifier.clone();
                let start_span = expr.span();
                let effect_span = self.tokens[self.pos].span;
                self.advance(); // consume effect call token
                expr = Expr::EffectCall {
                    name,
                    qualifier: Some(qualifier),
                    args: Vec::new(),
                    span: start_span.to(effect_span),
                };
                continue;
            }

            let start = expr.span().start;
            // Module access: `Math.abs` or `Shapes.Circle` -> QualifiedName (bare Constructor LHS only)
            if let Expr::Constructor { name: module, .. } = &expr {
                let module = module.clone();
                let name = match self.peek().clone() {
                    Token::Ident(n) => { self.advance(); n }
                    Token::UpperIdent(n) => { self.advance(); n }
                    tok => return Err(ParseError {
                        message: format!("expected identifier after '.', got {:?}", tok),
                        span: self.tokens[self.pos].span,
                    }),
                };
                let end = self.tokens[self.pos - 1].span;
                expr = Expr::QualifiedName {
                    module,
                    name,
                    span: Span {
                        start,
                        end: end.end,
                    },
                };
                continue;
            }
            let field = self.expect_ident()?;
            let end = self.tokens[self.pos - 1].span;
            expr = Expr::FieldAccess {
                expr: Box::new(expr),
                field,
                span: Span {
                    start,
                    end: end.end,
                },
            };
        }

        Ok(expr)
    }

    /// Parses the handler reference after `with`:
    /// - `with console_log` -> Handler::Named
    /// - `with { h1, h2, op args -> body }` -> Handler::Inline
    pub(super) fn parse_handler_ref(&mut self) -> Result<Handler, ParseError> {
        if matches!(self.peek(), Token::LBrace) {
            self.advance(); // consume '{'
            self.skip_terminators();

            let mut named = Vec::new();
            let mut arms = Vec::new();
            let mut return_clause = None;

            while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                let arm_start = self.tokens[self.pos].span;

                if matches!(self.peek(), Token::Return) {
                    // return clause: `return value -> body`
                    self.advance();
                    let param = self.expect_ident()?;
                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let arm_end = body.span();
                    return_clause = Some(Box::new(HandlerArm {
                        op_name: "return".to_string(),
                        params: vec![param],
                        body: Box::new(body),
                        span: arm_start.to(arm_end),
                    }));
                } else {
                    // Could be a named handler ref or an inline arm.
                    // Named ref: just an ident followed by `,` or `}` or newline
                    // Inline arm: ident [params...] -> body
                    let name = self.expect_ident()?;

                    if matches!(
                        self.peek(),
                        Token::Comma | Token::RBrace | Token::Terminator
                    ) {
                        named.push(name);
                    } else {
                        // Inline arm: op params -> body
                        let mut params = Vec::new();
                        while !matches!(self.peek(), Token::Arrow | Token::Eof) {
                            params.push(self.expect_ident()?);
                        }
                        self.expect(Token::Arrow)?;
                        let body = self.parse_expr(0)?;
                        let arm_end = body.span();
                        arms.push(HandlerArm {
                            op_name: name,
                            params,
                            body: Box::new(body),
                            span: arm_start.to(arm_end),
                        });
                    }
                }

                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                }
                self.skip_terminators();
            }
            self.expect(Token::RBrace)?;

            Ok(Handler::Inline {
                named,
                arms,
                return_clause,
            })
        } else {
            // Single named handler: `with console_log`
            let name = self.expect_ident()?;
            Ok(Handler::Named(name))
        }
    }

    pub(super) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        let span = self.tokens[self.pos].span;

        match self.advance() {
            Token::True => Ok(Expr::Lit {
                value: Lit::Bool(true),
                span,
            }),
            Token::False => Ok(Expr::Lit {
                value: Lit::Bool(false),
                span,
            }),
            Token::Int(n) => Ok(Expr::Lit {
                value: Lit::Int(n),
                span,
            }),
            Token::Float(f) => Ok(Expr::Lit {
                value: Lit::Float(f),
                span,
            }),
            Token::String(s) => Ok(Expr::Lit {
                value: Lit::String(s),
                span,
            }),
            Token::Ident(i) => Ok(Expr::Var { name: i, span }),
            Token::UpperIdent(i) => {
                if matches!(self.peek(), Token::LBrace) {
                    // Record create: User { name: "Dylan", age: 30 }
                    self.advance(); // consume '{'
                    self.skip_terminators();
                    let mut fields = Vec::new();
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        let field_name = self.expect_ident()?;
                        self.expect(Token::Colon)?;
                        let value = self.parse_expr(0)?;
                        fields.push((field_name, value));
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                        self.skip_terminators();
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    Ok(Expr::RecordCreate {
                        name: i,
                        fields,
                        span: span.to(end),
                    })
                } else if matches!(self.peek(), Token::LParen) {
                    // Constructor call: Circle(5), Rect(3, 4)
                    self.advance(); // consume '('
                    let mut args = Vec::new();
                    if !matches!(self.peek(), Token::RParen) {
                        args.push(self.parse_expr(0)?);
                        while matches!(self.peek(), Token::Comma) {
                            self.advance();
                            args.push(self.parse_expr(0)?);
                        }
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RParen)?;
                    let mut expr = Expr::Constructor { name: i, span };
                    for arg in args {
                        expr = Expr::App {
                            func: Box::new(expr),
                            arg: Box::new(arg),
                            span: span.to(end),
                        };
                    }
                    Ok(expr)
                } else {
                    Ok(Expr::Constructor { name: i, span })
                }
            }

            Token::LParen => {
                if matches!(self.peek(), Token::RParen) {
                    self.advance(); // consume ')'
                    Ok(Expr::Lit {
                        value: Lit::Unit,
                        span,
                    })
                } else {
                    let first = self.parse_expr(0)?;
                    if matches!(self.peek(), Token::Comma) {
                        // Tuple: (a, b, ...)
                        let mut elements = vec![first];
                        while matches!(self.peek(), Token::Comma) {
                            self.advance();
                            if matches!(self.peek(), Token::RParen) {
                                break; // trailing comma
                            }
                            elements.push(self.parse_expr(0)?);
                        }
                        let end = self.tokens[self.pos].span;
                        self.expect(Token::RParen)?;
                        Ok(Expr::Tuple {
                            elements,
                            span: span.to(end),
                        })
                    } else {
                        self.expect(Token::RParen)?;
                        Ok(first)
                    }
                }
            }

            // List literal: [e1, e2, e3]
            // Desugars to: Cons(e1, Cons(e2, Cons(e3, Nil)))
            Token::LBracket => {
                let mut elements = Vec::new();
                while !matches!(self.peek(), Token::RBracket | Token::Eof) {
                    elements.push(self.parse_expr(0)?);
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBracket)?;

                // Build from right to left: Nil, then wrap each element
                let mut result = Expr::Constructor {
                    name: "Nil".to_string(),
                    span: end,
                };
                for elem in elements.into_iter().rev() {
                    let elem_span = elem.span();
                    let cons = Expr::Constructor {
                        name: "Cons".to_string(),
                        span: elem_span,
                    };
                    let app1 = Expr::App {
                        func: Box::new(cons),
                        arg: Box::new(elem),
                        span: elem_span,
                    };
                    result = Expr::App {
                        func: Box::new(app1),
                        arg: Box::new(result),
                        span: elem_span.to(end),
                    };
                }
                Ok(result)
            }

            Token::Fun => {
                let mut params = Vec::new();
                while !matches!(self.peek(), Token::Arrow | Token::Eof) {
                    params.push(self.parse_pattern()?);
                }
                self.expect(Token::Arrow)?;

                let body = self.parse_expr(0)?;
                let end_span = body.span();

                Ok(Expr::Lambda {
                    params,
                    body: Box::new(body),
                    span: span.to(end_span),
                })
            }

            Token::LBrace => {
                self.skip_terminators();

                // Check for record update: { expr | field: val, ... }
                // We don't start with `let`, so try parsing an expression,
                // then check if the next token is `|`
                if !matches!(self.peek(), Token::Let | Token::RBrace | Token::Mut) {
                    let save = self.pos;
                    let first_expr = self.parse_expr(0);

                    if let Ok(record) = first_expr
                        && matches!(self.peek(), Token::Bar)
                    {
                        self.advance(); // consume '|'
                        self.skip_terminators();
                        let mut fields = Vec::new();
                        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                            let field_name = self.expect_ident()?;
                            self.expect(Token::Colon)?;
                            let value = self.parse_expr(0)?;
                            fields.push((field_name, value));
                            if matches!(self.peek(), Token::Comma) {
                                self.advance();
                            }
                            self.skip_terminators();
                        }
                        let end = self.tokens[self.pos].span;
                        self.expect(Token::RBrace)?;
                        return Ok(Expr::RecordUpdate {
                            record: Box::new(record),
                            fields,
                            span: span.to(end),
                        });
                    }

                    // Not a record update — backtrack and parse as block
                    self.pos = save;
                }

                let mut stmts: Vec<Stmt> = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    if matches!(self.peek(), Token::Let) {
                        let let_start = self.tokens[self.pos].span;
                        self.advance(); // consume 'let'
                        let mutable = matches!(self.peek(), Token::Mut);
                        if mutable {
                            self.advance(); // consume 'mut'
                        }
                        let pattern = self.parse_pattern()?;
                        self.expect(Token::Eq)?;
                        let value = self.parse_expr(0)?;
                        let stmt_span = let_start.to(value.span());
                        stmts.push(Stmt::Let {
                            pattern,
                            value,
                            mutable,
                            span: stmt_span,
                        });
                    } else {
                        // Parse expression, then check for `<-` assignment
                        let expr = self.parse_expr(0)?;
                        if matches!(self.peek(), Token::ArrowBack) {
                            // name <- value (assignment to mutable binding)
                            if let Expr::Var { name, .. } = &expr {
                                let name = name.clone();
                                self.advance(); // consume '<-'
                                let value = self.parse_expr(0)?;
                                let stmt_span = expr.span().to(value.span());
                                stmts.push(Stmt::Assign {
                                    name,
                                    value,
                                    span: stmt_span,
                                });
                            } else {
                                return Err(ParseError {
                                    message: "left side of <- must be a variable name".to_string(),
                                    span: expr.span(),
                                });
                            }
                        } else {
                            stmts.push(Stmt::Expr(expr));
                        }
                    }
                    self.skip_terminators();
                }
                let end_span = self.tokens[self.pos].span; // the RBrace
                self.expect(Token::RBrace)?;
                Ok(Expr::Block {
                    stmts,
                    span: span.to(end_span),
                })
            }

            Token::If => {
                let cond = self.parse_expr(0)?;
                self.skip_terminators();
                self.expect(Token::Then)?;

                let then_branch = self.parse_expr(0)?;
                self.skip_terminators();
                self.expect(Token::Else)?;

                let else_branch = self.parse_expr(0)?;
                let end_span = else_branch.span();

                Ok(Expr::If {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                    span: span.to(end_span),
                })
            }

            Token::Case => {
                let scrutinee = self.parse_expr(0)?;
                self.expect(Token::LBrace)?;
                self.skip_terminators();

                let mut branches = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;

                    let guard = if matches!(self.peek(), Token::If) {
                        self.advance();
                        Some(self.parse_expr(0)?)
                    } else {
                        None
                    };

                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span().end;
                    branches.push(CaseArm {
                        pattern,
                        guard,
                        body,
                        span: Span {
                            start: arm_start.start,
                            end: end_span,
                        },
                    });
                    self.skip_terminators();
                }

                let end = self.tokens[self.pos].span; // the RBrace
                self.expect(Token::RBrace)?;

                Ok(Expr::Case {
                    scrutinee: Box::new(scrutinee),
                    arms: branches,
                    span: span.to(end),
                })
            }

            // Unary negation
            Token::Minus => {
                let expr = self.parse_primary()?;
                let end_span = expr.span().end;
                Ok(Expr::UnaryMinus {
                    expr: Box::new(expr),
                    span: Span {
                        start: span.start,
                        end: end_span,
                    },
                })
            }

            // Effect call: `log! "hello"` args handled by parse_application
            Token::EffectCall(name) => Ok(Expr::EffectCall {
                name,
                qualifier: None,
                args: Vec::new(),
                span,
            }),

            // Resume: `resume value`
            Token::Resume => {
                let value = self.parse_expr(0)?;
                let end = value.span();
                Ok(Expr::Resume {
                    value: Box::new(value),
                    span: span.to(end),
                })
            }

            tok => {
                self.pos -= 1; // put back
                Err(ParseError {
                    message: format!("expected expression, got {:?}", tok),
                    span: self.tokens[self.pos].span,
                })
            }
        }
    }
}
