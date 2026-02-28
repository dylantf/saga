use crate::ast::*;
use crate::token::{Span, Spanned, Token};

pub struct Parser {
    tokens: Vec<Spanned>,
    pos: usize,
}

pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl Parser {
    // --- Helpers ---

    pub fn new(tokens: Vec<Spanned>) -> Self {
        Parser { tokens, pos: 0 }
    }

    pub fn peek(&self) -> &Token {
        &self.tokens[self.pos].token
    }

    pub fn peek_at(&self, offset: usize) -> &Token {
        let idx = self.pos + offset;
        if idx < self.tokens.len() {
            &self.tokens[idx].token
        } else {
            &self.tokens[self.tokens.len() - 1].token
        }
    }

    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].token.clone();
        self.pos += 1;
        tok
    }

    fn expect(&mut self, expected: Token) -> Result<(), ParseError> {
        let tok = self.advance();
        if tok == expected {
            Ok(())
        } else {
            Err(ParseError {
                message: format!("Expected {:?}, got {:?}", expected, tok),
                span: self.tokens[self.pos - 1].span,
            })
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::Ident(s) => Ok(s),
            tok => Err(ParseError {
                message: format!("expected identifier, got {:?}", tok),
                span: self.tokens[self.pos - 1].span,
            }),
        }
    }

    fn expect_upper_ident(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::UpperIdent(s) => Ok(s),
            tok => Err(ParseError {
                message: format!("expected type, got {:?}", tok),
                span: self.tokens[self.pos - 1].span,
            }),
        }
    }

    fn skip_terminators(&mut self) {
        while matches!(self.peek(), Token::Terminator) {
            self.advance();
        }
    }

    // Determines whether the next token can start a primary expression.
    // Used by parse_application to know when to keep consuming arguments.
    fn can_start_primary(&self) -> bool {
        matches!(
            self.peek(),
            Token::Int(_)
                | Token::Float(_)
                | Token::String(_)
                | Token::True
                | Token::False
                | Token::Ident(_)
                | Token::UpperIdent(_)
                | Token::LParen
                | Token::LBrace
        )
    }

    fn can_start_type_atom(&self) -> bool {
        matches!(
            self.peek(),
            Token::UpperIdent(_) | Token::Ident(_) | Token::LParen
        )
    }

    // --- Program ---

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        self.skip_terminators();
        let mut decls = Vec::new();
        while !matches!(self.peek(), Token::Eof) {
            decls.push(self.parse_decl()?);
            self.skip_terminators();
        }
        Ok(decls)
    }

    // --- Declarations ---

    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        match self.peek() {
            Token::Type => self.parse_type_def(),
            Token::Pub => {
                let start = self.tokens[self.pos].span;
                self.advance(); // consume 'pub'
                self.parse_fun_annotation(true, start)
            }
            Token::Fun => {
                let start = self.tokens[self.pos].span;
                self.parse_fun_annotation(false, start)
            }
            Token::Ident(_) => self.parse_fun_binding(),
            _ => Err(ParseError {
                message: format!("Expected declaration, got {:?}", self.peek()),
                span: self.tokens[self.pos].span,
            }),
        }
    }

    fn parse_type_def(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'type'
        let name = self.expect_upper_ident()?;
        let mut type_params = Vec::new();
        while !matches!(self.peek(), Token::LBrace | Token::Eof) {
            type_params.push(self.expect_ident()?);
        }
        self.expect(Token::LBrace)?;
        self.skip_terminators();
        let mut variants = Vec::new();
        while !matches!(self.peek(), Token::RBrace) {
            variants.push(self.parse_type_constructor_def()?);
            self.skip_terminators();
        }
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::TypeDef {
            name,
            type_params,
            variants,
            span: Span {
                start: start.start,
                end: end.end,
            },
        })
    }

    // Parses a single constructor inside a type def, e.g. `Some(a)` or `None`
    fn parse_type_constructor_def(&mut self) -> Result<TypeConstructor, ParseError> {
        let start = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let mut fields = Vec::new();

        if matches!(self.peek(), Token::LParen) {
            self.advance();
            fields.push(self.parse_type_expr()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                fields.push(self.parse_type_expr()?);
            }
            self.expect(Token::RParen)?;
        }

        let end = self.tokens[self.pos - 1].span;
        Ok(TypeConstructor {
            name,
            fields,
            span: Span {
                start: start.start,
                end: end.end,
            },
        })
    }

    // Parses: [pub] fun <name> (<p>: <Type>) ... -> <ReturnType> [with {Effect, ...}]
    fn parse_fun_annotation(&mut self, public: bool, start: Span) -> Result<Decl, ParseError> {
        self.advance(); // consume 'fun'
        let name = self.expect_ident()?;

        let mut params = Vec::new();
        while matches!(self.peek(), Token::LParen) {
            self.advance(); // consume '('
            let param_name = self.expect_ident()?;
            self.expect(Token::Colon)?;
            let param_type = self.parse_type_expr()?;
            self.expect(Token::RParen)?;
            params.push((param_name, param_type));
        }

        self.expect(Token::Arrow)?;
        let return_type = self.parse_type_expr()?;

        let mut effects = Vec::new();
        if matches!(self.peek(), Token::With) {
            self.advance(); // consume 'with'
            self.expect(Token::LBrace)?;
            effects.push(self.expect_upper_ident()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                effects.push(self.expect_upper_ident()?);
            }
            self.expect(Token::RBrace)?;
        }

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::FunAnnotation {
            public,
            name,
            params,
            return_type,
            effects,
            span: Span {
                start: start.start,
                end: end.end,
            },
        })
    }

    // Parses: <name> <pat> ... [if <guard>] = <body>
    fn parse_fun_binding(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        let name = self.expect_ident()?;

        let mut params = Vec::new();
        while !matches!(self.peek(), Token::Eq | Token::If | Token::Eof) {
            params.push(self.parse_pattern()?);
        }

        let guard = if matches!(self.peek(), Token::If) {
            self.advance();
            Some(Box::new(self.parse_expr(0)?))
        } else {
            None
        };

        self.expect(Token::Eq)?;
        let body = self.parse_expr(0)?;

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::FunBinding {
            name,
            params,
            guard,
            body,
            span: Span {
                start: start.start,
                end: end.end,
            },
        })
    }

    // --- Type expressions ---

    fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        // First: parse a type with possible application (`Option a`, `Result a e`)
        let mut left = self.parse_type_atom()?;
        while self.can_start_type_atom() {
            let arg = self.parse_type_atom()?;
            left = TypeExpr::App(Box::new(left), Box::new(arg));
        }

        // Then: check for arrow (right-associative)
        if matches!(self.peek(), Token::Arrow) {
            self.advance();
            let right = self.parse_type_expr()?; // recurse = right-associative
            Ok(TypeExpr::Arrow(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_type_atom(&mut self) -> Result<TypeExpr, ParseError> {
        match self.advance() {
            Token::UpperIdent(s) => Ok(TypeExpr::Named(s)),
            Token::Ident(s) => Ok(TypeExpr::Var(s)),
            Token::LParen => {
                let inner = self.parse_type_expr()?;
                self.expect(Token::RParen)?;
                Ok(inner)
            }
            tok => {
                self.pos -= 1; // put back
                Err(ParseError {
                    message: format!("expected type, got {:?}", tok),
                    span: self.tokens[self.pos].span,
                })
            }
        }
    }

    // --- Expressions ---

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
                Token::Pipe => (None, 1),     // desugars to App(right, left)
                Token::PipeBack => (None, 1), // desugars to App(left, right)
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

            // Remember if this is a backward pipe before consuming
            let is_backward_pipe = matches!(self.peek(), Token::PipeBack);
            self.advance(); // consume operator
            let right = self.parse_expr(bp + 1)?; // +1 = left-associative

            let span = Span {
                start: left.span().start,
                end: right.span().end,
            };
            left = match op {
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

        Ok(left)
    }

    /// Function application: `f x y` → App(App(f, x), y)
    /// Greedily consumes arguments while the next token can start a primary.
    fn parse_application(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        while self.can_start_primary() {
            let arg = self.parse_primary()?;
            let span = Span {
                start: expr.span().start,
                end: arg.span().end,
            };
            expr = Expr::App {
                func: Box::new(expr),
                arg: Box::new(arg),
                span,
            };
        }

        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
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
            Token::UpperIdent(i) => Ok(Expr::Constructor { name: i, span }),

            Token::LParen => {
                let inner = self.parse_expr(0)?;
                self.expect(Token::RParen)?;
                Ok(inner)
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
                    span: Span {
                        start: span.start,
                        end: end_span.end,
                    },
                })
            }

            Token::LBrace => {
                self.skip_terminators();
                let mut stmts: Vec<Stmt> = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    if matches!(self.peek(), Token::Let) {
                        let let_start = self.tokens[self.pos].span;
                        self.advance(); // consume 'let'
                        let name = self.expect_ident()?;
                        self.expect(Token::Eq)?;
                        let value = self.parse_expr(0)?;
                        let stmt_span = Span {
                            start: let_start.start,
                            end: value.span().end,
                        };
                        stmts.push(Stmt::Let {
                            name,
                            value,
                            span: stmt_span,
                        });
                    } else {
                        stmts.push(Stmt::Expr(self.parse_expr(0)?));
                    }
                    self.skip_terminators();
                }
                let end_span = self.tokens[self.pos].span; // the RBrace
                self.expect(Token::RBrace)?;
                Ok(Expr::Block {
                    stmts,
                    span: Span {
                        start: span.start,
                        end: end_span.end,
                    },
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
                    span: Span {
                        start: span.start,
                        end: end_span.end,
                    },
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
                    span: Span {
                        start: span.start,
                        end: end.end,
                    },
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

            tok => {
                self.pos -= 1; // put back
                Err(ParseError {
                    message: format!("expected expression, got {:?}", tok),
                    span: self.tokens[self.pos].span,
                })
            }
        }
    }

    // --- Patterns ---

    fn parse_pattern(&mut self) -> Result<Pat, ParseError> {
        let span = self.tokens[self.pos].span;

        match self.advance() {
            Token::UpperIdent(s) => {
                if matches!(self.peek(), Token::LParen) {
                    // Constructor with args: Some(x), Cons(a, b)
                    self.advance(); // consume '('
                    let mut args = vec![self.parse_pattern()?];
                    while matches!(self.peek(), Token::Comma) {
                        self.advance();
                        args.push(self.parse_pattern()?);
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RParen)?;
                    Ok(Pat::Constructor {
                        name: s,
                        args,
                        span: Span {
                            start: span.start,
                            end: end.end,
                        },
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
                        name: s,
                        fields,
                        span: Span {
                            start: span.start,
                            end: end.end,
                        },
                    })
                } else {
                    // Bare constructor: None
                    Ok(Pat::Constructor {
                        name: s,
                        args: vec![],
                        span,
                    })
                }
            }
            Token::Ident(s) if s.starts_with('_') => Ok(Pat::Wildcard { span }),
            Token::Ident(s) => Ok(Pat::Var { name: s, span }),
            Token::Int(n) => Ok(Pat::Lit {
                value: Lit::Int(n),
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
