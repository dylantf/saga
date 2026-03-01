use crate::ast::*;
use crate::token::{Span, Spanned, Token};

pub struct Parser {
    tokens: Vec<Spanned>,
    pos: usize,
}

#[derive(Debug)]
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
                | Token::LBracket
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
            Token::Record => self.parse_record_def(),
            Token::Let => {
                let start = self.tokens[self.pos].span;
                self.advance(); // consume 'let'
                let name = self.expect_ident()?;
                self.expect(Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Decl::Let {
                    span: start.to(value.span()),
                    name,
                    value,
                })
            }
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

    // Parses: record <Name> { <field>: <Type>, ... }
    fn parse_record_def(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'record'
        let name = self.expect_upper_ident()?;
        self.expect(Token::LBrace)?;
        self.skip_terminators();

        let mut fields = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let field_name = self.expect_ident()?;
            self.expect(Token::Colon)?;
            let field_type = self.parse_type_expr()?;
            fields.push((field_name, field_type));
            if matches!(self.peek(), Token::Comma) {
                self.advance();
            }
            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::RecordDef {
            name,
            fields,
            span: start.to(end),
        })
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
            span: start.to(end),
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
            span: start.to(end),
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
            span: start.to(end),
        })
    }

    // Parses: <name> <pat> ... [| <guard>] = <body>
    fn parse_fun_binding(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        let name = self.expect_ident()?;

        let mut params = Vec::new();
        while !matches!(self.peek(), Token::Eq | Token::Bar | Token::Eof) {
            params.push(self.parse_pattern()?);
        }

        let guard = if matches!(self.peek(), Token::Bar) {
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
            span: start.to(end),
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

    /// Postfix operators: field access via `.`
    /// `user.name.first` → FieldAccess(FieldAccess(user, "name"), "first")
    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        while matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'
            let field = self.expect_ident()?;
            let end = self.tokens[self.pos - 1].span;
            let start = expr.span().start;
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
                        expr = Expr::App { func: Box::new(expr), arg: Box::new(arg), span: span.to(end) };
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
                    let inner = self.parse_expr(0)?;
                    self.expect(Token::RParen)?;
                    Ok(inner)
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
                if !matches!(self.peek(), Token::Let | Token::RBrace) {
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
                        let name = self.expect_ident()?;
                        self.expect(Token::Eq)?;
                        let value = self.parse_expr(0)?;
                        let stmt_span = let_start.to(value.span());
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
                        name: s,
                        fields,
                        span: span.to(end),
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
            Token::LParen => {
                self.expect(Token::RParen)?;
                Ok(Pat::Lit {
                    value: Lit::Unit,
                    span,
                })
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

#[cfg(test)]
mod parser_tests;
