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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;

    fn parse(source: &str) -> Program {
        let tokens = Lexer::new(source).lex().unwrap();
        Parser::new(tokens).parse_program().unwrap()
    }

    fn parse_expr(source: &str) -> Expr {
        let tokens = Lexer::new(source).lex().unwrap();
        Parser::new(tokens).parse_expr(0).unwrap()
    }

    fn parse_pattern(source: &str) -> Pat {
        let tokens = Lexer::new(source).lex().unwrap();
        Parser::new(tokens).parse_pattern().unwrap()
    }

    // --- Literals ---

    #[test]
    fn literal_int() {
        let expr = parse_expr("42");
        assert!(matches!(
            expr,
            Expr::Lit {
                value: Lit::Int(42),
                ..
            }
        ));
    }

    #[test]
    fn literal_float() {
        let expr = parse_expr("1.5");
        assert!(matches!(expr, Expr::Lit { value: Lit::Float(f), .. } if f == 1.5));
    }

    #[test]
    fn literal_string() {
        let expr = parse_expr("\"hello\"");
        assert!(matches!(expr, Expr::Lit { value: Lit::String(s), .. } if s == "hello"));
    }

    #[test]
    fn literal_bool() {
        let t = parse_expr("True");
        let f = parse_expr("False");
        assert!(matches!(
            t,
            Expr::Lit {
                value: Lit::Bool(true),
                ..
            }
        ));
        assert!(matches!(
            f,
            Expr::Lit {
                value: Lit::Bool(false),
                ..
            }
        ));
    }

    // --- Variables and constructors ---

    #[test]
    fn variable() {
        let expr = parse_expr("foo");
        assert!(matches!(expr, Expr::Var { name, .. } if name == "foo"));
    }

    #[test]
    fn constructor() {
        let expr = parse_expr("Some");
        assert!(matches!(expr, Expr::Constructor { name, .. } if name == "Some"));
    }

    // --- Binary operators ---

    #[test]
    fn binary_add() {
        let expr = parse_expr("1 + 2");
        assert!(matches!(expr, Expr::BinOp { op: BinOp::Add, .. }));
    }

    #[test]
    fn binary_precedence_mul_over_add() {
        // 1 + 2 * 3 should parse as 1 + (2 * 3)
        let expr = parse_expr("1 + 2 * 3");
        match expr {
            Expr::BinOp {
                op: BinOp::Add,
                left,
                right,
                ..
            } => {
                assert!(matches!(
                    *left,
                    Expr::Lit {
                        value: Lit::Int(1),
                        ..
                    }
                ));
                assert!(matches!(*right, Expr::BinOp { op: BinOp::Mul, .. }));
            }
            _ => panic!("expected Add at top level, got {:?}", expr),
        }
    }

    #[test]
    fn binary_precedence_comparison_over_logic() {
        // x == 1 && y == 2 should parse as (x == 1) && (y == 2)
        let expr = parse_expr("x == 1 && y == 2");
        match expr {
            Expr::BinOp {
                op: BinOp::And,
                left,
                right,
                ..
            } => {
                assert!(matches!(*left, Expr::BinOp { op: BinOp::Eq, .. }));
                assert!(matches!(*right, Expr::BinOp { op: BinOp::Eq, .. }));
            }
            _ => panic!("expected And at top level, got {:?}", expr),
        }
    }

    #[test]
    fn binary_left_associative() {
        // 1 - 2 - 3 should parse as (1 - 2) - 3
        let expr = parse_expr("1 - 2 - 3");
        match expr {
            Expr::BinOp {
                op: BinOp::Sub,
                left,
                right,
                ..
            } => {
                assert!(matches!(*left, Expr::BinOp { op: BinOp::Sub, .. }));
                assert!(matches!(
                    *right,
                    Expr::Lit {
                        value: Lit::Int(3),
                        ..
                    }
                ));
            }
            _ => panic!("expected Sub at top level, got {:?}", expr),
        }
    }

    // --- Parenthesized expressions ---

    #[test]
    fn parenthesized() {
        // (1 + 2) * 3 should have Mul at top
        let expr = parse_expr("(1 + 2) * 3");
        match expr {
            Expr::BinOp {
                op: BinOp::Mul,
                left,
                ..
            } => {
                assert!(matches!(*left, Expr::BinOp { op: BinOp::Add, .. }));
            }
            _ => panic!("expected Mul at top level, got {:?}", expr),
        }
    }

    // --- Unary minus ---

    #[test]
    fn unary_minus() {
        let expr = parse_expr("-x");
        assert!(matches!(expr, Expr::UnaryMinus { .. }));
    }

    #[test]
    fn unary_minus_precedence() {
        // -x + 1 should parse as (-x) + 1
        let expr = parse_expr("-x + 1");
        match expr {
            Expr::BinOp {
                op: BinOp::Add,
                left,
                ..
            } => {
                assert!(matches!(*left, Expr::UnaryMinus { .. }));
            }
            _ => panic!("expected Add at top level, got {:?}", expr),
        }
    }

    // --- Function application ---

    #[test]
    fn application_single_arg() {
        let expr = parse_expr("f x");
        match expr {
            Expr::App { func, arg, .. } => {
                assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
                assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
            }
            _ => panic!("expected App, got {:?}", expr),
        }
    }

    #[test]
    fn application_curried() {
        // f x y should parse as App(App(f, x), y)
        let expr = parse_expr("f x y");
        match expr {
            Expr::App { func, arg, .. } => {
                assert!(matches!(*arg, Expr::Var { name, .. } if name == "y"));
                assert!(matches!(*func, Expr::App { .. }));
            }
            _ => panic!("expected nested App, got {:?}", expr),
        }
    }

    #[test]
    fn application_binds_tighter_than_binop() {
        // f x + g y should parse as (f x) + (g y)
        let expr = parse_expr("f x + g y");
        match expr {
            Expr::BinOp {
                op: BinOp::Add,
                left,
                right,
                ..
            } => {
                assert!(matches!(*left, Expr::App { .. }));
                assert!(matches!(*right, Expr::App { .. }));
            }
            _ => panic!("expected Add at top level, got {:?}", expr),
        }
    }

    // --- Pipes ---

    #[test]
    fn forward_pipe() {
        // x |> f desugars to App(f, x)
        let expr = parse_expr("x |> f");
        match expr {
            Expr::App { func, arg, .. } => {
                assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
                assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
            }
            _ => panic!("expected App from pipe, got {:?}", expr),
        }
    }

    #[test]
    fn backward_pipe() {
        // f <| x desugars to App(f, x)
        let expr = parse_expr("f <| x");
        match expr {
            Expr::App { func, arg, .. } => {
                assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
                assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
            }
            _ => panic!("expected App from backward pipe, got {:?}", expr),
        }
    }

    // --- If/else ---

    #[test]
    fn if_else() {
        let expr = parse_expr("if True then 1 else 2");
        match expr {
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                assert!(matches!(
                    *cond,
                    Expr::Lit {
                        value: Lit::Bool(true),
                        ..
                    }
                ));
                assert!(matches!(
                    *then_branch,
                    Expr::Lit {
                        value: Lit::Int(1),
                        ..
                    }
                ));
                assert!(matches!(
                    *else_branch,
                    Expr::Lit {
                        value: Lit::Int(2),
                        ..
                    }
                ));
            }
            _ => panic!("expected If, got {:?}", expr),
        }
    }

    #[test]
    fn if_else_if() {
        let expr = parse_expr("if x then 1 else if y then 2 else 3");
        match expr {
            Expr::If { else_branch, .. } => {
                assert!(matches!(*else_branch, Expr::If { .. }));
            }
            _ => panic!("expected If, got {:?}", expr),
        }
    }

    // --- Blocks ---

    #[test]
    fn block_single_expr() {
        let expr = parse_expr("{ 42 }");
        match expr {
            Expr::Block { stmts, .. } => {
                assert_eq!(stmts.len(), 1);
                assert!(matches!(
                    stmts[0],
                    Stmt::Expr(Expr::Lit {
                        value: Lit::Int(42),
                        ..
                    })
                ));
            }
            _ => panic!("expected Block, got {:?}", expr),
        }
    }

    #[test]
    fn block_with_let() {
        let expr = parse_expr("{\n  let x = 1\n  x + 2\n}");
        match expr {
            Expr::Block { stmts, .. } => {
                assert_eq!(stmts.len(), 2);
                assert!(matches!(&stmts[0], Stmt::Let { name, .. } if name == "x"));
                assert!(matches!(
                    &stmts[1],
                    Stmt::Expr(Expr::BinOp { op: BinOp::Add, .. })
                ));
            }
            _ => panic!("expected Block, got {:?}", expr),
        }
    }

    // --- Patterns ---

    #[test]
    fn pattern_wildcard() {
        let pat = parse_pattern("_");
        assert!(matches!(pat, Pat::Wildcard { .. }));
    }

    #[test]
    fn pattern_wildcard_prefixed() {
        let pat = parse_pattern("_unused");
        assert!(matches!(pat, Pat::Wildcard { .. }));
    }

    #[test]
    fn pattern_var() {
        let pat = parse_pattern("x");
        assert!(matches!(pat, Pat::Var { name, .. } if name == "x"));
    }

    #[test]
    fn pattern_lit_int() {
        let pat = parse_pattern("42");
        assert!(matches!(
            pat,
            Pat::Lit {
                value: Lit::Int(42),
                ..
            }
        ));
    }

    #[test]
    fn pattern_lit_bool() {
        let pat = parse_pattern("True");
        assert!(matches!(
            pat,
            Pat::Lit {
                value: Lit::Bool(true),
                ..
            }
        ));
    }

    #[test]
    fn pattern_bare_constructor() {
        let pat = parse_pattern("None");
        match pat {
            Pat::Constructor { name, args, .. } => {
                assert_eq!(name, "None");
                assert!(args.is_empty());
            }
            _ => panic!("expected Constructor, got {:?}", pat),
        }
    }

    #[test]
    fn pattern_constructor_with_args() {
        let pat = parse_pattern("Some(x)");
        match pat {
            Pat::Constructor { name, args, .. } => {
                assert_eq!(name, "Some");
                assert_eq!(args.len(), 1);
                assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
            }
            _ => panic!("expected Constructor, got {:?}", pat),
        }
    }

    #[test]
    fn pattern_constructor_multiple_args() {
        let pat = parse_pattern("Cons(a, b)");
        match pat {
            Pat::Constructor { name, args, .. } => {
                assert_eq!(name, "Cons");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Constructor, got {:?}", pat),
        }
    }

    #[test]
    fn pattern_nested_constructor() {
        let pat = parse_pattern("Some(Cons(a, b))");
        match pat {
            Pat::Constructor { name, args, .. } => {
                assert_eq!(name, "Some");
                assert_eq!(args.len(), 1);
                assert!(matches!(&args[0], Pat::Constructor { name, .. } if name == "Cons"));
            }
            _ => panic!("expected Constructor, got {:?}", pat),
        }
    }

    #[test]
    fn pattern_record() {
        let pat = parse_pattern("User { name, age }");
        match pat {
            Pat::Record { name, fields, .. } => {
                assert_eq!(name, "User");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0], ("name".to_string(), None));
                assert_eq!(fields[1], ("age".to_string(), None));
            }
            _ => panic!("expected Record pattern, got {:?}", pat),
        }
    }

    #[test]
    fn pattern_record_with_alias() {
        let pat = parse_pattern("Error { code: c }");
        match pat {
            Pat::Record { name, fields, .. } => {
                assert_eq!(name, "Error");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, "code");
                assert!(matches!(&fields[0].1, Some(Pat::Var { name, .. }) if name == "c"));
            }
            _ => panic!("expected Record pattern, got {:?}", pat),
        }
    }

    // --- Declarations ---

    #[test]
    fn fun_annotation_simple() {
        let decls = parse("fun add (a: Int) (b: Int) -> Int");
        assert_eq!(decls.len(), 1);
        match &decls[0] {
            Decl::FunAnnotation {
                name,
                params,
                return_type,
                public,
                effects,
                ..
            } => {
                assert_eq!(name, "add");
                assert!(!public);
                assert_eq!(params.len(), 2);
                assert_eq!(params[0].0, "a");
                assert!(matches!(&params[0].1, TypeExpr::Named(n) if n == "Int"));
                assert!(matches!(return_type, TypeExpr::Named(n) if n == "Int"));
                assert!(effects.is_empty());
            }
            _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
        }
    }

    #[test]
    fn fun_annotation_public_with_effects() {
        let decls = parse("pub fun print (msg: String) -> Unit with { Console }");
        assert_eq!(decls.len(), 1);
        match &decls[0] {
            Decl::FunAnnotation {
                public, effects, ..
            } => {
                assert!(public);
                assert_eq!(effects, &vec!["Console".to_string()]);
            }
            _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
        }
    }

    #[test]
    fn fun_binding_simple() {
        let decls = parse("add x y = x + y");
        assert_eq!(decls.len(), 1);
        match &decls[0] {
            Decl::FunBinding {
                name,
                params,
                guard,
                body,
                ..
            } => {
                assert_eq!(name, "add");
                assert_eq!(params.len(), 2);
                assert!(guard.is_none());
                assert!(matches!(body, Expr::BinOp { op: BinOp::Add, .. }));
            }
            _ => panic!("expected FunBinding, got {:?}", decls[0]),
        }
    }

    #[test]
    fn fun_binding_with_guard() {
        let decls = parse("abs n if n < 0 = -n");
        assert_eq!(decls.len(), 1);
        match &decls[0] {
            Decl::FunBinding { name, guard, .. } => {
                assert_eq!(name, "abs");
                assert!(guard.is_some());
            }
            _ => panic!("expected FunBinding, got {:?}", decls[0]),
        }
    }

    // --- Type definitions ---

    #[test]
    fn type_def_simple() {
        let decls = parse("type Option a {\n  Some(a)\n  None\n}");
        assert_eq!(decls.len(), 1);
        match &decls[0] {
            Decl::TypeDef {
                name,
                type_params,
                variants,
                ..
            } => {
                assert_eq!(name, "Option");
                assert_eq!(type_params, &vec!["a".to_string()]);
                assert_eq!(variants.len(), 2);
                assert_eq!(variants[0].name, "Some");
                assert_eq!(variants[0].fields.len(), 1);
                assert_eq!(variants[1].name, "None");
                assert!(variants[1].fields.is_empty());
            }
            _ => panic!("expected TypeDef, got {:?}", decls[0]),
        }
    }

    // --- Case expressions ---

    #[test]
    fn case_simple() {
        let expr = parse_expr("case x {\n  Some(v) -> v\n  None -> 0\n}");
        match expr {
            Expr::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(arms[0].guard.is_none());
                assert!(
                    matches!(&arms[0].pattern, Pat::Constructor { name, .. } if name == "Some")
                );
                assert!(
                    matches!(&arms[1].pattern, Pat::Constructor { name, .. } if name == "None")
                );
            }
            _ => panic!("expected Case, got {:?}", expr),
        }
    }

    #[test]
    fn case_with_guard() {
        let expr = parse_expr("case x {\n  n if n > 0 -> n\n  _ -> 0\n}");
        match expr {
            Expr::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(arms[0].guard.is_some());
                assert!(arms[1].guard.is_none());
                assert!(matches!(&arms[1].pattern, Pat::Wildcard { .. }));
            }
            _ => panic!("expected Case, got {:?}", expr),
        }
    }

    // --- Type expressions ---

    #[test]
    fn type_expr_named() {
        let decls = parse("fun id (x: Int) -> Int");
        match &decls[0] {
            Decl::FunAnnotation {
                params,
                return_type,
                ..
            } => {
                assert!(matches!(&params[0].1, TypeExpr::Named(n) if n == "Int"));
                assert!(matches!(return_type, TypeExpr::Named(n) if n == "Int"));
            }
            _ => panic!("expected FunAnnotation"),
        }
    }

    #[test]
    fn type_expr_application() {
        let decls = parse("fun unwrap (x: Option a) -> a");
        match &decls[0] {
            Decl::FunAnnotation {
                params,
                return_type,
                ..
            } => {
                assert!(matches!(&params[0].1, TypeExpr::App(_, _)));
                assert!(matches!(return_type, TypeExpr::Var(v) if v == "a"));
            }
            _ => panic!("expected FunAnnotation"),
        }
    }

    #[test]
    fn type_expr_arrow() {
        let decls = parse("fun apply (f: a -> b) (x: a) -> b");
        match &decls[0] {
            Decl::FunAnnotation { params, .. } => {
                assert!(matches!(&params[0].1, TypeExpr::Arrow(_, _)));
            }
            _ => panic!("expected FunAnnotation"),
        }
    }

    // --- Combined programs ---

    #[test]
    fn annotation_and_binding() {
        let decls = parse("fun add (a: Int) (b: Int) -> Int\nadd x y = x + y");
        assert_eq!(decls.len(), 2);
        assert!(matches!(&decls[0], Decl::FunAnnotation { .. }));
        assert!(matches!(&decls[1], Decl::FunBinding { .. }));
    }

    #[test]
    fn multiple_bindings_pattern_match() {
        let decls = parse("abs n if n < 0 = -n\nabs n = n");
        assert_eq!(decls.len(), 2);
        match &decls[0] {
            Decl::FunBinding { guard, .. } => assert!(guard.is_some()),
            _ => panic!("expected FunBinding"),
        }
        match &decls[1] {
            Decl::FunBinding { guard, .. } => assert!(guard.is_none()),
            _ => panic!("expected FunBinding"),
        }
    }
}
