use super::{ParseError, Parser};
use crate::ast::*;
use crate::token::{Span, Token};

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
                Token::Pipe => (None, 1),           // desugars to App(right, left)
                Token::PipeBack => (None, 1),       // desugars to App(left, right)
                Token::ComposeForward => (None, 1), // f >> g  →  fun x -> g (f x)
                Token::ComposeBack => (None, 1),    // f << g  →  fun x -> f (g x)
                Token::DoubleColon => (None, 1),    // desugars to Cons(left, right), right-assoc
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
                Token::Slash => (Some(BinOp::FloatDiv), 7),
                Token::Modulo => (Some(BinOp::Mod), 7),
                _ => break,
            };

            if bp < min_bp {
                break;
            }

            // Remember operator kind before consuming
            let desugar = match self.peek() {
                Token::PipeBack => Desugar::PipeBack,
                Token::DoubleColon => Desugar::Cons,
                Token::ComposeForward => Desugar::ComposeForward,
                Token::ComposeBack => Desugar::ComposeBack,
                _ => Desugar::None,
            };
            self.advance(); // consume operator
            // :: is right-associative (recurse at same bp); everything else is left-associative
            let is_cons = matches!(desugar, Desugar::Cons);
            let right = self.parse_expr(if is_cons { bp } else { bp + 1 })?;

            let span = left.span.to(right.span);
            left = match op {
                // x :: xs  →  Cons x xs  (right-associative)
                None if is_cons => {
                    let cons = Expr { id: self.next_id(), span, kind: ExprKind::Constructor {
                        name: "Cons".to_string(),
                    }};
                    let app1 = Expr { id: self.next_id(), span, kind: ExprKind::App {
                        func: Box::new(cons),
                        arg: Box::new(left),
                    }};
                    Expr { id: self.next_id(), span, kind: ExprKind::App {
                        func: Box::new(app1),
                        arg: Box::new(right),
                    }}
                }
                // f >> g  →  fun x -> g (f x)
                None if matches!(desugar, Desugar::ComposeForward) => {
                    self.desugar_compose(left, right, span)
                }
                // f << g  →  fun x -> f (g x)
                None if matches!(desugar, Desugar::ComposeBack) => {
                    self.desugar_compose(right, left, span)
                }
                // |> forward pipe: `x |> f` becomes `App(f, x)`
                // <| backward pipe: `f <| x` becomes `App(f, x)`
                None if matches!(desugar, Desugar::PipeBack) => Expr { id: self.next_id(), span, kind: ExprKind::App {
                    func: Box::new(left),
                    arg: Box::new(right),
                }},
                None => Expr { id: self.next_id(), span, kind: ExprKind::App {
                    func: Box::new(right),
                    arg: Box::new(left),
                }},
                Some(op) => Expr { id: self.next_id(), span, kind: ExprKind::BinOp {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                }},
            };
        }

        // `with` has lowest precedence — checked after all binary ops
        if matches!(self.peek(), Token::With) {
            self.advance();
            let handler = self.parse_handler_ref()?;
            let end = self.tokens[self.pos - 1].span;
            let span = left.span.to(end);
            left = Expr { id: self.next_id(), span, kind: ExprKind::With {
                expr: Box::new(left),
                handler: Box::new(handler),
            }};
        }

        // Type ascription: `expr : Type` — lowest precedence, only at top level
        if min_bp == 0 && matches!(self.peek(), Token::Colon) {
            self.advance(); // consume ':'
            let type_expr = self.parse_type_expr()?;
            let end = self.tokens[self.pos - 1].span;
            let span = left.span.to(end);
            left = Expr { id: self.next_id(), span, kind: ExprKind::Ascription {
                expr: Box::new(left),
                type_expr,
            }};
        }

        Ok(left)
    }

    /// Function application: `f x y` → App(App(f, x), y)
    /// Greedily consumes arguments while the next token can start a primary.
    fn parse_application(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_postfix()?;

        while self.can_start_primary() {
            let arg = self.parse_postfix()?;
            let span = expr.span.to(arg.span);
            expr = Expr { id: self.next_id(), span, kind: ExprKind::App {
                func: Box::new(expr),
                arg: Box::new(arg),
            }};
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
                && let ExprKind::Constructor {
                    name: qualifier, ..
                } = &expr.kind
            {
                let qualifier = qualifier.clone();
                let start_span = expr.span;
                let effect_span = self.tokens[self.pos].span;
                self.advance(); // consume effect call token
                let span = start_span.to(effect_span);
                expr = Expr { id: self.next_id(), span, kind: ExprKind::EffectCall {
                    name,
                    qualifier: Some(qualifier),
                    args: Vec::new(),
                }};
                continue;
            }

            let start = expr.span.start;
            // Module access: `Math.abs` or `Shapes.Circle` -> QualifiedName (bare Constructor LHS only)
            if let ExprKind::Constructor { name: module, .. } = &expr.kind {
                let module = module.clone();
                let name = match self.peek().clone() {
                    Token::Ident(n) => {
                        self.advance();
                        n
                    }
                    Token::UpperIdent(n) => {
                        self.advance();
                        n
                    }
                    tok => {
                        return Err(ParseError {
                            message: format!("expected identifier after '.', got {:?}", tok),
                            span: self.tokens[self.pos].span,
                        });
                    }
                };
                let end = self.tokens[self.pos - 1].span;
                let qspan = Span {
                    start,
                    end: end.end,
                };

                // Qualified record create: `A.Animal { field: val }`
                // Uses unqualified type name, consistent with how `A.Circle(5)` → Constructor("Circle").
                if name.chars().next().is_some_and(|c| c.is_uppercase())
                    && matches!(self.peek(), Token::LBrace)
                {
                    self.advance(); // consume '{'
                    self.skip_terminators();
                    let mut fields = Vec::new();
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        let field_name = self.expect_ident()?;
                        let field_span = self.tokens[self.pos - 1].span;
                        self.expect(Token::Colon)?;
                        let value = self.parse_expr(0)?;
                        fields.push((field_name, field_span, value));
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                        self.skip_terminators();
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    let span = qspan.to(end);
                    expr = Expr { id: self.next_id(), span, kind: ExprKind::RecordCreate {
                        name,
                        fields,
                    }};
                    continue;
                }

                expr = Expr { id: self.next_id(), span: qspan, kind: ExprKind::QualifiedName {
                    module,
                    name,
                }};
                continue;
            }
            let field = self.expect_ident()?;
            let end = self.tokens[self.pos - 1].span;
            let span = Span {
                start,
                end: end.end,
            };
            expr = Expr { id: self.next_id(), span, kind: ExprKind::FieldAccess {
                expr: Box::new(expr),
                field,
            }};
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
                    // return clause: `return value = body`
                    self.advance();
                    let param_span = self.tokens[self.pos].span;
                    let param = self.expect_ident()?;
                    self.expect(Token::Eq)?;
                    let body = self.parse_expr(0)?;
                    let arm_end = body.span;
                    return_clause = Some(Box::new(HandlerArm {
                        op_name: "return".to_string(),
                        params: vec![(param, param_span)],
                        body: Box::new(body),
                        span: arm_start.to(arm_end),
                    }));
                } else {
                    // Could be a named handler ref or an inline arm.
                    // Named ref: just an ident followed by `,` or `}` or newline
                    // Inline arm: ident [params...] = body
                    let name = self.expect_ident()?;

                    if matches!(
                        self.peek(),
                        Token::Comma | Token::RBrace | Token::Terminator
                    ) {
                        named.push(name);
                    } else {
                        // Inline arm: op params = body
                        let mut params = Vec::new();
                        while !matches!(self.peek(), Token::Eq | Token::Eof) {
                            // Skip `()` unit params (zero-param effect ops)
                            if matches!(self.peek(), Token::LParen)
                                && matches!(self.peek_at(1), Token::RParen)
                            {
                                self.advance(); // consume '('
                                self.advance(); // consume ')'
                                continue;
                            }
                            let pspan = self.tokens[self.pos].span;
                            params.push((self.expect_ident()?, pspan));
                        }
                        self.expect(Token::Eq)?;
                        let body = self.parse_expr(0)?;
                        let arm_end = body.span;
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
            let handler_span = self.tokens[self.pos].span;
            let name = self.expect_ident()?;
            Ok(Handler::Named(name, handler_span))
        }
    }

    pub(super) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        let span = self.tokens[self.pos].span;

        match self.advance() {
            Token::True => Ok(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                value: Lit::Bool(true),
            }}),
            Token::False => Ok(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                value: Lit::Bool(false),
            }}),
            Token::Int(n) => Ok(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                value: Lit::Int(n),
            }}),
            Token::Float(f) => Ok(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                value: Lit::Float(f),
            }}),
            Token::String(s) => Ok(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                value: Lit::String(s),
            }}),
            Token::InterpolatedString(parts) => {
                use crate::token::InterpPart;
                // Desugar to a chain of `<>` concatenations.
                // Each hole becomes `show(expr)`, each literal stays as a string.
                // Adds a trailing Eof so sub-parsers can terminate cleanly.
                let mut segments: Vec<Expr> = Vec::new();
                for part in parts {
                    match part {
                        InterpPart::Literal(s) => {
                            if !s.is_empty() {
                                segments.push(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                                    value: Lit::String(s),
                                }});
                            }
                        }
                        InterpPart::Hole(mut tokens) => {
                            // Use the last token's end position + 1 for the desugared
                            // `show` call so it doesn't collide with a user-written `show`
                            // inside the hole (which would share the first token's span).
                            let show_span = tokens
                                .last()
                                .map(|t| Span {
                                    start: t.span.end + 1,
                                    end: t.span.end + 2,
                                })
                                .unwrap_or(span);
                            // Span covering the entire hole for the wrapping App node,
                            // so LSP traversal can reach expressions inside interpolation.
                            let app_span = match (tokens.first(), tokens.last()) {
                                (Some(first), Some(last)) => Span {
                                    start: first.span.start,
                                    end: last.span.end,
                                },
                                _ => span,
                            };
                            tokens.push(crate::token::Spanned {
                                token: crate::token::Token::Eof,
                                span,
                            });

                            let mut sub = crate::parser::Parser::new(tokens);
                            let hole_expr = sub.parse_expr(0)?;
                            segments.push(Expr { id: self.next_id(), span: app_span, kind: ExprKind::App {
                                func: Box::new(Expr { id: self.next_id(), span: show_span, kind: ExprKind::Var {
                                    name: "show".to_string(),
                                }}),
                                arg: Box::new(hole_expr),
                            }});
                        }
                    }
                }
                // Fold into a left-associative `<>` chain; empty string if no parts.
                let init = segments.into_iter().reduce(|left, right| Expr { id: self.next_id(), span, kind: ExprKind::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(left),
                    right: Box::new(right),
                }});
                Ok(init.unwrap_or(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                    value: Lit::String(String::new()),
                }}))
            }
            Token::Ident(ref i)
                if self.test_mode
                    && (i == "test" || i == "describe" || i == "skip")
                    && matches!(self.peek(), Token::String(_)) =>
            {
                // Desugar: test "name" { body } -> test "name" (fun () -> { body })
                //          describe "name" { body } -> describe "name" (fun () -> { body })
                let func_name = i.clone();
                let name_str = self.expect_string()?;
                let name_span = self.tokens[self.pos - 1].span;
                let body = self.parse_expr(0)?;
                let body_span = body.span;

                let lambda = Expr {
                    id: self.next_id(),
                    span: body_span,
                    kind: ExprKind::Lambda {
                        params: vec![Pat::Lit {
                            id: NodeId::fresh(),
                            value: Lit::Unit,
                            span: body_span,
                        }],
                        body: Box::new(body),
                    },
                };

                let func = Expr {
                    id: self.next_id(),
                    span,
                    kind: ExprKind::Var { name: func_name },
                };
                let name_lit = Expr {
                    id: self.next_id(),
                    span: name_span,
                    kind: ExprKind::Lit {
                        value: Lit::String(name_str),
                    },
                };
                let app1 = Expr {
                    id: self.next_id(),
                    span: span.to(name_span),
                    kind: ExprKind::App {
                        func: Box::new(func),
                        arg: Box::new(name_lit),
                    },
                };
                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(body_span),
                    kind: ExprKind::App {
                        func: Box::new(app1),
                        arg: Box::new(lambda),
                    },
                })
            }
            Token::Ident(i) => Ok(Expr { id: self.next_id(), span, kind: ExprKind::Var { name: i } }),
            Token::UpperIdent(i) => {
                if matches!(self.peek(), Token::LBrace) {
                    // Record create: User { name: "Dylan", age: 30 }
                    self.advance(); // consume '{'
                    self.skip_terminators();
                    let mut fields = Vec::new();
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        let field_name = self.expect_ident()?;
                        let field_span = self.tokens[self.pos - 1].span;
                        self.expect(Token::Colon)?;
                        let value = self.parse_expr(0)?;
                        fields.push((field_name, field_span, value));
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                        self.skip_terminators();
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::RecordCreate {
                        name: i,
                        fields,
                    }})
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
                    let mut expr = Expr { id: self.next_id(), span, kind: ExprKind::Constructor { name: i } };
                    for arg in args {
                        expr = Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::App {
                            func: Box::new(expr),
                            arg: Box::new(arg),
                        }};
                    }
                    Ok(expr)
                } else {
                    Ok(Expr { id: self.next_id(), span, kind: ExprKind::Constructor { name: i } })
                }
            }

            Token::LParen => {
                if matches!(self.peek(), Token::RParen) {
                    self.advance(); // consume ')'
                    Ok(Expr { id: self.next_id(), span, kind: ExprKind::Lit {
                        value: Lit::Unit,
                    }})
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
                        Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::Tuple {
                            elements,
                        }})
                    } else {
                        self.expect(Token::RParen)?;
                        Ok(first)
                    }
                }
            }

            // List literal: [e1, e2, e3]
            // Desugars to: Cons(e1, Cons(e2, Cons(e3, Nil)))
            //
            // List comprehension: [expr | qualifiers]
            // Desugars using Haskell rules:
            //   [e | p <- l, Q]  ==> flat_map (fun p -> [e | Q]) l
            //   [e | guard, Q]   ==> if guard then [e | Q] else []
            //   [e | let p = v, Q] ==> { let p = v; [e | Q] }
            //   [e | ]           ==> [e]
            Token::LBracket => {
                // Empty list
                if matches!(self.peek(), Token::RBracket) {
                    let end = self.tokens[self.pos].span;
                    self.advance();
                    return Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::Constructor {
                        name: "Nil".to_string(),
                    }});
                }

                let first = self.parse_expr(0)?;

                if matches!(self.peek(), Token::Bar) {
                    // List comprehension: [expr | qualifiers]
                    self.advance(); // consume |
                    let qualifiers = self.parse_comprehension_qualifiers()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBracket)?;
                    return Ok(self.desugar_comprehension(first, &qualifiers, span.to(end)));
                }

                // Normal list literal
                let mut elements = vec![first];
                while matches!(self.peek(), Token::Comma) {
                    self.advance();
                    if matches!(self.peek(), Token::RBracket) {
                        break; // trailing comma
                    }
                    elements.push(self.parse_expr(0)?);
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBracket)?;

                // Build from right to left: Nil, then wrap each element
                let mut result = Expr { id: self.next_id(), span: end, kind: ExprKind::Constructor {
                    name: "Nil".to_string(),
                }};
                for elem in elements.into_iter().rev() {
                    let elem_span = elem.span;
                    let cons = Expr { id: self.next_id(), span: elem_span, kind: ExprKind::Constructor {
                        name: "Cons".to_string(),
                    }};
                    let app1 = Expr { id: self.next_id(), span: elem_span, kind: ExprKind::App {
                        func: Box::new(cons),
                        arg: Box::new(elem),
                    }};
                    result = Expr { id: self.next_id(), span: elem_span.to(end), kind: ExprKind::App {
                        func: Box::new(app1),
                        arg: Box::new(result),
                    }};
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
                let end_span = body.span;

                Ok(Expr { id: self.next_id(), span: span.to(end_span), kind: ExprKind::Lambda {
                    params,
                    body: Box::new(body),
                }})
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
                            let field_span = self.tokens[self.pos - 1].span;
                            self.expect(Token::Colon)?;
                            let value = self.parse_expr(0)?;
                            fields.push((field_name, field_span, value));
                            if matches!(self.peek(), Token::Comma) {
                                self.advance();
                            }
                            self.skip_terminators();
                        }
                        let end = self.tokens[self.pos].span;
                        self.expect(Token::RBrace)?;
                        return Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::RecordUpdate {
                            record: Box::new(record),
                            fields,
                        }});
                    }

                    // Not a record update — backtrack and parse as block
                    self.pos = save;
                }

                // Check for anonymous record create: { field: expr, ... }
                // Recognized when current token is a lowercase ident followed by ':'
                if matches!(self.peek(), Token::Ident(_))
                    && self.pos + 1 < self.tokens.len()
                    && matches!(self.tokens[self.pos + 1].token, Token::Colon)
                {
                    let mut fields = Vec::new();
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        let field_name = self.expect_ident()?;
                        let field_span = self.tokens[self.pos - 1].span;
                        self.expect(Token::Colon)?;
                        let value = self.parse_expr(0)?;
                        fields.push((field_name, field_span, value));
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                        self.skip_terminators();
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    return Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::AnonRecordCreate { fields },
                    });
                }

                let mut stmts: Vec<Stmt> = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    if matches!(self.peek(), Token::Let) {
                        let let_start = self.tokens[self.pos].span;
                        self.advance(); // consume 'let'
                        let is_assert = matches!(self.peek(), Token::Ident(s) if s == "assert");
                        if is_assert {
                            self.advance(); // consume 'assert'
                        }
                        let pattern = self.parse_pattern()?;

                        // Check for local function definition: `let f x y = body`
                        // If the first pattern is a variable and next token is NOT
                        // `=` or `:`, we have parameter patterns following the name.
                        if let Pat::Var { name, span: fn_name_span, .. } = &pattern
                            && !matches!(self.peek(), Token::Eq | Token::Colon)
                        {
                            let fun_name = name.clone();
                            let fn_name_span = *fn_name_span;
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
                            let stmt_span = let_start.to(body.span);
                            stmts.push(Stmt::LetFun {
                                id: NodeId::fresh(),
                                name: fun_name,
                                name_span: fn_name_span,
                                params,
                                guard,
                                body,
                                span: stmt_span,
                            });
                        } else {
                            let annotation = if matches!(self.peek(), Token::Colon)
                                && matches!(pattern, Pat::Var { .. })
                            {
                                self.advance(); // consume ':'
                                Some(self.parse_type_expr()?)
                            } else {
                                None
                            };
                            self.expect(Token::Eq)?;
                            let value = self.parse_expr(0)?;
                            let stmt_span = let_start.to(value.span);
                            stmts.push(Stmt::Let {
                                pattern,
                                annotation,
                                value,
                                assert: is_assert,
                                span: stmt_span,
                            });
                        }
                    } else {
                        stmts.push(Stmt::Expr(self.parse_expr(0)?));
                    }
                    self.skip_terminators();
                }
                let end_span = self.tokens[self.pos].span; // the RBrace
                self.expect(Token::RBrace)?;
                Ok(Expr { id: self.next_id(), span: span.to(end_span), kind: ExprKind::Block {
                    stmts,
                }})
            }

            Token::If => {
                let cond = self.parse_expr(0)?;
                self.skip_terminators();
                self.expect(Token::Then)?;

                let then_branch = self.parse_expr(0)?;
                self.skip_terminators();
                self.expect(Token::Else)?;

                let else_branch = self.parse_expr(0)?;
                let end_span = else_branch.span;

                Ok(Expr { id: self.next_id(), span: span.to(end_span), kind: ExprKind::If {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                }})
            }

            Token::Case => {
                self.no_brace_app = true;
                let scrutinee = self.parse_expr(0)?;
                self.no_brace_app = false;
                self.expect(Token::LBrace)?;
                self.skip_terminators();

                let mut branches = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;

                    let guard = if matches!(self.peek(), Token::Bar) {
                        self.advance();
                        Some(self.parse_expr(0)?)
                    } else {
                        None
                    };

                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span.end;
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

                Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::Case {
                    scrutinee: Box::new(scrutinee),
                    arms: branches,
                }})
            }

            Token::Receive => {
                self.expect(Token::LBrace)?;
                self.skip_terminators();

                let mut branches = Vec::new();
                let mut after_clause = None;

                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    // Check for `after` clause
                    if matches!(self.peek(), Token::After) {
                        self.advance(); // consume 'after'
                        let timeout = self.parse_expr(0)?;
                        self.expect(Token::Arrow)?;
                        let body = self.parse_expr(0)?;
                        after_clause = Some((Box::new(timeout), Box::new(body)));
                        self.skip_terminators();
                        break; // after must be last
                    }

                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;

                    let guard = if matches!(self.peek(), Token::Bar) {
                        self.advance();
                        Some(self.parse_expr(0)?)
                    } else {
                        None
                    };

                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span.end;
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

                let end = self.tokens[self.pos].span;
                self.expect(Token::RBrace)?;

                Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::Receive {
                    arms: branches,
                    after_clause,
                }})
            }

            // Unary negation
            Token::Minus => {
                let expr = self.parse_primary()?;
                let end_span = expr.span.end;
                let neg_span = Span {
                    start: span.start,
                    end: end_span,
                };
                Ok(Expr { id: self.next_id(), span: neg_span, kind: ExprKind::UnaryMinus {
                    expr: Box::new(expr),
                }})
            }

            // Effect call: `log! "hello"` args handled by parse_application
            Token::EffectCall(name) => Ok(Expr { id: self.next_id(), span, kind: ExprKind::EffectCall {
                name,
                qualifier: None,
                args: Vec::new(),
            }}),

            // Resume: `resume value`
            Token::Resume => {
                let value = self.parse_expr(0)?;
                let end = value.span;
                Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::Resume {
                    value: Box::new(value),
                }})
            }

            // do...else block: `do { Pat <- expr ... SuccessExpr } else { Pat -> expr ... }`
            Token::Do => {
                self.expect(Token::LBrace)?;
                self.skip_terminators();

                let mut bindings = Vec::new();
                // Parse bindings (`Pat <- expr`) until we find the success expression
                // (a line without `<-`). Distinguish by trying to parse a pattern and
                // checking whether `<-` follows; backtrack if not.
                let success = loop {
                    if matches!(self.peek(), Token::RBrace | Token::Eof) {
                        return Err(ParseError {
                            message: "do block missing success expression before '}'".to_string(),
                            span: self.tokens[self.pos].span,
                        });
                    }
                    let saved_pos = self.pos;
                    match self.parse_pattern() {
                        Ok(pat) if matches!(self.peek(), Token::LeftArrow) => {
                            self.advance(); // consume `<-`
                            let expr = self.parse_expr(0)?;
                            bindings.push((pat, expr));
                            self.skip_terminators();
                        }
                        _ => {
                            // Not a binding -- restore and parse as success expression
                            self.pos = saved_pos;
                            let success = self.parse_expr(0)?;
                            self.skip_terminators();
                            break success;
                        }
                    }
                };
                self.expect(Token::RBrace)?;

                self.skip_terminators();
                self.expect(Token::Else)?;
                self.expect(Token::LBrace)?;
                self.skip_terminators();

                let mut else_arms = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;
                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span.end;
                    else_arms.push(CaseArm {
                        pattern,
                        guard: None,
                        body,
                        span: Span {
                            start: arm_start.start,
                            end: end_span,
                        },
                    });
                    self.skip_terminators();
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBrace)?;

                Ok(Expr { id: self.next_id(), span: span.to(end), kind: ExprKind::Do {
                    bindings,
                    success: Box::new(success),
                    else_arms,
                }})
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

    // --- List comprehension helpers ---

    /// Parse comma-separated comprehension qualifiers until `]`.
    /// Each qualifier is a generator (`pat <- expr`), guard (`expr`),
    /// or let binding (`let pat = expr`).
    fn parse_comprehension_qualifiers(
        &mut self,
    ) -> Result<Vec<ComprehensionQualifier>, ParseError> {
        let mut qualifiers = Vec::new();
        loop {
            if matches!(self.peek(), Token::RBracket | Token::Eof) {
                break;
            }

            // Let binding: let pat = expr
            if matches!(self.peek(), Token::Let) {
                self.advance(); // consume let
                let pat = self.parse_pattern()?;
                self.expect(Token::Eq)?;
                let value = self.parse_expr(0)?;
                qualifiers.push(ComprehensionQualifier::Let(pat, value));
            } else {
                // Try generator (pat <- expr), fall back to guard (expr)
                let saved_pos = self.pos;
                match self.parse_pattern() {
                    Ok(pat) if matches!(self.peek(), Token::LeftArrow) => {
                        self.advance(); // consume <-
                        let source = self.parse_expr(0)?;
                        qualifiers.push(ComprehensionQualifier::Generator(pat, source));
                    }
                    _ => {
                        self.pos = saved_pos;
                        let guard = self.parse_expr(0)?;
                        qualifiers.push(ComprehensionQualifier::Guard(guard));
                    }
                }
            }

            if matches!(self.peek(), Token::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(qualifiers)
    }

    /// Recursively desugar list comprehension qualifiers into nested
    /// flat_map / if-then-else / let expressions.
    fn desugar_comprehension(
        &mut self,
        body: Expr,
        qualifiers: &[ComprehensionQualifier],
        span: Span,
    ) -> Expr {
        if qualifiers.is_empty() {
            // Base case: [e] ==> Cons(e, Nil)
            return self.make_singleton_list(body, span);
        }

        match &qualifiers[0] {
            ComprehensionQualifier::Generator(pat, source) => {
                // [e | p <- l, Q] ==> flat_map (fun p -> [e | Q]) l
                let inner = self.desugar_comprehension(body, &qualifiers[1..], span);
                let lambda = Expr { id: self.next_id(), span, kind: ExprKind::Lambda {
                    params: vec![pat.clone()],
                    body: Box::new(inner),
                }};
                let flat_map = Expr { id: self.next_id(), span, kind: ExprKind::QualifiedName {
                    module: "List".to_string(),
                    name: "flat_map".to_string(),
                }};
                let app1 = Expr { id: self.next_id(), span, kind: ExprKind::App {
                    func: Box::new(flat_map),
                    arg: Box::new(lambda),
                }};
                Expr { id: self.next_id(), span, kind: ExprKind::App {
                    func: Box::new(app1),
                    arg: Box::new(source.clone()),
                }}
            }
            ComprehensionQualifier::Guard(guard) => {
                // [e | g, Q] ==> if g then [e | Q] else []
                let then_branch = self.desugar_comprehension(body, &qualifiers[1..], span);
                let else_branch = Expr { id: self.next_id(), span, kind: ExprKind::Constructor {
                    name: "Nil".to_string(),
                }};
                Expr { id: self.next_id(), span, kind: ExprKind::If {
                    cond: Box::new(guard.clone()),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                }}
            }
            ComprehensionQualifier::Let(pat, value) => {
                // [e | let p = v, Q] ==> { let p = v; [e | Q] }
                let inner = self.desugar_comprehension(body, &qualifiers[1..], span);
                Expr { id: self.next_id(), span, kind: ExprKind::Block {
                    stmts: vec![
                        Stmt::Let {
                            pattern: pat.clone(),
                            annotation: None,
                            value: value.clone(),
                            assert: false,
                            span,
                        },
                        Stmt::Expr(inner),
                    ],
                }}
            }
        }
    }

    /// Desugar `first >> second` into `fun _x -> second (first _x)`.
    /// Both forward and backward compose call this with args in the right order.
    fn desugar_compose(&mut self, first: Expr, second: Expr, span: Span) -> Expr {
        let param = Pat::Var {
            id: NodeId::fresh(),
            name: "_x".to_string(),
            span,
        };
        let arg = Expr { id: self.next_id(), span, kind: ExprKind::Var {
            name: "_x".to_string(),
        }};
        let inner = Expr { id: self.next_id(), span, kind: ExprKind::App {
            func: Box::new(first),
            arg: Box::new(arg),
        }};
        let body = Expr { id: self.next_id(), span, kind: ExprKind::App {
            func: Box::new(second),
            arg: Box::new(inner),
        }};
        Expr { id: self.next_id(), span, kind: ExprKind::Lambda {
            params: vec![param],
            body: Box::new(body),
        }}
    }

    /// Build Cons(elem, Nil) -- a singleton list.
    fn make_singleton_list(&mut self, elem: Expr, span: Span) -> Expr {
        let nil = Expr { id: self.next_id(), span, kind: ExprKind::Constructor {
            name: "Nil".to_string(),
        }};
        let cons = Expr { id: self.next_id(), span, kind: ExprKind::Constructor {
            name: "Cons".to_string(),
        }};
        let app1 = Expr { id: self.next_id(), span, kind: ExprKind::App {
            func: Box::new(cons),
            arg: Box::new(elem),
        }};
        Expr { id: self.next_id(), span, kind: ExprKind::App {
            func: Box::new(app1),
            arg: Box::new(nil),
        }}
    }
}

/// Tracks which desugared operator is being parsed.
enum Desugar {
    None,
    PipeBack,
    Cons,
    ComposeForward,
    ComposeBack,
}

/// A qualifier in a list comprehension.
enum ComprehensionQualifier {
    /// `pat <- expr` -- draw elements from a list
    Generator(Pat, Expr),
    /// `expr` -- boolean guard/filter
    Guard(Expr),
    /// `let pat = expr` -- local binding
    Let(Pat, Expr),
}
