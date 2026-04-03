use super::{ParseError, Parser};
use crate::ast::*;
use crate::token::{Span, StringKind, Token};

impl Parser {
    /// Parse record fields: `field: expr, field2: expr2, ...`
    /// Handles recovery for incomplete fields (missing `:` or value) so that
    /// the rest of the file can still be parsed for LSP features.
    fn parse_record_fields(&mut self) -> Result<Vec<(String, Span, Expr)>, ParseError> {
        let mut fields = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            // Recovery: if next token isn't an ident, skip it and try again.
            if !matches!(self.peek(), Token::Ident(_)) {
                self.advance();
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                }
                continue;
            }
            let field_name = self.expect_ident()?;
            let field_span = self.tokens[self.pos - 1].span;
            if matches!(self.peek(), Token::Colon) {
                self.advance(); // consume ':'
                let value = self.parse_expr(0)?;
                fields.push((field_name, field_span, value));
            } else {
                // Recovery: incomplete field (e.g. `House { a }` while typing).
                // Treat as a punned field `name: name` so parsing can continue.
                let value = Expr {
                    id: self.next_id(),
                    span: field_span,
                    kind: ExprKind::Var {
                        name: field_name.clone(),
                    },
                };
                fields.push((field_name, field_span, value));
            }
            if matches!(self.peek(), Token::Comma) {
                self.advance();
            }
        }
        Ok(fields)
    }

    /// Return the binding power of the next token if it's a binary operator.
    fn peek_binop_bp(&self) -> Option<u8> {
        match self.peek() {
            Token::Or => Some(2),
            Token::And => Some(3),
            Token::EqEq | Token::NotEq => Some(4),
            Token::Lt | Token::Gt | Token::LtEq | Token::GtEq => Some(5),
            Token::Concat | Token::Plus | Token::Minus => Some(6),
            Token::Star | Token::Slash | Token::Modulo => Some(7),
            _ => None,
        }
    }

    /// Return the BinOp for the next token (must be a binop).
    fn peek_binop_op(&self) -> Option<BinOp> {
        match self.peek() {
            Token::Or => Some(BinOp::Or),
            Token::And => Some(BinOp::And),
            Token::EqEq => Some(BinOp::Eq),
            Token::NotEq => Some(BinOp::NotEq),
            Token::Lt => Some(BinOp::Lt),
            Token::Gt => Some(BinOp::Gt),
            Token::LtEq => Some(BinOp::LtEq),
            Token::GtEq => Some(BinOp::GtEq),
            Token::Concat => Some(BinOp::Concat),
            Token::Plus => Some(BinOp::Add),
            Token::Minus => Some(BinOp::Sub),
            Token::Star => Some(BinOp::Mul),
            Token::Slash => Some(BinOp::FloatDiv),
            Token::Modulo => Some(BinOp::Mod),
            _ => None,
        }
    }

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
            // Binary operators continue across lines - an operator token at the
            // start of a line is unambiguous (it can't begin a new statement).
            // For `-`, this means `foo\n-bar` is subtraction, not `foo` then `(-bar)`.
            // Use `(-bar)` for unary negation as a separate expression.
            let (op, bp) = match self.peek() {
                Token::Pipe => (None, 1),
                Token::PipeBack => (None, 1),
                Token::ComposeForward => (None, 1),
                Token::ComposeBack => (None, 1),
                Token::DoubleColon => (None, 1),
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

            // For |>, collect a flat pipe chain with full trivia per segment.
            if matches!(self.peek(), Token::Pipe) {
                // First segment is `left` (no pipe-specific trivia, it gets decl-level trivia)
                let mut segments = vec![Annotated::bare(left)];
                let mut multiline = false;
                while matches!(self.peek(), Token::Pipe) {
                    // Track if any |> is on a new line
                    if self.tokens[self.pos].preceded_by_newline {
                        multiline = true;
                    }
                    // Capture trailing comment from end of previous segment
                    let trailing = self.tokens[self.pos - 1].trailing_comment.take();
                    if let Some(comment) = trailing
                        && let Some(last) = segments.last_mut()
                    {
                        last.trailing_comment = Some(comment);
                    }
                    // Capture leading trivia on the |> token
                    let leading = self.take_leading_trivia(self.pos);
                    self.advance(); // consume |>
                    let seg = self.parse_expr(bp + 1)?;
                    segments.push(Annotated {
                        node: seg,
                        leading_trivia: leading,
                        trailing_comment: None,
                        trailing_trivia: vec![],
                    });
                }
                // Capture trailing comment on last segment's final token
                let trailing = self.tokens[self.pos - 1].trailing_comment.take();
                if let Some(comment) = trailing
                    && let Some(last) = segments.last_mut()
                {
                    last.trailing_comment = Some(comment);
                }
                // Steal own-line comments from next token that follow without a blank line
                let stolen = self.steal_trailing_trivia();
                if !stolen.is_empty()
                    && let Some(last) = segments.last_mut()
                {
                    last.trailing_trivia = stolen;
                }
                let start_span = segments.first().unwrap().node.span;
                let end_span = segments.last().unwrap().node.span;
                left = Expr {
                    id: self.next_id(),
                    span: start_span.to(end_span),
                    kind: ExprKind::Pipe {
                        segments,
                        multiline,
                    },
                };
                continue;
            }

            // For <|, >>, << collect flat chain like |>
            if matches!(
                self.peek(),
                Token::PipeBack | Token::ComposeForward | Token::ComposeBack
            ) {
                let chain_token = self.peek().clone();
                let mut segments = vec![Annotated::bare(left)];
                while self.peek() == &chain_token {
                    self.advance(); // consume operator
                    let seg = self.parse_expr(bp + 1)?;
                    segments.push(Annotated::bare(seg));
                }
                let start_span = segments.first().unwrap().node.span;
                let end_span = segments.last().unwrap().node.span;
                let span = start_span.to(end_span);
                let kind = match chain_token {
                    Token::PipeBack => ExprKind::PipeBack { segments },
                    Token::ComposeForward => ExprKind::ComposeForward { segments },
                    Token::ComposeBack => ExprKind::ComposeBack { segments },
                    _ => unreachable!(),
                };
                left = Expr {
                    id: self.next_id(),
                    span,
                    kind,
                };
                continue;
            }

            // :: is cons sugar (right-associative, not a binop chain)
            if matches!(self.peek(), Token::DoubleColon) {
                self.advance(); // consume ::
                let right = self.parse_expr(bp)?; // right-assoc: same bp
                let span = left.span.to(right.span);
                left = Expr {
                    id: self.next_id(),
                    span,
                    kind: ExprKind::Cons {
                        head: Box::new(left),
                        tail: Box::new(right),
                    },
                };
                continue;
            }

            // Binary operator - collect same-precedence chains into BinOpChain
            // with trivia on each segment, mirroring the Pipe pattern.
            let op = op.unwrap();
            let chain_bp = bp;

            // Capture trivia from the first operator token
            let first_multiline = self.tokens[self.pos].preceded_by_newline;
            let first_trailing = self.tokens[self.pos - 1].trailing_comment.take();
            let first_leading = self.take_leading_trivia(self.pos);
            self.advance(); // consume first operator
            let right = self.parse_expr(chain_bp + 1)?;

            // Check if the next token is a binop at the same precedence level.
            // If so, collect into a BinOpChain. Otherwise, emit plain BinOp.
            let next_same_bp = self.peek_binop_bp() == Some(chain_bp);
            if !next_same_bp {
                // Plain BinOp (2 operands, no chain) - no trivia to preserve
                // (same as before; trivia was on the operator token which is gone)
                if let Some(comment) = first_trailing {
                    // Re-attach trailing comment we stole - put on left expr's last token
                    // This is best-effort; single binops can't carry trivia.
                    let _ = comment;
                }
                let span = left.span.to(right.span);
                left = Expr {
                    id: self.next_id(),
                    span,
                    kind: ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                };
            } else {
                // Build a BinOpChain
                let mut segments = vec![Annotated::bare(left)];
                if let Some(comment) = first_trailing {
                    segments[0].trailing_comment = Some(comment);
                }
                let mut ops = vec![op];
                let mut multiline = first_multiline;

                segments.push(Annotated {
                    node: right,
                    leading_trivia: first_leading,
                    trailing_comment: None,
                    trailing_trivia: vec![],
                });

                // Continue collecting same-precedence operators
                while let Some(next_bp) = self.peek_binop_bp() {
                    if next_bp != chain_bp {
                        break;
                    }
                    if self.tokens[self.pos].preceded_by_newline {
                        multiline = true;
                    }
                    // Capture trailing comment from previous segment
                    if let Some(comment) = self.tokens[self.pos - 1].trailing_comment.take()
                        && let Some(last) = segments.last_mut()
                    {
                        last.trailing_comment = Some(comment);
                    }
                    let leading = self.take_leading_trivia(self.pos);
                    let next_op = self.peek_binop_op().unwrap();
                    self.advance(); // consume operator
                    let seg = self.parse_expr(chain_bp + 1)?;
                    ops.push(next_op);
                    segments.push(Annotated {
                        node: seg,
                        leading_trivia: leading,
                        trailing_comment: None,
                        trailing_trivia: vec![],
                    });
                }
                // Trailing comment on last segment
                if let Some(comment) = self.tokens[self.pos - 1].trailing_comment.take()
                    && let Some(last) = segments.last_mut()
                {
                    last.trailing_comment = Some(comment);
                }

                let start_span = segments.first().unwrap().node.span;
                let end_span = segments.last().unwrap().node.span;
                left = Expr {
                    id: self.next_id(),
                    span: start_span.to(end_span),
                    kind: ExprKind::BinOpChain {
                        segments,
                        ops,
                        multiline,
                    },
                };
            }
        }

        // `with` has lowest precedence - checked after all binary ops
        if matches!(self.peek(), Token::With) && !self.next_on_new_line() {
            self.advance();
            let handler = self.parse_handler_ref()?;
            let end = self.tokens[self.pos - 1].span;
            let span = left.span.to(end);
            left = Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::With {
                    expr: Box::new(left),
                    handler: Box::new(handler),
                },
            };
        }

        // Type ascription: `expr : Type` - lowest precedence, only at top level
        if min_bp == 0 && matches!(self.peek(), Token::Colon) && !self.next_on_new_line() {
            self.advance(); // consume ':'
            let type_expr = self.parse_type_expr()?;
            let end = self.tokens[self.pos - 1].span;
            let span = left.span.to(end);
            left = Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Ascription {
                    expr: Box::new(left),
                    type_expr,
                },
            };
        }

        Ok(left)
    }

    /// Function application: `f x y` → App(App(f, x), y)
    /// Greedily consumes arguments while the next token can start a primary.
    fn parse_application(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_postfix()?;

        while self.can_start_primary() && !self.next_on_new_line() {
            let arg = self.parse_postfix()?;
            let span = expr.span.to(arg.span);
            expr = Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::App {
                    func: Box::new(expr),
                    arg: Box::new(arg),
                },
            };
        }

        Ok(expr)
    }

    /// Postfix operators: field access `.` and qualified effect calls
    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        while matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'

            // Qualified effect call: `Cache.get! key` or `Std.Cache.get! key`
            if let Token::EffectCall(name) = self.peek().clone() {
                // Check for effect qualifier (uppercase: Cache.get!)
                let qualifier = match &expr.kind {
                    ExprKind::Constructor { name: q, .. } => Some(q.clone()),
                    ExprKind::QualifiedName { module, name: prev_name, .. }
                        if prev_name.starts_with(|c: char| c.is_uppercase()) =>
                    {
                        Some(format!("{}.{}", module, prev_name))
                    }
                    _ => None,
                };
                if qualifier.is_some() {
                    let start_span = expr.span;
                    let effect_span = self.tokens[self.pos].span;
                    self.advance(); // consume effect call token
                    let span = start_span.to(effect_span);
                    expr = Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::EffectCall {
                            name,
                            qualifier,
                            args: Vec::new(),
                        },
                    };
                    continue;
                }
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
                    _ => {
                        // Recovery: incomplete module access (e.g. `Math.`).
                        // Produce a QualifiedName with an empty name.
                        let end = self.tokens[self.pos - 1].span;
                        let qspan = Span {
                            start,
                            end: end.end,
                        };
                        expr = Expr {
                            id: self.next_id(),
                            span: qspan,
                            kind: ExprKind::QualifiedName {
                                module,
                                name: String::new(),
                                canonical_module: None,
                            },
                        };
                        continue;
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
                    let fields = self.parse_record_fields()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    let span = qspan.to(end);
                    expr = Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::RecordCreate { name, fields },
                    };
                    continue;
                }

                expr = Expr {
                    id: self.next_id(),
                    span: qspan,
                    kind: ExprKind::QualifiedName { module, name, canonical_module: None },
                };
                continue;
            }
            // Multi-level module access: `Std.String.replace` when LHS is already QualifiedName
            // and its name part is uppercase (a module segment, not a function).
            if let ExprKind::QualifiedName { module: prev_module, name: prev_name, .. } = &expr.kind
                && prev_name.starts_with(|c: char| c.is_uppercase())
            {
                let extended_module = format!("{}.{}", prev_module, prev_name);
                let name = match self.peek().clone() {
                    Token::Ident(n) => { self.advance(); n }
                    Token::UpperIdent(n) => { self.advance(); n }
                    _ => {
                        let end = self.tokens[self.pos - 1].span;
                        let qspan = Span { start, end: end.end };
                        expr = Expr {
                            id: self.next_id(),
                            span: qspan,
                            kind: ExprKind::QualifiedName {
                                module: extended_module,
                                name: String::new(),
                                canonical_module: None,
                            },
                        };
                        continue;
                    }
                };
                let end = self.tokens[self.pos - 1].span;
                let qspan = Span { start, end: end.end };

                // Qualified record create with multi-level module path
                if name.chars().next().is_some_and(|c| c.is_uppercase())
                    && matches!(self.peek(), Token::LBrace)
                {
                    self.advance(); // consume '{'
                    let fields = self.parse_record_fields()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    let span = qspan.to(end);
                    expr = Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::RecordCreate { name, fields },
                    };
                    continue;
                }

                expr = Expr {
                    id: self.next_id(),
                    span: qspan,
                    kind: ExprKind::QualifiedName { module: extended_module, name, canonical_module: None },
                };
                continue;
            }
            // Recovery: if no identifier follows the dot (e.g. `record.`),
            // produce a FieldAccess with an empty field name so the rest of
            // the file can still be parsed and typechecked.
            let (field, end) = if matches!(self.peek(), Token::Ident(_)) {
                let f = self.expect_ident()?;
                (f, self.tokens[self.pos - 1].span)
            } else {
                // Incomplete field access -- use the dot's span as the end.
                (String::new(), self.tokens[self.pos - 1].span)
            };
            let span = Span {
                start,
                end: end.end,
            };
            expr = Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::FieldAccess {
                    expr: Box::new(expr),
                    field,
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

            let mut named = Vec::new();
            let mut arms = Vec::new();
            let mut return_clause = None;

            // Phase 1: Parse comma-separated named handler refs.
            // Named refs must come before inline arms. Supports both bare
            // (console_log) and qualified (Logger.console_log) forms.
            while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                // A named ref is an ident followed by `,` or `}`,
                // or an ident.ident followed by `,` or `}`
                let is_named_ref = matches!(self.peek(), Token::Ident(_))
                    && (matches!(self.peek_at(1), Token::Comma | Token::RBrace)
                        || (matches!(self.peek_at(1), Token::Dot)
                            && matches!(self.peek_at(2), Token::Ident(_))
                            && matches!(self.peek_at(3), Token::Comma | Token::RBrace)));
                if is_named_ref {
                    let start = self.pos;
                    let name_start = self.tokens[self.pos].span;
                    let name = self.expect_ident()?;
                    let name = if matches!(self.peek(), Token::Dot)
                        && matches!(self.peek_at(1), Token::Ident(_))
                    {
                        self.advance(); // consume '.'
                        let qualified = self.expect_ident()?;
                        format!("{}.{}", name, qualified)
                    } else {
                        name
                    };
                    let name_end = self.tokens[self.pos - 1].span;
                    let mut trailing_comment = None;
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                        trailing_comment = self.take_trailing_comment(self.pos - 1);
                    }
                    named.push(Annotated {
                        node: NamedHandlerRef {
                            name,
                            span: name_start.to(name_end),
                        },
                        leading_trivia: self.take_leading_trivia(start),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                } else {
                    break;
                }
            }

            // Phase 2: Parse inline handler arms (newline-separated, commas optional).
            while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                let start = self.pos;
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
                        qualifier: None,
                        params: vec![(param, param_span)],
                        body: Box::new(body),
                        finally_block: None,
                        span: arm_start.to(arm_end),
                    }));
                } else {
                    // Check for qualified name: `Effect.op` (UpperIdent.Ident)
                    let (qualifier, name) = if matches!(self.peek(), Token::UpperIdent(_))
                        && matches!(self.peek_at(1), Token::Dot)
                        && matches!(self.peek_at(2), Token::Ident(_))
                    {
                        let q = self.expect_upper_ident()?;
                        self.advance(); // consume '.'
                        let op = self.expect_ident()?;
                        (Some(q), op)
                    } else {
                        (None, self.expect_ident()?)
                    };

                    if matches!(self.peek(), Token::Comma | Token::RBrace) {
                        // Named ref after inline arms
                        return Err(ParseError {
                            message: "named handler refs must come before inline handler arms"
                                .to_string(),
                            span: arm_start,
                        });
                    }

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
                    let mut arm_end = body.span;

                    // Parse optional `finally { cleanup }` block
                    let finally_block = if matches!(self.peek(), Token::Finally) {
                        self.advance(); // consume 'finally'
                        let fb = self.parse_expr(0)?;
                        arm_end = fb.span;
                        Some(Box::new(fb))
                    } else {
                        None
                    };

                    let trailing_comment = self.take_trailing_comment(self.pos - 1);
                    arms.push(Annotated {
                        node: HandlerArm {
                            op_name: name,
                            qualifier,
                            params,
                            body: Box::new(body),
                            finally_block,
                            span: arm_start.to(arm_end),
                        },
                        leading_trivia: self.take_leading_trivia(start),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                }

                // Commas between inline arms are optional
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                    // Transfer trailing comment from comma to the last arm
                    if let Some(comment) = self.tokens[self.pos - 1].trailing_comment.take()
                        && let Some(last_arm) = arms.last_mut()
                        && last_arm.trailing_comment.is_none()
                    {
                        last_arm.trailing_comment = Some(comment);
                    }
                }
            }
            let dangling_trivia = self.take_leading_trivia(self.pos);
            self.expect(Token::RBrace)?;

            Ok(Handler::Inline {
                named,
                arms,
                return_clause,
                dangling_trivia,
            })
        } else {
            // Single named handler: `with console_log` or `with Logger.console_log`
            let handler_span = self.tokens[self.pos].span;
            let name = self.expect_ident()?;
            let name = if matches!(self.peek(), Token::Dot)
                && matches!(self.peek_at(1), Token::Ident(_))
            {
                self.advance(); // consume '.'
                let qualified = self.expect_ident()?;
                format!("{}.{}", name, qualified)
            } else {
                name
            };
            Ok(Handler::Named(name, handler_span))
        }
    }

    pub(super) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        let span = self.tokens[self.pos].span;

        match self.advance() {
            Token::True => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Lit {
                    value: Lit::Bool(true),
                },
            }),
            Token::False => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Lit {
                    value: Lit::Bool(false),
                },
            }),
            Token::Int(s, n) => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Lit {
                    value: Lit::Int(s, n),
                },
            }),
            Token::Float(s, f) => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Lit {
                    value: Lit::Float(s, f),
                },
            }),
            Token::String(s, kind) => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Lit {
                    value: Lit::String(s, kind),
                },
            }),
            Token::InterpolatedString(parts, kind) => {
                use crate::token::InterpPart;
                // Preserve as StringInterp; desugared later to show/concat chain.
                let mut string_parts: Vec<StringPart> = Vec::new();
                for part in parts {
                    match part {
                        InterpPart::Literal(s) => {
                            if !s.is_empty() {
                                string_parts.push(StringPart::Lit(s));
                            }
                        }
                        InterpPart::Hole(mut tokens) => {
                            tokens.push(crate::token::Spanned {
                                token: crate::token::Token::Eof,
                                span,
                                leading_trivia: Vec::new(),
                                trailing_comment: None,
                                preceded_by_newline: false,
                            });
                            let mut sub = crate::parser::Parser::new(tokens);
                            let hole_expr = sub.parse_expr(0)?;
                            string_parts.push(StringPart::Expr(hole_expr));
                        }
                    }
                }
                Ok(Expr {
                    id: self.next_id(),
                    span,
                    kind: ExprKind::StringInterp {
                        parts: string_parts,
                        kind,
                    },
                })
            }
            Token::Ident(ref i)
                if self.test_mode
                    && (i == "test" || i == "describe" || i == "skip" || i == "only")
                    && matches!(self.peek(), Token::String(..)) =>
            {
                // Parse test/describe sugar, preserving the block body as-is.
                // Lambda wrapping (fun () -> body) happens in desugar.rs so
                // the formatter can round-trip the original syntax.
                let func_name = i.clone();
                let name_str = self.expect_string()?;
                let name_span = self.tokens[self.pos - 1].span;
                let body = self.parse_expr(0)?;
                let body_span = body.span;

                let func = Expr {
                    id: self.next_id(),
                    span,
                    kind: ExprKind::Var { name: func_name },
                };
                let name_lit = Expr {
                    id: self.next_id(),
                    span: name_span,
                    kind: ExprKind::Lit {
                        value: Lit::String(name_str, StringKind::Normal),
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
                        arg: Box::new(body),
                    },
                })
            }
            Token::Ident(i) => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Var { name: i },
            }),
            Token::UpperIdent(i) => {
                if matches!(self.peek(), Token::LBrace) {
                    // Record create: User { name: "Dylan", age: 30 }
                    self.advance(); // consume '{'
                    let fields = self.parse_record_fields()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::RecordCreate { name: i, fields },
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
                    let mut expr = Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::Constructor { name: i },
                    };
                    for arg in args {
                        expr = Expr {
                            id: self.next_id(),
                            span: span.to(end),
                            kind: ExprKind::App {
                                func: Box::new(expr),
                                arg: Box::new(arg),
                            },
                        };
                    }
                    Ok(expr)
                } else {
                    Ok(Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::Constructor { name: i },
                    })
                }
            }

            Token::LParen => {
                if matches!(self.peek(), Token::RParen) {
                    self.advance(); // consume ')'
                    Ok(Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::Lit { value: Lit::Unit },
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
                        Ok(Expr {
                            id: self.next_id(),
                            span: span.to(end),
                            kind: ExprKind::Tuple { elements },
                        })
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
                    return Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::ListLit { elements: vec![] },
                    });
                }

                let first = self.parse_expr(0)?;

                if matches!(self.peek(), Token::Bar) {
                    // List comprehension: [expr | qualifiers]
                    self.advance(); // consume |
                    let qualifiers = self.parse_comprehension_qualifiers()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBracket)?;
                    return Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::ListComprehension {
                            body: Box::new(first),
                            qualifiers,
                        },
                    });
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
                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::ListLit { elements },
                })
            }

            Token::Fun => {
                let mut params = Vec::new();
                while !matches!(self.peek(), Token::Arrow | Token::Eof) {
                    params.push(self.parse_pattern()?);
                }
                self.expect(Token::Arrow)?;

                let body = self.parse_expr(0)?;
                let end_span = body.span;

                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end_span),
                    kind: ExprKind::Lambda {
                        params,
                        body: Box::new(body),
                    },
                })
            }

            Token::LBrace => {
                // Check for record update: { expr | field: val, ... }
                // We don't start with `let`, so try parsing an expression,
                // then check if the next token is `|`
                if !matches!(self.peek(), Token::Let | Token::RBrace) {
                    let save = self.save();
                    let first_expr = self.parse_expr(0);

                    if let Ok(record) = first_expr
                        && matches!(self.peek(), Token::Bar)
                    {
                        self.advance(); // consume '|'
                        let fields = self.parse_record_fields()?;
                        let end = self.tokens[self.pos].span;
                        self.expect(Token::RBrace)?;
                        return Ok(Expr {
                            id: self.next_id(),
                            span: span.to(end),
                            kind: ExprKind::RecordUpdate {
                                record: Box::new(record),
                                fields,
                            },
                        });
                    }

                    // Not a record update - backtrack and parse as block
                    self.restore(save);
                }

                // Check for anonymous record create: { field: expr, ... }
                // Recognized when current token is a lowercase ident followed by ':'
                if matches!(self.peek(), Token::Ident(_))
                    && self.pos + 1 < self.tokens.len()
                    && matches!(self.tokens[self.pos + 1].token, Token::Colon)
                {
                    let fields = self.parse_record_fields()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    return Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::AnonRecordCreate { fields },
                    });
                }

                let mut stmts: Vec<Annotated<Stmt>> = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let start = self.pos;
                    let stmt = if matches!(self.peek(), Token::Let) {
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
                        if let Pat::Var {
                            name,
                            span: fn_name_span,
                            ..
                        } = &pattern
                            && !matches!(self.peek(), Token::Eq | Token::Colon)
                        {
                            let fun_name = name.clone();
                            let fn_name_span = *fn_name_span;
                            let mut params = Vec::new();
                            while !matches!(self.peek(), Token::Eq | Token::When | Token::Eof) {
                                params.push(self.parse_pattern()?);
                            }
                            let guard = if matches!(self.peek(), Token::When) {
                                self.advance();
                                Some(Box::new(self.parse_expr(0)?))
                            } else {
                                None
                            };
                            self.expect(Token::Eq)?;
                            let body = self.parse_expr(0)?;
                            let stmt_span = let_start.to(body.span);
                            Stmt::LetFun {
                                id: NodeId::fresh(),
                                name: fun_name,
                                name_span: fn_name_span,
                                params,
                                guard,
                                body,
                                span: stmt_span,
                            }
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
                            Stmt::Let {
                                pattern,
                                annotation,
                                value,
                                assert: is_assert,
                                span: stmt_span,
                            }
                        }
                    } else {
                        Stmt::Expr(self.parse_expr(0)?)
                    };
                    let trailing_comment = self.take_trailing_comment(self.pos - 1);
                    stmts.push(Annotated {
                        node: stmt,
                        leading_trivia: self.take_leading_trivia(start),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                }
                let dangling_trivia = self.take_leading_trivia(self.pos);
                let end_span = self.tokens[self.pos].span; // the RBrace
                self.expect(Token::RBrace)?;
                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end_span),
                    kind: ExprKind::Block {
                        stmts,
                        dangling_trivia,
                    },
                })
            }

            Token::If => {
                let cond = self.parse_expr(0)?;
                self.expect(Token::Then)?;

                let then_branch = self.parse_expr(0)?;
                let multiline = self.tokens[self.pos].preceded_by_newline;
                self.expect(Token::Else)?;

                let else_branch = self.parse_expr(0)?;
                let end_span = else_branch.span;

                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end_span),
                    kind: ExprKind::If {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                        multiline,
                    },
                })
            }

            Token::Case => {
                self.no_brace_app = true;
                let scrutinee = self.parse_expr(0)?;
                self.no_brace_app = false;
                self.expect(Token::LBrace)?;

                let mut branches = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let start = self.pos;
                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;

                    let guard = if matches!(self.peek(), Token::When) {
                        self.advance();
                        Some(self.parse_expr(0)?)
                    } else {
                        None
                    };

                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span.end;
                    let trailing_comment = self.take_trailing_comment(self.pos - 1);
                    branches.push(Annotated {
                        node: CaseArm {
                            pattern,
                            guard,
                            body,
                            span: Span {
                                start: arm_start.start,
                                end: end_span,
                            },
                        },
                        leading_trivia: self.take_leading_trivia(start),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                }

                let dangling_trivia = self.take_leading_trivia(self.pos);
                let end = self.tokens[self.pos].span; // the RBrace
                self.expect(Token::RBrace)?;

                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::Case {
                        scrutinee: Box::new(scrutinee),
                        arms: branches,
                        dangling_trivia,
                    },
                })
            }

            Token::Receive => {
                self.expect(Token::LBrace)?;

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
                        break; // after must be last
                    }

                    let start = self.pos;
                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;

                    let guard = if matches!(self.peek(), Token::When) {
                        self.advance();
                        Some(self.parse_expr(0)?)
                    } else {
                        None
                    };

                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span.end;
                    let trailing_comment = self.take_trailing_comment(self.pos - 1);
                    branches.push(Annotated {
                        node: CaseArm {
                            pattern,
                            guard,
                            body,
                            span: Span {
                                start: arm_start.start,
                                end: end_span,
                            },
                        },
                        leading_trivia: self.take_leading_trivia(start),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                }

                let dangling_trivia = self.take_leading_trivia(self.pos);
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBrace)?;

                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::Receive {
                        arms: branches,
                        after_clause,
                        dangling_trivia,
                    },
                })
            }

            // Unary negation
            Token::Minus => {
                let expr = self.parse_primary()?;
                let end_span = expr.span.end;
                let neg_span = Span {
                    start: span.start,
                    end: end_span,
                };
                Ok(Expr {
                    id: self.next_id(),
                    span: neg_span,
                    kind: ExprKind::UnaryMinus {
                        expr: Box::new(expr),
                    },
                })
            }

            // Effect call: `log! "hello"` args handled by parse_application
            Token::EffectCall(name) => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::EffectCall {
                    name,
                    qualifier: None,
                    args: Vec::new(),
                },
            }),

            // Resume: `resume value`
            Token::Resume => {
                let value = self.parse_expr(0)?;
                let end = value.span;
                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::Resume {
                        value: Box::new(value),
                    },
                })
            }

            // do...else block: `do { Pat <- expr ... SuccessExpr } else { Pat -> expr ... }`
            Token::Do => {
                self.expect(Token::LBrace)?;

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
                        }
                        _ => {
                            // Not a binding -- restore and parse as success expression
                            self.pos = saved_pos;
                            let success = self.parse_expr(0)?;
                            break success;
                        }
                    }
                };
                self.expect(Token::RBrace)?;

                self.expect(Token::Else)?;
                self.expect(Token::LBrace)?;

                let mut else_arms = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let start = self.pos;
                    let arm_start = self.tokens[self.pos].span;
                    let pattern = self.parse_pattern()?;
                    self.expect(Token::Arrow)?;
                    let body = self.parse_expr(0)?;
                    let end_span = body.span.end;
                    let trailing_comment = self.take_trailing_comment(self.pos - 1);
                    else_arms.push(Annotated {
                        node: CaseArm {
                            pattern,
                            guard: None,
                            body,
                            span: Span {
                                start: arm_start.start,
                                end: end_span,
                            },
                        },
                        leading_trivia: self.take_leading_trivia(start),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                }
                let dangling_trivia = self.take_leading_trivia(self.pos);
                let end = self.tokens[self.pos].span;
                self.expect(Token::RBrace)?;

                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::Do {
                        bindings,
                        success: Box::new(success),
                        else_arms,
                        dangling_trivia,
                    },
                })
            }

            Token::Handler => {
                // handler for Effect { arms... } -- anonymous handler expression
                let parsed = self.parse_handler_body()?;
                let end = self.tokens[self.pos.saturating_sub(1)].span;
                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::HandlerExpr { body: parsed.body },
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
}

