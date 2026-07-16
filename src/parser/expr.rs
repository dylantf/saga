use super::{ParseError, Parser};
use crate::ast::*;
use crate::token::{Span, Token};

impl Parser {
    /// Parse an expression body following `=`, `->`, `then`, or another
    /// explicit body introducer. A body on the same line is a single
    /// expression; a body beginning on the next line is a layout block.
    pub(super) fn parse_expr_body(
        &mut self,
        owner_indent: usize,
        context: &str,
    ) -> Result<Expr, ParseError> {
        if self.next_on_new_line() {
            self.parse_layout_block(owner_indent, context, true)
        } else {
            self.parse_expr(0)
        }
    }

    fn parse_branch_body(
        &mut self,
        owner_indent: usize,
        context: &str,
    ) -> Result<Expr, ParseError> {
        if self.next_on_new_line() {
            self.parse_layout_block(owner_indent, context, false)
        } else {
            self.parse_expr(0)
        }
    }

    fn parse_layout_block(
        &mut self,
        owner_indent: usize,
        context: &str,
        attach_with: bool,
    ) -> Result<Expr, ParseError> {
        let indent = self.begin_layout(owner_indent, context)?;
        let block_start = self.tokens[self.pos].span;
        let mut stmts = Vec::new();

        while self.layout_has_item(indent) {
            if self.next_on_new_line() && !self.next_after_semicolon() {
                if self.next_column() < indent {
                    break;
                }
                self.require_layout_item(indent, context)?;
            }

            let start = self.pos;
            let stmt = self.parse_stmt()?;
            let trailing_comment = self.take_trailing_comment(self.pos - 1);
            stmts.push(Annotated {
                node: stmt,
                leading_trivia: self.take_leading_trivia(start),
                trailing_comment,
                trailing_trivia: vec![],
            });

            // A parser bug or malformed construct must not leave us spinning
            // within the layout loop.
            if self.pos == start {
                return Err(ParseError {
                    message: format!("could not make progress while parsing {}", context),
                    span: self.tokens[self.pos].span,
                });
            }
        }

        if stmts.is_empty() {
            return Err(ParseError {
                message: format!("{} body cannot be empty", context),
                span: self.tokens[self.pos].span,
            });
        }
        let collapse_single_expr = stmts.len() == 1
            && stmts[0].leading_trivia.is_empty()
            && stmts[0].trailing_comment.is_none()
            && stmts[0].trailing_trivia.is_empty();
        let mut expr = if collapse_single_expr {
            match stmts.pop().unwrap().node {
                Stmt::Expr(expr) => expr,
                stmt => {
                    let end = match &stmt {
                        Stmt::Let { span, .. } | Stmt::LetFun { span, .. } => *span,
                        Stmt::Expr(expr) => expr.span,
                    };
                    Expr {
                        id: self.next_id(),
                        span: block_start.to(end),
                        kind: ExprKind::Block {
                            stmts: vec![Annotated::bare(stmt)],
                            dangling_trivia: vec![],
                        },
                    }
                }
            }
        } else {
            let last = stmts.last().unwrap();
            let end = match &last.node {
                Stmt::Let { span, .. } | Stmt::LetFun { span, .. } => *span,
                Stmt::Expr(expr) => expr.span,
            };
            Expr {
                id: self.next_id(),
                span: block_start.to(end),
                kind: ExprKind::Block {
                    stmts,
                    dangling_trivia: vec![],
                },
            }
        };

        // A `with` aligned with the construct that opened this layout block
        // applies to the completed block, not merely its last statement.
        if attach_with
            && matches!(self.peek(), Token::With)
            && self.next_on_new_line()
            && self.next_column() == owner_indent
        {
            self.advance();
            let handler = self.parse_handler_ref(owner_indent)?;
            let end = self.tokens[self.pos.saturating_sub(1)].span;
            let span = expr.span.to(end);
            expr = Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::With {
                    expr: Box::new(expr),
                    handler: Box::new(handler),
                },
            };
        }

        Ok(expr)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        if !matches!(self.peek(), Token::Let) {
            return Ok(Stmt::Expr(self.parse_expr(0)?));
        }

        let owner_indent = self.current_line_indent();
        let let_start = self.tokens[self.pos].span;
        self.advance(); // consume `let`
        let is_assert = matches!(self.peek(), Token::Ident(s) if s == "assert");
        if is_assert {
            self.advance();
        }
        let pattern = self.parse_pattern()?;

        // Local function definition: `let f x y = body`.
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
            let body = self.parse_expr_body(owner_indent, "local function")?;
            let stmt_span = let_start.to(body.span);
            return Ok(Stmt::LetFun {
                id: NodeId::fresh(),
                name: fun_name,
                name_span: fn_name_span,
                params,
                guard,
                body,
                span: stmt_span,
            });
        }

        let annotation =
            if matches!(self.peek(), Token::Colon) && matches!(pattern, Pat::Var { .. }) {
                self.advance();
                Some(self.parse_type_expr()?)
            } else {
                None
            };
        self.expect(Token::Eq)?;
        let value = self.parse_expr_body(owner_indent, "let binding")?;
        let stmt_span = let_start.to(value.span);
        Ok(Stmt::Let {
            pattern,
            annotation,
            value,
            assert: is_assert,
            span: stmt_span,
        })
    }

    fn parse_case_arm(&mut self, arm_indent: usize) -> Result<Annotated<CaseArm>, ParseError> {
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
        let body = self.parse_expr_body(arm_indent, "case arm")?;
        let end_span = body.span.end;
        let trailing_comment = self.take_trailing_comment(self.pos - 1);
        Ok(Annotated {
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
        })
    }

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

    fn parse_upper_path_with_span(&mut self) -> Result<(String, Span), ParseError> {
        let start = self.tokens[self.pos].span;
        let mut name = self.expect_upper_ident()?;
        while matches!(self.peek(), Token::Dot) && matches!(self.peek_at(1), Token::UpperIdent(_)) {
            self.advance(); // consume '.'
            let segment = self.expect_upper_ident()?;
            name = format!("{name}.{segment}");
        }
        let end = self.tokens[self.pos - 1].span;
        Ok((name, start.to(end)))
    }

    fn record_build_ahead_after_build(&self) -> bool {
        let mut i = 0;
        if !matches!(self.peek_at(i), Token::UpperIdent(_)) {
            return false;
        }
        i += 1;
        while matches!(self.peek_at(i), Token::Dot)
            && matches!(self.peek_at(i + 1), Token::UpperIdent(_))
        {
            i += 2;
        }
        if matches!(self.peek_at(i), Token::LBrace) {
            return true;
        }
        if !matches!(self.peek_at(i), Token::UpperIdent(_)) {
            return false;
        }
        i += 1;
        while matches!(self.peek_at(i), Token::Dot)
            && matches!(self.peek_at(i + 1), Token::UpperIdent(_))
        {
            i += 2;
        }
        matches!(self.peek_at(i), Token::LBrace)
    }

    fn parse_record_build(&mut self, build_span: Span) -> Result<Expr, ParseError> {
        let (context, context_span) = self.parse_upper_path_with_span()?;
        let (record, record_span) = if matches!(self.peek(), Token::UpperIdent(_)) {
            let (record, record_span) = self.parse_upper_path_with_span()?;
            (Some(record), Some(record_span))
        } else {
            (None, None)
        };
        self.expect(Token::LBrace)?;
        let fields = self.parse_record_fields()?;
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;
        Ok(Expr {
            id: self.next_id(),
            span: build_span.to(end),
            kind: ExprKind::RecordBuild {
                context,
                context_span,
                record,
                record_span,
                fields,
            },
        })
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
        let owner_indent = self.current_line_indent();
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

            // For <|, >> collect flat chain like |>
            if matches!(self.peek(), Token::PipeBack | Token::ComposeForward) {
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
        if matches!(self.peek(), Token::With)
            && (!self.next_on_new_line() || self.next_column() == owner_indent)
        {
            self.advance();
            let handler = self.parse_handler_ref(owner_indent)?;
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

    /// Function application: `f x y` -> App(App(f, x), y)
    /// Greedily consumes arguments while the next token can start a primary.
    fn parse_application(&mut self) -> Result<Expr, ParseError> {
        let head_pos = self.pos;
        let head_column = self.legacy_statement_indent.map_or_else(
            || self.current_line_indent(),
            |floor| floor.max(self.current_line_indent()),
        );
        let soft_delimited_line = head_pos > 0
            && matches!(
                self.tokens[head_pos - 1].token,
                Token::LParen | Token::LBracket | Token::Comma
            );
        let mut expr = self.parse_postfix()?;

        while self.can_start_primary()
            && (!self.next_on_new_line()
                || (!self.next_after_semicolon()
                    && !self.next_starts_blank_line()
                    && (self.next_column() >= head_column + 2
                        || (soft_delimited_line && self.next_column() >= head_column))))
        {
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
                    ExprKind::QualifiedName {
                        module,
                        name: prev_name,
                        ..
                    } if prev_name.starts_with(|c: char| c.is_uppercase()) => {
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
                // Preserve the qualifier so formatting can round-trip the
                // source even when the type is not imported unqualified.
                // Guarded by `no_brace_app` so `case A.Foo { ... }` parses as
                // case-over-qualified-name, not case over a record literal.
                if name.chars().next().is_some_and(|c| c.is_uppercase())
                    && !self.no_brace_app
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
                        kind: ExprKind::RecordCreate {
                            name: format!("{}.{}", module, name),
                            fields,
                            record_name: None,
                        },
                    };
                    continue;
                }

                expr = Expr {
                    id: self.next_id(),
                    span: qspan,
                    kind: ExprKind::QualifiedName {
                        module,
                        name,
                        canonical_module: None,
                    },
                };
                continue;
            }
            // Multi-level module access: `Std.String.replace` when LHS is already QualifiedName
            // and its name part is uppercase (a module segment, not a function).
            if let ExprKind::QualifiedName {
                module: prev_module,
                name: prev_name,
                ..
            } = &expr.kind
                && prev_name.starts_with(|c: char| c.is_uppercase())
            {
                let extended_module = format!("{}.{}", prev_module, prev_name);
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
                        let end = self.tokens[self.pos - 1].span;
                        let qspan = Span {
                            start,
                            end: end.end,
                        };
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
                let qspan = Span {
                    start,
                    end: end.end,
                };

                // Qualified record create with multi-level module path.
                // See `no_brace_app` comment above for why this is gated.
                if name.chars().next().is_some_and(|c| c.is_uppercase())
                    && !self.no_brace_app
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
                        kind: ExprKind::RecordCreate {
                            name: format!("{}.{}", extended_module, name),
                            fields,
                            record_name: None,
                        },
                    };
                    continue;
                }

                expr = Expr {
                    id: self.next_id(),
                    span: qspan,
                    kind: ExprKind::QualifiedName {
                        module: extended_module,
                        name,
                        canonical_module: None,
                    },
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
                    record_name: None,
                },
            };
        }

        Ok(expr)
    }

    /// Parses the handler reference after `with`:
    /// - `with console_log` -> Handler::Named
    /// - `with { h1, h2, op args -> body }` -> Handler::Inline
    ///   Check if the current position is a named handler ref: a (possibly
    ///   module-qualified) dotted path ending in a lowercase ident, followed
    ///   by `,` or `}`. e.g. `console`, `foo.bar`, `DateTime.system_clock`.
    fn is_named_handler_ref(&self) -> bool {
        let mut i = 0;
        while matches!(self.peek_at(i), Token::UpperIdent(_) | Token::Ident(_))
            && matches!(self.peek_at(i + 1), Token::Dot)
        {
            i += 2;
        }
        matches!(self.peek_at(i), Token::Ident(_))
            && matches!(self.peek_at(i + 1), Token::Comma | Token::RBrace)
    }

    fn is_layout_named_handler_ref(&self, item_indent: usize) -> bool {
        let mut i = 0;
        while matches!(self.peek_at(i), Token::UpperIdent(_) | Token::Ident(_))
            && matches!(self.peek_at(i + 1), Token::Dot)
        {
            i += 2;
        }
        if !matches!(self.peek_at(i), Token::Ident(_)) {
            return false;
        }
        let next = self.pos + i + 1;
        next >= self.tokens.len()
            || matches!(self.tokens[next].token, Token::Eof)
            || matches!(self.tokens[next].token, Token::Comma)
            || (self.tokens[next].preceded_by_newline && self.tokens[next].column <= item_indent)
    }

    /// Parse a named handler ref: a (possibly module-qualified) dotted path.
    fn parse_named_handler_ref(&mut self) -> Result<Annotated<HandlerItem>, ParseError> {
        let start = self.pos;
        let name_start = self.tokens[self.pos].span;
        let mut name = if matches!(self.peek(), Token::UpperIdent(_)) {
            self.expect_upper_ident()?
        } else {
            self.expect_ident()?
        };
        while matches!(self.peek(), Token::Dot)
            && matches!(self.peek_at(1), Token::Ident(_) | Token::UpperIdent(_))
        {
            self.advance(); // consume '.'
            let segment = if matches!(self.peek(), Token::UpperIdent(_)) {
                self.expect_upper_ident()?
            } else {
                self.expect_ident()?
            };
            name = format!("{name}.{segment}");
        }
        let name_end = self.tokens[self.pos - 1].span;
        let mut trailing_comment = None;
        if matches!(self.peek(), Token::Comma) {
            self.advance();
            trailing_comment = self.take_trailing_comment(self.pos - 1);
        }
        Ok(Annotated {
            node: HandlerItem::Named(NamedHandlerRef {
                id: NodeId::fresh(),
                name,
                span: name_start.to(name_end),
            }),
            leading_trivia: self.take_leading_trivia(start),
            trailing_comment,
            trailing_trivia: vec![],
        })
    }

    /// Parse an inline handler arm: `[Qualifier.]op params = body [finally cleanup]`
    fn parse_inline_handler_arm(&mut self) -> Result<Annotated<HandlerItem>, ParseError> {
        let start = self.pos;
        let owner_indent = self.current_line_indent();
        let arm_start = self.tokens[self.pos].span;

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

        // Inline arm: op params = body
        let mut params = Vec::new();
        while !matches!(self.peek(), Token::Eq | Token::Eof) {
            // Skip `()` unit params (zero-param effect ops)
            if matches!(self.peek(), Token::LParen) && matches!(self.peek_at(1), Token::RParen) {
                self.advance(); // consume '('
                self.advance(); // consume ')'
                continue;
            }
            params.push(self.parse_pattern()?);
        }
        self.expect(Token::Eq)?;
        let body = self.parse_expr_body(owner_indent, "handler arm")?;
        let mut arm_end = body.span;

        // Parse optional `finally { cleanup }` block
        let finally_block = if matches!(self.peek(), Token::Finally) {
            self.advance(); // consume 'finally'
            let fb = self.parse_expr_body(owner_indent, "finally")?;
            arm_end = fb.span;
            Some(Box::new(fb))
        } else {
            None
        };

        let trailing_comment = self.take_trailing_comment(self.pos - 1);
        Ok(Annotated {
            node: HandlerItem::Arm(HandlerArm {
                id: NodeId::fresh(),
                op_name: name,
                qualifier,
                params,
                body: Box::new(body),
                finally_block,
                span: arm_start.to(arm_end),
            }),
            leading_trivia: self.take_leading_trivia(start),
            trailing_comment,
            trailing_trivia: vec![],
        })
    }

    /// Parse a return clause: `return param = body`
    fn parse_return_clause(&mut self) -> Result<Annotated<HandlerItem>, ParseError> {
        let start = self.pos;
        let owner_indent = self.current_line_indent();
        let arm_start = self.tokens[self.pos].span;
        self.advance(); // consume 'return'
        let param = self.parse_pattern()?;
        self.expect(Token::Eq)?;
        let body = self.parse_expr_body(owner_indent, "handler return")?;
        let arm_end = body.span;
        let trailing_comment = self.take_trailing_comment(self.pos - 1);
        Ok(Annotated {
            node: HandlerItem::Return(HandlerArm {
                id: NodeId::fresh(),
                op_name: "return".to_string(),
                qualifier: None,
                params: vec![param],
                body: Box::new(body),
                finally_block: None,
                span: arm_start.to(arm_end),
            }),
            leading_trivia: self.take_leading_trivia(start),
            trailing_comment,
            trailing_trivia: vec![],
        })
    }

    fn current_inline_segment_has_return(items: &[Annotated<HandlerItem>]) -> bool {
        items
            .iter()
            .rev()
            .take_while(|ann| !matches!(ann.node, HandlerItem::Named(_)))
            .any(|ann| matches!(ann.node, HandlerItem::Return(_)))
    }

    /// Parses the handler reference after `with`:
    /// - `with console_log` -> Handler::Named
    /// - `with { h1, h2, op args -> body }` -> Handler::Inline
    pub(super) fn parse_handler_ref(&mut self, owner_indent: usize) -> Result<Handler, ParseError> {
        if matches!(self.peek(), Token::LBrace) {
            self.advance(); // consume '{'

            if matches!(self.peek(), Token::RBrace) {
                return Err(ParseError {
                    message: "expected identifier, got RBrace".to_string(),
                    span: self.tokens[self.pos].span,
                });
            }

            let mut items: Vec<Annotated<HandlerItem>> = Vec::new();

            // Unified loop: parse named refs, inline arms, and return clauses
            // in any order.
            while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                if matches!(self.peek(), Token::Return) {
                    if Self::current_inline_segment_has_return(&items) {
                        return Err(ParseError {
                            message: "inline handler segment may contain at most one return clause"
                                .to_string(),
                            span: self.tokens[self.pos].span,
                        });
                    }
                    items.push(self.parse_return_clause()?);
                } else if self.is_named_handler_ref() {
                    items.push(self.parse_named_handler_ref()?);
                } else {
                    items.push(self.parse_inline_handler_arm()?);
                }

                // Commas between items are optional
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                    // Transfer trailing comment from comma to the last item
                    if let Some(comment) = self.tokens[self.pos - 1].trailing_comment.take()
                        && let Some(last_item) = items.last_mut()
                        && last_item.trailing_comment.is_none()
                    {
                        last_item.trailing_comment = Some(comment);
                    }
                }
            }
            let dangling_trivia = self.take_leading_trivia(self.pos);
            self.expect(Token::RBrace)?;

            Ok(Handler::Inline {
                items,
                dangling_trivia,
            })
        } else if self.next_on_new_line() {
            let item_indent = self.begin_layout(owner_indent, "with")?;
            let mut items: Vec<Annotated<HandlerItem>> = Vec::new();
            while self.layout_has_item(item_indent) {
                self.require_layout_item(item_indent, "with")?;
                if matches!(self.peek(), Token::Return) {
                    if Self::current_inline_segment_has_return(&items) {
                        return Err(ParseError {
                            message: "inline handler segment may contain at most one return clause"
                                .to_string(),
                            span: self.tokens[self.pos].span,
                        });
                    }
                    items.push(self.parse_return_clause()?);
                } else if self.is_layout_named_handler_ref(item_indent) {
                    items.push(self.parse_named_handler_ref()?);
                } else {
                    items.push(self.parse_inline_handler_arm()?);
                }
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                }
            }
            if items.is_empty() {
                return Err(ParseError {
                    message: "with body cannot be empty".to_string(),
                    span: self.tokens[self.pos].span,
                });
            }
            Ok(Handler::Inline {
                items,
                dangling_trivia: vec![],
            })
        } else {
            // Single named handler: `with console_log` or `with DateTime.system_clock`
            let handler_span = self.tokens[self.pos].span;
            let mut name = if matches!(self.peek(), Token::UpperIdent(_)) {
                self.expect_upper_ident()?
            } else {
                self.expect_ident()?
            };
            while matches!(self.peek(), Token::Dot)
                && matches!(self.peek_at(1), Token::Ident(_) | Token::UpperIdent(_))
            {
                self.advance(); // consume '.'
                let segment = if matches!(self.peek(), Token::UpperIdent(_)) {
                    self.expect_upper_ident()?
                } else {
                    self.expect_ident()?
                };
                name = format!("{name}.{segment}");
            }
            Ok(Handler::Named(NamedHandlerRef {
                id: NodeId::fresh(),
                name,
                span: handler_span,
            }))
        }
    }

    pub(super) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        let span = self.tokens[self.pos].span;
        let owner_indent = self.current_line_indent();

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
                                preceded_by_semicolon: false,
                                column: 0,
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
            Token::Ident(i) if i == "build" && self.record_build_ahead_after_build() => {
                self.parse_record_build(span)
            }
            Token::Ident(i) => Ok(Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Var { name: i },
            }),
            Token::UpperIdent(i) => {
                // `no_brace_app` suppresses `{`-as-record-create so that
                // `case Foo { ... }` parses `Foo` as a bare constructor and
                // leaves the `{` for the case arms (likewise inside `if`/`with`).
                if !self.no_brace_app && matches!(self.peek(), Token::LBrace) {
                    // Record create: User { name: "Dylan", age: 30 }
                    self.advance(); // consume '{'
                    let fields = self.parse_record_fields()?;
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::RecordCreate {
                            name: i,
                            fields,
                            record_name: None,
                        },
                    })
                } else {
                    // Bare constructor — application is handled by parse_application
                    Ok(Expr {
                        id: self.next_id(),
                        span,
                        kind: ExprKind::Constructor { name: i },
                    })
                }
            }

            Token::LParen => {
                // Inside a delimited sub-expression, reset `no_brace_app` so a
                // `Foo { ... }` record literal within the parens is not
                // misparsed as a bare constructor leaving `{` for the outer
                // case arms. Restored after this branch completes.
                let saved_nba = std::mem::replace(&mut self.no_brace_app, false);
                let saved_case_stop = std::mem::replace(&mut self.stop_at_case_of, false);
                let result: Result<Expr, ParseError> = (|| {
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
                })();
                self.no_brace_app = saved_nba;
                self.stop_at_case_of = saved_case_stop;
                result
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
                // See LParen branch: reset `no_brace_app` inside the delimited
                // sub-expression so record literals can be parsed normally.
                let saved_nba = std::mem::replace(&mut self.no_brace_app, false);
                let saved_case_stop = std::mem::replace(&mut self.stop_at_case_of, false);
                let result: Result<Expr, ParseError> = (|| {
                    // Empty list
                    if matches!(self.peek(), Token::RBracket) {
                        let end = self.tokens[self.pos].span;
                        let dangling_trivia = self.take_leading_trivia(self.pos);
                        self.advance();
                        return Ok(Expr {
                            id: self.next_id(),
                            span: span.to(end),
                            kind: ExprKind::ListLit {
                                elements: vec![],
                                dangling_trivia,
                            },
                        });
                    }

                    let first_start = self.pos;
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
                    let first_trailing = self.take_trailing_comment(self.pos - 1);
                    let mut elements = vec![Annotated {
                        node: first,
                        leading_trivia: self.take_leading_trivia(first_start),
                        trailing_comment: first_trailing,
                        trailing_trivia: vec![],
                    }];
                    while matches!(self.peek(), Token::Comma) {
                        self.advance();
                        if let Some(comment) = self.take_trailing_comment(self.pos - 1)
                            && let Some(last) = elements.last_mut()
                            && last.trailing_comment.is_none()
                        {
                            last.trailing_comment = Some(comment);
                        }
                        if matches!(self.peek(), Token::RBracket) {
                            break; // trailing comma
                        }
                        let elem_start = self.pos;
                        let elem = self.parse_expr(0)?;
                        let trailing_comment = self.take_trailing_comment(self.pos - 1);
                        elements.push(Annotated {
                            node: elem,
                            leading_trivia: self.take_leading_trivia(elem_start),
                            trailing_comment,
                            trailing_trivia: vec![],
                        });
                    }
                    let end = self.tokens[self.pos].span;
                    let dangling_trivia = self.take_leading_trivia(self.pos);
                    self.expect(Token::RBracket)?;
                    Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::ListLit {
                            elements,
                            dangling_trivia,
                        },
                    })
                })();
                self.no_brace_app = saved_nba;
                self.stop_at_case_of = saved_case_stop;
                result
            }

            Token::Fun => {
                let mut params = Vec::new();
                while !matches!(self.peek(), Token::Arrow | Token::Eof) {
                    params.push(self.parse_pattern()?);
                }
                self.expect(Token::Arrow)?;

                let body = self.parse_expr_body(owner_indent, "lambda")?;
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
                                record_name: None,
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

                let statement_indent = if self.next_on_new_line() {
                    self.next_column()
                } else {
                    owner_indent + 2
                };
                let previous_indent = self
                    .legacy_statement_indent
                    .replace(statement_indent.max(self.legacy_statement_indent.unwrap_or(0)));
                let result = (|| -> Result<Expr, ParseError> {
                    let mut stmts: Vec<Annotated<Stmt>> = Vec::new();
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        let start = self.pos;
                        let stmt = self.parse_stmt()?;
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
                })();
                self.legacy_statement_indent = previous_indent;
                result
            }

            Token::If => {
                let cond = self.parse_expr(0)?;
                self.expect(Token::Then)?;

                let then_branch = self.parse_branch_body(owner_indent, "then")?;
                let multiline = self.tokens[self.pos].preceded_by_newline;
                self.expect(Token::Else)?;

                let else_branch = self.parse_branch_body(owner_indent, "else")?;
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
                let outer_case_stop = std::mem::replace(&mut self.stop_at_case_of, true);
                self.no_brace_app = true;
                let scrutinee_result = self.parse_expr(0);
                self.no_brace_app = false;
                self.stop_at_case_of = false;
                let scrutinee = match scrutinee_result {
                    Ok(scrutinee) => scrutinee,
                    Err(error) => {
                        self.stop_at_case_of = outer_case_stop;
                        return Err(error);
                    }
                };
                let mut branches = Vec::new();
                let (end, dangling_trivia) = if matches!(self.peek(), Token::Ident(name) if name == "of")
                {
                    self.advance();
                    let arm_indent = self.begin_layout(owner_indent, "case")?;
                    while self.layout_has_item(arm_indent) {
                        self.require_layout_item(arm_indent, "case")?;
                        branches.push(self.parse_case_arm(arm_indent)?);
                    }
                    let end =
                        branches
                            .last()
                            .map(|arm| arm.node.span)
                            .ok_or_else(|| ParseError {
                                message: "case expression requires at least one arm".to_string(),
                                span: self.tokens[self.pos].span,
                            })?;
                    (end, vec![])
                } else {
                    // Legacy braced form, retained so the formatter can migrate
                    // existing source files in one pass.
                    self.expect(Token::LBrace)?;
                    while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                        let arm_indent = self.token_line_indent(self.pos);
                        branches.push(self.parse_case_arm(arm_indent)?);
                    }
                    let dangling = self.take_leading_trivia(self.pos);
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    (end, dangling)
                };

                let expr = Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::Case {
                        scrutinee: Box::new(scrutinee),
                        arms: branches,
                        dangling_trivia,
                    },
                };
                self.stop_at_case_of = outer_case_stop;
                Ok(expr)
            }

            Token::Receive => {
                let mut branches = Vec::new();
                let mut after_clause = None;
                let legacy_braces = matches!(self.peek(), Token::LBrace);
                let body_indent = if legacy_braces {
                    self.advance();
                    None
                } else {
                    Some(self.begin_layout(owner_indent, "receive")?)
                };

                while if legacy_braces {
                    !matches!(self.peek(), Token::RBrace | Token::Eof)
                } else {
                    self.layout_has_item(body_indent.unwrap())
                } {
                    if let Some(indent) = body_indent {
                        self.require_layout_item(indent, "receive")?;
                    }
                    // Check for `after` clause
                    if matches!(self.peek(), Token::After) {
                        let after_indent = self.current_line_indent();
                        self.advance(); // consume 'after'
                        let timeout = self.parse_expr(0)?;
                        self.expect(Token::Arrow)?;
                        let body = self.parse_expr_body(after_indent, "receive after")?;
                        after_clause = Some((Box::new(timeout), Box::new(body)));
                        break; // after must be last
                    }
                    let arm_indent = body_indent.unwrap_or_else(|| self.current_line_indent());
                    branches.push(self.parse_case_arm(arm_indent)?);
                }

                let (dangling_trivia, end) = if legacy_braces {
                    let dangling = self.take_leading_trivia(self.pos);
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RBrace)?;
                    (dangling, end)
                } else {
                    let end = after_clause
                        .as_ref()
                        .map(|(_, body)| body.span)
                        .or_else(|| branches.last().map(|arm| arm.node.span))
                        .ok_or_else(|| ParseError {
                            message: "receive body cannot be empty".to_string(),
                            span: self.tokens[self.pos].span,
                        })?;
                    (vec![], end)
                };

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

            // Sequential pattern binding with an explicit success expression.
            Token::Do => {
                let saved_nba = std::mem::replace(&mut self.no_brace_app, false);
                let result: Result<Expr, ParseError> = (|| {
                    let mut bindings = Vec::new();
                    let mut else_arms = Vec::new();
                    let legacy_braces = matches!(self.peek(), Token::LBrace);
                    let do_indent = if legacy_braces {
                        self.advance();
                        None
                    } else {
                        Some(self.begin_layout(owner_indent, "do")?)
                    };

                    let success = loop {
                        if legacy_braces && matches!(self.peek(), Token::RBrace | Token::Eof) {
                            return Err(ParseError {
                                message: "do block missing success expression".to_string(),
                                span: self.tokens[self.pos].span,
                            });
                        }
                        if let Some(indent) = do_indent {
                            if !self.layout_has_item(indent) {
                                return Err(ParseError {
                                    message: "do block missing success expression".to_string(),
                                    span: self.tokens[self.pos].span,
                                });
                            }
                            self.require_layout_item(indent, "do")?;
                        }
                        let saved = self.save();
                        match self.parse_pattern() {
                            Ok(pat) if matches!(self.peek(), Token::LeftArrow) => {
                                self.advance();
                                let binding_indent =
                                    do_indent.unwrap_or_else(|| self.token_line_indent(saved.pos));
                                let expr = self.parse_expr_body(binding_indent, "do binding")?;
                                bindings.push((pat, expr));
                            }
                            _ => {
                                self.restore(saved);
                                break self.parse_expr(0)?;
                            }
                        }
                    };
                    if legacy_braces {
                        self.expect(Token::RBrace)?;
                    }

                    self.expect(Token::Else)?;
                    let dangling_trivia = if matches!(self.peek(), Token::LBrace) {
                        self.advance();
                        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                            let arm_indent = self.token_line_indent(self.pos);
                            else_arms.push(self.parse_case_arm(arm_indent)?);
                        }
                        let dangling = self.take_leading_trivia(self.pos);
                        self.expect(Token::RBrace)?;
                        dangling
                    } else {
                        let arm_indent = self.begin_layout(owner_indent, "do else")?;
                        while self.layout_has_item(arm_indent) {
                            self.require_layout_item(arm_indent, "do else")?;
                            else_arms.push(self.parse_case_arm(arm_indent)?);
                        }
                        vec![]
                    };
                    let end =
                        else_arms
                            .last()
                            .map(|arm| arm.node.span)
                            .ok_or_else(|| ParseError {
                                message: "do else body cannot be empty".to_string(),
                                span: self.tokens[self.pos].span,
                            })?;

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
                })();
                self.no_brace_app = saved_nba;
                result
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

            // <<seg, seg, ...>> -- bitstring construction
            Token::ComposeBack => {
                // <<>> -- empty bitstring
                if matches!(self.peek(), Token::ComposeForward) {
                    let end = self.tokens[self.pos].span;
                    self.advance(); // consume >>
                    return Ok(Expr {
                        id: self.next_id(),
                        span: span.to(end),
                        kind: ExprKind::BitString { segments: vec![] },
                    });
                }

                let mut segments = Vec::new();
                loop {
                    let seg = self.parse_bit_segment_expr()?;
                    segments.push(seg);
                    if matches!(self.peek(), Token::Comma) {
                        self.advance(); // consume ,
                    } else {
                        break;
                    }
                }
                let end = self.tokens[self.pos].span;
                self.expect(Token::ComposeForward)?; // consume >>
                Ok(Expr {
                    id: self.next_id(),
                    span: span.to(end),
                    kind: ExprKind::BitString { segments },
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

    /// Parse a single bitstring segment in expression position.
    /// `value` or `value:size` or `value/specs` or `value:size/specs`
    fn parse_bit_segment_expr(&mut self) -> Result<BitSegment<Expr>, ParseError> {
        let start = self.tokens[self.pos].span;
        // Use parse_postfix for the value so we don't consume `:` or `/` as binary ops
        let value = self.parse_postfix()?;

        let size = if matches!(self.peek(), Token::Colon) {
            self.advance(); // consume :
            // Size is a simple expression (int literal or variable)
            let size_expr = self.parse_postfix()?;
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

    /// Parse bitstring type specifiers: `integer-unsigned-big`
    pub(super) fn parse_bit_specs(&mut self) -> Result<Vec<BitSegSpec>, ParseError> {
        let mut specs = Vec::new();
        loop {
            let spec = match self.peek() {
                Token::Ident(s) => match s.as_str() {
                    "integer" => BitSegSpec::Integer,
                    "float" => BitSegSpec::Float,
                    "binary" => BitSegSpec::Binary,
                    "utf8" => BitSegSpec::Utf8,
                    "big" => BitSegSpec::Big,
                    "little" => BitSegSpec::Little,
                    "native" => BitSegSpec::Native,
                    "signed" => BitSegSpec::Signed,
                    "unsigned" => BitSegSpec::Unsigned,
                    other => {
                        return Err(ParseError {
                            message: format!("unknown bitstring specifier: {}", other),
                            span: self.tokens[self.pos].span,
                        });
                    }
                },
                _ => {
                    return Err(ParseError {
                        message: "expected bitstring type specifier after '/'".to_string(),
                        span: self.tokens[self.pos].span,
                    });
                }
            };
            self.advance(); // consume the specifier ident
            specs.push(spec);
            if matches!(self.peek(), Token::Minus) {
                self.advance(); // consume -
            } else {
                break;
            }
        }
        Ok(specs)
    }
}
