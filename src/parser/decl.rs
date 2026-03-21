use crate::ast::*;
use crate::token::{Span, Token};

use super::{ParseError, Parser};

/// Parsed type annotation: labeled params, return type, and effect requirements.
type AnnotatedSignature = (Vec<(String, TypeExpr)>, TypeExpr, Vec<EffectRef>);

impl Parser {
    // Parse `Name` or `Module.Name`, returning the full qualified string.
    // Used where we want to preserve the qualification (e.g. needs lists).
    fn parse_effect_ref(&mut self) -> Result<EffectRef, ParseError> {
        let start = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let name = if matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'
            let qualifier = self.expect_upper_ident()?;
            format!("{}.{}", name, qualifier)
        } else {
            name
        };
        let mut type_args = Vec::new();
        while self.can_start_type_atom_no_brace() {
            type_args.push(self.parse_type_atom()?);
        }
        let end = self.tokens[self.pos - 1].span;
        let span = Span {
            start: start.start,
            end: end.end,
        };
        Ok(EffectRef {
            name,
            type_args,
            span,
        })
    }

    // Parse `Name` or `Module.Name`, returning only the base name.
    // Used where runtime/typechecker keys are bare names (traits, types, effects).
    fn parse_upper_name(&mut self) -> Result<String, ParseError> {
        let name = self.expect_upper_ident()?;
        if matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'
            Ok(self.expect_upper_ident()?) // discard module prefix, return base name
        } else {
            Ok(name)
        }
    }

    // --- Declarations ---

    pub(super) fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        match self.peek() {
            Token::Type => self.parse_type_def(false, false),
            Token::Opaque => {
                self.advance(); // consume 'opaque'
                self.parse_type_def(true, true)
            }
            Token::Record => self.parse_record_def(false),
            Token::Let => {
                let start = self.tokens[self.pos].span;
                self.advance(); // consume 'let'
                let name = self.expect_ident()?;
                let annotation = if matches!(self.peek(), Token::Colon) {
                    self.advance(); // consume ':'
                    Some(self.parse_type_expr()?)
                } else {
                    None
                };
                self.expect(Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Decl::Let {
                    id: NodeId::fresh(),
                    span: start.to(value.span),
                    name,
                    annotation,
                    value,
                })
            }
            Token::At => {
                let start = self.tokens[self.pos].span;
                self.parse_external_fun(false, start)
            }
            Token::Pub => {
                let start = self.tokens[self.pos].span;
                self.advance(); // consume 'pub'
                match self.peek() {
                    Token::Fun => self.parse_fun_annotation(true, start),
                    Token::At => self.parse_external_fun(true, start),
                    Token::Type => self.parse_type_def(true, false),
                    Token::Opaque => {
                        self.advance(); // consume 'opaque'
                        self.parse_type_def(true, true)
                    }
                    Token::Record => self.parse_record_def(true),
                    Token::Effect => self.parse_effect_def(true),
                    Token::Handler => self.parse_handler_def(true),
                    Token::Trait => self.parse_trait_def(true),
                    _ => Err(ParseError {
                        message: format!("Expected declaration after 'pub', got {:?}", self.peek()),
                        span: self.tokens[self.pos].span,
                    }),
                }
            }
            Token::Fun => {
                let start = self.tokens[self.pos].span;
                self.parse_fun_annotation(false, start)
            }
            Token::Effect => self.parse_effect_def(false),
            Token::Handler => self.parse_handler_def(false),
            Token::Trait => self.parse_trait_def(false),
            Token::Impl => self.parse_impl_def(),
            Token::Module => self.parse_module_decl(),
            Token::Import => self.parse_import_decl(),
            Token::Ident(s)
                if self.test_mode
                    && (s == "test" || s == "describe" || s == "skip")
                    && matches!(
                        self.tokens.get(self.pos + 1).map(|t| &t.token),
                        Some(Token::String(_))
                    ) =>
            {
                // Top-level test/describe: parse as expression (desugar triggers in parse_primary)
                let start = self.tokens[self.pos].span;
                let value = self.parse_expr(0)?;
                Ok(Decl::Let {
                    id: NodeId::fresh(),
                    name: "_".to_string(),
                    annotation: None,
                    span: start.to(value.span),
                    value,
                })
            }
            Token::Ident(_) => self.parse_fun_binding(),
            _ => Err(ParseError {
                message: format!("Expected declaration, got {:?}", self.peek()),
                span: self.tokens[self.pos].span,
            }),
        }
    }

    // Parses: record <Name> [type_params...] { <field>: <Type>, ... }
    fn parse_record_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'record'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let mut type_params = Vec::new();
        while !matches!(self.peek(), Token::LBrace | Token::Eof) {
            type_params.push(self.expect_ident()?);
        }
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

        // Parse optional `deriving (Debug, Show, ...)`
        let mut deriving = Vec::new();
        if matches!(self.peek(), Token::Deriving) {
            self.advance();
            self.expect(Token::LParen)?;
            loop {
                deriving.push(self.expect_upper_ident()?);
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(Token::RParen)?;
        }

        Ok(Decl::RecordDef {
            id: NodeId::fresh(),
            public,
            name,
            name_span,
            type_params,
            fields,
            deriving,
            span: start.to(end),
        })
    }

    fn parse_type_def(&mut self, public: bool, opaque: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'type'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let mut type_params = Vec::new();
        while !matches!(self.peek(), Token::LBrace | Token::Eof) {
            type_params.push(self.expect_ident()?);
        }
        self.expect(Token::LBrace)?;
        self.skip_terminators();
        let mut variants = Vec::new();
        while !matches!(self.peek(), Token::RBrace) {
            if matches!(self.peek(), Token::Bar) {
                self.advance(); // skip optional `|` separator
            }
            variants.push(self.parse_type_constructor_def()?);
            self.skip_terminators();
        }
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        // Parse optional `deriving (Show, Eq, ...)`
        let mut deriving = Vec::new();
        if matches!(self.peek(), Token::Deriving) {
            self.advance(); // consume 'deriving'
            self.expect(Token::LParen)?;
            loop {
                deriving.push(self.expect_upper_ident()?);
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(Token::RParen)?;
        }

        Ok(Decl::TypeDef {
            id: NodeId::fresh(),
            public,
            opaque,
            name,
            name_span,
            type_params,
            variants,
            deriving,
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
            fields.push(self.parse_labeled_type_field()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                fields.push(self.parse_labeled_type_field()?);
            }
            self.expect(Token::RParen)?;
        }

        let end = self.tokens[self.pos - 1].span;
        Ok(TypeConstructor {
            id: NodeId::fresh(),
            name,
            fields,
            span: start.to(end),
        })
    }

    /// Parse an optional label followed by a type expression: `radius: Float` or just `Float`.
    fn parse_labeled_type_field(&mut self) -> Result<(Option<String>, TypeExpr), ParseError> {
        // Try label: if we see `ident :`, it's a labeled field
        if let Token::Ident(name) = self.peek() {
            let name = name.clone();
            let save = self.pos;
            self.advance();
            if matches!(self.peek(), Token::Colon) {
                self.advance(); // consume ':'
                let ty = self.parse_type_expr()?;
                return Ok((Some(name), ty));
            }
            // Not a label, backtrack
            self.pos = save;
        }
        let ty = self.parse_type_expr()?;
        Ok((None, ty))
    }

    // Parses: [pub] fun <name> (<p>: <Type>) ... -> <ReturnType> [needs {Effect, ...}]
    fn parse_fun_annotation(&mut self, public: bool, start: Span) -> Result<Decl, ParseError> {
        self.advance(); // consume 'fun'
        let name = self.expect_ident()?;
        let name_span = self.tokens[self.pos - 1].span;

        self.expect(Token::Colon)?;
        let (params, return_type, effects) = self.parse_annotated_signature()?;

        // Parse optional `where {a: Show + Eq, b: Ord}`
        let where_clause = self.parse_where_clause()?;

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::FunAnnotation {
            id: NodeId::fresh(),
            public,
            name,
            name_span,
            params,
            return_type,
            effects,
            where_clause,
            span: start.to(end),
        })
    }

    // Parses: @external("erlang", "module", "func") [pub] fun name (params) -> RetType
    fn parse_external_fun(&mut self, public: bool, start: Span) -> Result<Decl, ParseError> {
        self.advance(); // consume '@'

        // Expect 'external' identifier
        match self.peek() {
            Token::Ident(s) if s == "external" => {
                self.advance();
            }
            _ => {
                return Err(ParseError {
                    message: format!("expected 'external' after '@', got {:?}", self.peek()),
                    span: self.tokens[self.pos].span,
                });
            }
        }

        // Parse (runtime, module, func)
        self.expect(Token::LParen)?;
        let runtime = match self.advance() {
            Token::String(s) => s,
            tok => {
                return Err(ParseError {
                    message: format!("expected string literal for runtime, got {:?}", tok),
                    span: self.tokens[self.pos - 1].span,
                });
            }
        };
        self.expect(Token::Comma)?;
        let module = match self.advance() {
            Token::String(s) => s,
            tok => {
                return Err(ParseError {
                    message: format!("expected string literal for module, got {:?}", tok),
                    span: self.tokens[self.pos - 1].span,
                });
            }
        };
        self.expect(Token::Comma)?;
        let func = match self.advance() {
            Token::String(s) => s,
            tok => {
                return Err(ParseError {
                    message: format!("expected string literal for function, got {:?}", tok),
                    span: self.tokens[self.pos - 1].span,
                });
            }
        };
        self.expect(Token::RParen)?;

        // Skip terminators between @external(...) and fun signature
        self.skip_terminators();

        // Parse the fun signature (no body)
        self.expect(Token::Fun)?;
        let name = self.expect_ident()?;

        self.expect(Token::Colon)?;
        let (params, return_type, effects) = self.parse_annotated_signature()?;

        let where_clause = self.parse_where_clause()?;

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::ExternalFun {
            id: NodeId::fresh(),
            public,
            name,
            runtime,
            module,
            func,
            params,
            return_type,
            effects,
            where_clause,
            span: start.to(end),
        })
    }

    // Parses: effect <Name> { fun <op> (<p>: <T>) ... -> <T> ... }
    fn parse_effect_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'effect'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let mut type_params = Vec::new();
        while matches!(self.peek(), Token::Ident(_)) {
            type_params.push(self.expect_ident()?);
        }
        self.expect(Token::LBrace)?;
        self.skip_terminators();

        let mut operations = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let op_start = self.tokens[self.pos].span;
            self.expect(Token::Fun)?;
            let op_name = self.expect_ident()?;

            self.expect(Token::Colon)?;
            let (params, return_type, _effects) = self.parse_annotated_signature()?;
            let op_end = self.tokens[self.pos - 1].span;

            operations.push(EffectOp {
                name: op_name,
                params,
                return_type,
                span: op_start.to(op_end),
            });
            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::EffectDef {
            id: NodeId::fresh(),
            public,
            name,
            name_span,
            type_params,
            operations,
            span: start.to(end),
        })
    }

    // Parses: handler <name> for <Effect>, ... { <op> <params> -> <body> ... }
    fn parse_handler_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'handler'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_ident()?;
        self.expect(Token::For)?;

        let mut effects = vec![self.parse_effect_ref()?];
        while matches!(self.peek(), Token::Comma) {
            self.advance();
            effects.push(self.parse_effect_ref()?);
        }

        let mut needs = Vec::new();
        if matches!(self.peek(), Token::Needs) {
            self.advance(); // consume 'needs'
            self.expect(Token::LBrace)?;
            needs.push(self.parse_effect_ref()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                if matches!(self.peek(), Token::RBrace) {
                    break; // trailing comma
                }
                needs.push(self.parse_effect_ref()?);
            }
            self.expect(Token::RBrace)?;
        }

        self.expect(Token::LBrace)?;
        self.skip_terminators();

        let mut arms = Vec::new();
        let mut recovered_arms = Vec::new();
        let mut return_clause = None;

        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let arm_start = self.tokens[self.pos].span;
            let save = self.pos;

            let arm_result: Result<(), ParseError> = (|| {
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
                    let op_name = self.expect_ident()?;
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
                        op_name,
                        params,
                        body: Box::new(body),
                        span: arm_start.to(arm_end),
                    });
                }
                Ok(())
            })();

            if arm_result.is_err() {
                // Recovery: try to salvage the op name for LSP hover
                self.pos = save;
                if let Token::Ident(_) = self.peek() {
                    let op_name = self.expect_ident().unwrap();
                    let mut params = Vec::new();
                    while !matches!(
                        self.peek(),
                        Token::Eq | Token::Terminator | Token::RBrace | Token::Eof
                    ) {
                        let pspan = self.tokens[self.pos].span;
                        if let Ok(p) = self.expect_ident() {
                            params.push((p, pspan));
                        } else {
                            break;
                        }
                    }
                    let end = self.tokens[self.pos.saturating_sub(1)].span;
                    recovered_arms.push(HandlerArm {
                        op_name,
                        params,
                        body: Box::new(Expr {
                            id: NodeId::fresh(),
                            kind: ExprKind::Lit { value: Lit::Unit },
                            span: end,
                        }),
                        span: arm_start.to(end),
                    });
                }
                while !matches!(self.peek(), Token::Terminator | Token::RBrace | Token::Eof) {
                    self.advance();
                }
            }

            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::HandlerDef {
            id: NodeId::fresh(),
            public,
            name,
            name_span,
            effects,
            needs,
            arms,
            recovered_arms,
            return_clause,
            span: start.to(end),
        })
    }

    fn parse_trait_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'trait'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let type_param = self.expect_ident()?;

        let mut supertraits = Vec::new();
        if *self.peek() == Token::Where {
            self.advance();
            self.expect(Token::LBrace)?;

            while *self.peek() != Token::RBrace {
                if !supertraits.is_empty() {
                    self.expect(Token::Comma)?;
                    if *self.peek() == Token::RBrace {
                        break;
                    }
                }

                // `a: Show + Eq` we ignore the type var since it must be the trait's param
                self.expect_ident()?;
                self.expect(Token::Colon)?;
                let st_name = self.parse_upper_name()?;
                let st_span = self.tokens[self.pos - 1].span;
                supertraits.push((st_name, st_span));

                while *self.peek() == Token::Plus {
                    self.advance();
                    let st_name = self.parse_upper_name()?;
                    let st_span = self.tokens[self.pos - 1].span;
                    supertraits.push((st_name, st_span));
                }
            }

            self.expect(Token::RBrace)?;
        }

        self.expect(Token::LBrace)?;
        self.skip_terminators();

        let mut methods = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let method_start = self.tokens[self.pos].span;
            self.expect(Token::Fun)?;
            let method_name = self.expect_ident()?;

            self.expect(Token::Colon)?;
            let (params, return_type, _effects) = self.parse_annotated_signature()?;
            let method_end = self.tokens[self.pos - 1].span;

            methods.push(TraitMethod {
                name: method_name,
                params,
                return_type,
                span: method_start.to(method_end),
            });
            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::TraitDef {
            id: NodeId::fresh(),
            public,
            name,
            name_span,
            type_param,
            supertraits,
            methods,
            span: start.to(end),
        })
    }

    /// Parse `where {a: Show + Eq, b: Ord}` clause, returns empty vec if no `where` keyword
    fn parse_where_clause(&mut self) -> Result<Vec<crate::ast::TraitBound>, ParseError> {
        if *self.peek() != Token::Where {
            return Ok(Vec::new());
        }
        self.advance();
        self.expect(Token::LBrace)?;
        let mut bounds = Vec::new();
        while *self.peek() != Token::RBrace {
            if !bounds.is_empty() {
                self.expect(Token::Comma)?;
                if *self.peek() == Token::RBrace {
                    break;
                }
            }
            let type_var = self.expect_ident()?;
            self.expect(Token::Colon)?;
            let name = self.parse_upper_name()?;
            let span = self.tokens[self.pos - 1].span;
            let mut traits = vec![(name, span)];
            while *self.peek() == Token::Plus {
                self.advance();
                let name = self.parse_upper_name()?;
                let span = self.tokens[self.pos - 1].span;
                traits.push((name, span));
            }
            bounds.push(crate::ast::TraitBound { type_var, traits });
        }
        self.expect(Token::RBrace)?;
        Ok(bounds)
    }

    fn parse_impl_def(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume impl

        let trait_name = self.parse_upper_name()?;
        let trait_name_span = self.tokens[self.pos - 1].span;
        self.expect(Token::For)?;
        let target_type = self.parse_upper_name()?;
        let target_type_span = self.tokens[self.pos - 1].span;

        // Parse optional type params: `impl Show for Box a b`
        let mut type_params = Vec::new();
        while matches!(self.peek(), Token::Ident(_)) {
            type_params.push(self.expect_ident()?);
        }

        let where_clause = self.parse_where_clause()?;

        let mut needs = Vec::new();
        if matches!(self.peek(), Token::Needs) {
            self.advance(); // consume 'needs'
            self.expect(Token::LBrace)?;
            needs.push(self.parse_effect_ref()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                if matches!(self.peek(), Token::RBrace) {
                    break; // trailing comma
                }
                needs.push(self.parse_effect_ref()?);
            }
            self.expect(Token::RBrace)?;
        }

        self.expect(Token::LBrace)?;
        self.skip_terminators();

        let mut methods = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let name = self.expect_ident()?;
            let name_span = self.tokens[self.pos - 1].span;
            let mut params = Vec::new();
            while !matches!(self.peek(), Token::Eq | Token::Eof) {
                params.push(self.parse_pattern()?);
            }

            self.expect(Token::Eq)?;
            let body = self.parse_expr(0)?;
            methods.push((name, name_span, params, body));
            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::ImplDef {
            id: NodeId::fresh(),
            trait_name,
            trait_name_span,
            target_type,
            target_type_span,
            type_params,
            where_clause,
            needs,
            methods,
            span: start.to(end),
        })
    }

    // Parses: <name> <pat> ... [| <guard>] = <body>
    fn parse_fun_binding(&mut self) -> Result<Decl, ParseError> {
        let name_span = self.tokens[self.pos].span;
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
            id: NodeId::fresh(),
            name,
            name_span,
            params,
            guard,
            body,
            span: name_span.to(end),
        })
    }

    // --- Annotated signatures ---

    /// Parse an annotated type signature after the `:`.
    /// Each arrow segment can optionally have a label: `(label: Type) -> Type -> RetType`
    /// Returns (params, return_type, effects).
    fn parse_annotated_signature(&mut self) -> Result<AnnotatedSignature, ParseError> {
        // Collect all arrow segments: parse "A -> B -> C -> D" as [A, B, C, D]
        // Each segment is either (Some(label), type) or (None, type)
        let mut segments: Vec<(Option<String>, TypeExpr)> = Vec::new();
        segments.push(self.parse_labeled_type_segment()?);

        while matches!(self.peek(), Token::Arrow) {
            self.advance(); // consume '->'
            segments.push(self.parse_labeled_type_segment()?);
        }

        // Parse trailing `needs {...}` if present
        let mut effects = Vec::new();
        if matches!(self.peek(), Token::Needs) {
            self.advance();
            self.expect(Token::LBrace)?;
            effects.push(self.parse_effect_ref()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                effects.push(self.parse_effect_ref()?);
            }
            self.expect(Token::RBrace)?;
        }

        if segments.len() < 2 {
            // No arrow at all, e.g. `fun x : Int` -- just a constant annotation
            let (_label, ty) = segments.pop().unwrap();
            return Ok((vec![], ty, effects));
        }

        // Last segment is the return type, rest are params
        let (_, return_type) = segments.pop().unwrap();
        let params: Vec<(String, TypeExpr)> = segments
            .into_iter()
            .enumerate()
            .map(|(i, (label, ty))| {
                let name = label.unwrap_or_else(|| format!("_{}", i));
                (name, ty)
            })
            .collect();

        Ok((params, return_type, effects))
    }

    /// Parse a single type segment that may have an optional label: `(label: Type)` or just `Type`.
    fn parse_labeled_type_segment(&mut self) -> Result<(Option<String>, TypeExpr), ParseError> {
        // Check for `(label: Type)` pattern
        if matches!(self.peek(), Token::LParen) {
            // Peek ahead to see if this is `(ident : ...` (labeled) or just a parenthesized/tuple type
            if self.is_labeled_param() {
                self.advance(); // consume '('
                let label = self.expect_ident()?;
                self.expect(Token::Colon)?;
                let ty = self.parse_type_expr()?;
                self.expect(Token::RParen)?;
                return Ok((Some(label), ty));
            }
        }

        // Regular type (may include application: `Option a`, `Result String Int`)
        let seg_start = self.tokens[self.pos].span;
        let mut left = self.parse_type_atom()?;
        while self.can_start_type_atom() {
            let arg = self.parse_type_atom()?;
            let span = seg_start.to(arg.span());
            left = TypeExpr::App { func: Box::new(left), arg: Box::new(arg), span };
        }
        Ok((None, left))
    }

    /// Look ahead to check if we have `(ident :` which signals a labeled parameter.
    fn is_labeled_param(&self) -> bool {
        // Current token is '('. Check pos+1 is an ident and pos+2 is ':'
        let base = self.pos + 1;
        if base + 1 >= self.tokens.len() {
            return false;
        }
        matches!(self.tokens[base].token, Token::Ident(_))
            && matches!(self.tokens[base + 1].token, Token::Colon)
    }

    // --- Type expressions ---

    pub(super) fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        let start = self.tokens[self.pos].span;
        // First: parse a type with possible application (`Option a`, `Result a e`)
        let mut left = self.parse_type_atom()?;
        while self.can_start_type_atom() {
            let arg = self.parse_type_atom()?;
            let span = start.to(arg.span());
            left = TypeExpr::App { func: Box::new(left), arg: Box::new(arg), span };
        }

        // Then: check for arrow (right-associative)
        if matches!(self.peek(), Token::Arrow) {
            self.advance();
            let right = self.parse_type_expr()?; // recurse = right-associative
            let mut needs = Vec::new();
            if matches!(self.peek(), Token::Needs) {
                self.advance();
                self.expect(Token::LBrace)?;
                while !matches!(self.peek(), Token::RBrace) {
                    needs.push(self.parse_effect_ref()?);
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                }
                self.expect(Token::RBrace)?;
            }
            let end = self.tokens[self.pos - 1].span;
            let span = start.to(end);
            Ok(TypeExpr::Arrow { from: Box::new(left), to: Box::new(right), effects: needs, span })
        } else {
            Ok(left)
        }
    }

    fn parse_type_atom(&mut self) -> Result<TypeExpr, ParseError> {
        let start = self.tokens[self.pos].span;
        match self.advance() {
            Token::UpperIdent(s) => {
                // Support qualified type names: `Module.Type`
                if matches!(self.peek(), Token::Dot) {
                    self.advance(); // consume '.'
                    let end = self.tokens[self.pos].span;
                    let name = self.expect_upper_ident()?;
                    Ok(TypeExpr::Named { name: format!("{}.{}", s, name), span: start.to(end) })
                } else {
                    Ok(TypeExpr::Named { name: s, span: start })
                }
            }
            Token::Ident(s) => Ok(TypeExpr::Var { name: s, span: start }),
            Token::LParen => {
                // () is the Unit type
                if matches!(self.peek(), Token::RParen) {
                    let end = self.tokens[self.pos].span;
                    self.advance();
                    return Ok(TypeExpr::Named { name: "Unit".to_string(), span: start.to(end) });
                }
                let first = self.parse_type_expr()?;
                if matches!(self.peek(), Token::Comma) {
                    // Tuple type: (Int, String, ...)
                    let mut elements = vec![first];
                    while matches!(self.peek(), Token::Comma) {
                        self.advance();
                        if matches!(self.peek(), Token::RParen) {
                            break;
                        }
                        elements.push(self.parse_type_expr()?);
                    }
                    let end = self.tokens[self.pos].span;
                    self.expect(Token::RParen)?;
                    let span = start.to(end);
                    let mut result = TypeExpr::Named { name: "Tuple".into(), span };
                    for elem in elements {
                        let elem_span = start.to(elem.span());
                        result = TypeExpr::App { func: Box::new(result), arg: Box::new(elem), span: elem_span };
                    }
                    Ok(result)
                } else {
                    self.expect(Token::RParen)?;
                    Ok(first)
                }
            }
            Token::LBrace => {
                // Anonymous record type: { field: Type, ... }
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
                Ok(TypeExpr::Record { fields, span: start.to(end) })
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

    // --- Module declarations ---

    // Parses: module Foo.Bar.Baz
    fn parse_module_decl(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'module'
        let mut path = vec![self.expect_upper_ident()?];
        while matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'
            path.push(self.expect_upper_ident()?);
        }
        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::ModuleDecl {
            id: NodeId::fresh(),
            path,
            span: start.to(end),
        })
    }

    // Parses:
    //   import Math
    //   import Math as M
    //   import Math (abs, max)
    //   import Math as M (abs, max)
    //   import Foo.Bar
    fn parse_import_decl(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'import'

        let mut module_path = vec![self.expect_upper_ident()?];
        while matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'
            module_path.push(self.expect_upper_ident()?);
        }

        // Optional: as Alias
        let alias = if matches!(self.peek(), Token::As) {
            self.advance(); // consume 'as'
            Some(self.expect_upper_ident()?)
        } else {
            None
        };

        // Optional: (name1, Name2, ...) — unqualified imports
        // Capital names are inferred as types and hoist their constructors automatically.
        let exposing = if matches!(self.peek(), Token::LParen) {
            self.advance(); // consume '('
            let mut items = Vec::new();
            while !matches!(self.peek(), Token::RParen | Token::Eof) {
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
                            message: format!("expected identifier in import list, got {:?}", tok),
                            span: self.tokens[self.pos].span,
                        });
                    }
                };
                items.push(name);
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                }
            }
            let end = self.tokens[self.pos].span;
            self.expect(Token::RParen)?;
            Some((items, end))
        } else {
            None
        };

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::Import {
            id: NodeId::fresh(),
            module_path,
            alias,
            exposing: exposing.map(|(items, _)| items),
            span: start.to(end),
        })
    }
}
