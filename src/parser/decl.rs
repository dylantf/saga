use crate::ast::*;
use crate::token::{Span, Token};

use super::{ParseError, Parser};

/// Parsed type annotation: labeled params, return type, and effect requirements.
type AnnotatedSignature = (Vec<(String, TypeExpr)>, TypeExpr, Vec<EffectRef>, Option<(String, Span)>);

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
                let name_span = self.tokens[self.pos - 1].span;
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
                    name_span,
                    annotation,
                    value,
                })
            }
            Token::At => {
                let start = self.tokens[self.pos].span;
                let annotations = self.parse_annotations()?;
                // After annotations, expect a function declaration (optionally pub)
                let public = if matches!(self.peek(), Token::Pub) {
                    self.advance();
                    true
                } else {
                    false
                };
                if !matches!(self.peek(), Token::Fun) {
                    return Err(ParseError {
                        message: format!("expected 'fun' after annotation, got {:?}", self.peek()),
                        span: self.tokens[self.pos].span,
                    });
                }
                self.parse_fun_signature(public, start, annotations)
            }
            Token::Pub => {
                let start = self.tokens[self.pos].span;
                self.advance(); // consume 'pub'
                match self.peek() {
                    Token::Fun => self.parse_fun_signature(true, start, vec![]),
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
                self.parse_fun_signature(false, start, vec![])
            }
            Token::Effect => self.parse_effect_def(false),
            Token::Handler => self.parse_handler_def(false),
            Token::Trait => self.parse_trait_def(false),
            Token::Impl => self.parse_impl_def(),
            Token::Module => self.parse_module_decl(),
            Token::Import => self.parse_import_decl(),
            Token::Ident(s)
                if self.test_mode
                    && (s == "test" || s == "describe" || s == "skip" || s == "only")
                    && matches!(
                        self.tokens.get(self.pos + 1).map(|t| &t.token),
                        Some(Token::String(..))
                    ) =>
            {
                // Top-level test/describe: parse as expression (desugar triggers in parse_primary)
                let start = self.tokens[self.pos].span;
                let value = self.parse_expr(0)?;
                Ok(Decl::Let {
                    id: NodeId::fresh(),
                    name: "_".to_string(),
                    name_span: start,
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

        let mut fields = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let start = self.pos;
            let field_name = self.expect_ident()?;
            self.expect(Token::Colon)?;
            let field_type = self.parse_type_expr()?;
            let trailing_comment = self.take_trailing_comment(self.pos - 1);
            fields.push(Annotated {
                node: (field_name, field_type),
                leading_trivia: self.take_leading_trivia(start),
                trailing_comment,
                trailing_trivia: vec![],
            });
            if matches!(self.peek(), Token::Comma) {
                self.advance();
            }
        }

        let dangling_trivia = self.take_leading_trivia(self.pos);
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
            doc: vec![],
            public,
            name,
            name_span,
            type_params,
            fields,
            deriving,
            dangling_trivia,
            span: start.to(end),
        })
    }

    fn parse_type_def(&mut self, public: bool, opaque: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'type'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        let mut type_params = Vec::new();
        // Type params are lowercase identifiers before `=`
        while matches!(self.peek(), Token::Ident(_)) {
            type_params.push(self.expect_ident()?);
        }
        self.expect(Token::Eq)?;

        // Optional leading `|` before first variant
        let mut multiline = false;
        if matches!(self.peek(), Token::Bar) {
            if self.tokens[self.pos].preceded_by_newline {
                multiline = true;
            }
            self.advance();
        }

        let mut variants = Vec::new();
        let first_start = self.pos;
        let first = self.parse_type_constructor_def()?;
        let mut end = first.span;
        let trailing_comment = self.take_trailing_comment(self.pos - 1);
        variants.push(Annotated {
            node: first,
            leading_trivia: self.take_leading_trivia(first_start),
            trailing_comment,
            trailing_trivia: vec![],
        });

        while matches!(self.peek(), Token::Bar) {
            if self.tokens[self.pos].preceded_by_newline {
                multiline = true;
            }
            self.advance();
            let variant_start = self.pos;
            let variant = self.parse_type_constructor_def()?;
            end = variant.span;
            let trailing_comment = self.take_trailing_comment(self.pos - 1);
            variants.push(Annotated {
                node: variant,
                leading_trivia: self.take_leading_trivia(variant_start),
                trailing_comment,
                trailing_trivia: vec![],
            });
        }

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
            end = self.tokens[self.pos].span;
            self.expect(Token::RParen)?;
        }

        Ok(Decl::TypeDef {
            id: NodeId::fresh(),
            doc: vec![],
            public,
            opaque,
            name,
            name_span,
            type_params,
            variants,
            deriving,
            multiline,
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
    fn parse_fun_signature(
        &mut self,
        public: bool,
        start: Span,
        annotations: Vec<Annotation>,
    ) -> Result<Decl, ParseError> {
        self.advance(); // consume 'fun'
        let name = self.expect_ident()?;
        let name_span = self.tokens[self.pos - 1].span;

        self.expect(Token::Colon)?;
        let (params, return_type, effects, effect_row_var) = self.parse_annotated_signature()?;

        // Parse optional `where {a: Show + Eq, b: Ord}`
        let where_clause = self.parse_where_clause()?;

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::FunSignature {
            id: NodeId::fresh(),
            doc: vec![],
            public,
            name,
            name_span,
            params,
            return_type,
            effects,
            effect_row_var,
            where_clause,
            annotations,
            span: start.to(end),
        })
    }

    /// Parse one or more annotations: `@name` or `@name(arg1, arg2, ...)`
    fn parse_annotations(&mut self) -> Result<Vec<Annotation>, ParseError> {
        let mut annotations = Vec::new();
        while matches!(self.peek(), Token::At) {
            let start = self.tokens[self.pos].span;
            self.advance(); // consume '@'

            let name = self.expect_ident()?;
            let name_span = self.tokens[self.pos - 1].span;

            const KNOWN_ANNOTATIONS: &[&str] = &["external", "builtin"];
            if !KNOWN_ANNOTATIONS.contains(&name.as_str()) {
                return Err(ParseError {
                    message: format!("unknown annotation @{}", name),
                    span: name_span,
                });
            }

            let args = if matches!(self.peek(), Token::LParen) {
                self.advance(); // consume '('
                let mut args = Vec::new();
                while !matches!(self.peek(), Token::RParen) {
                    if !args.is_empty() {
                        self.expect(Token::Comma)?;
                    }
                    let lit = match self.advance() {
                        Token::String(s, kind) => Lit::String(s, kind),
                        Token::Int(s, n) => Lit::Int(s, n),
                        Token::Float(s, f) => Lit::Float(s, f),
                        Token::True => Lit::Bool(true),
                        Token::False => Lit::Bool(false),
                        tok => {
                            return Err(ParseError {
                                message: format!(
                                    "expected literal in annotation arguments, got {:?}",
                                    tok
                                ),
                                span: self.tokens[self.pos - 1].span,
                            });
                        }
                    };
                    args.push(lit);
                }
                self.expect(Token::RParen)?;
                args
            } else {
                vec![]
            };

            let end = self.tokens[self.pos - 1].span;
            annotations.push(Annotation {
                name,
                name_span,
                args,
                span: start.to(end),
            });
        }
        Ok(annotations)
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

        let mut operations = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let start = self.pos;
            let op_start = self.tokens[self.pos].span;
            self.expect(Token::Fun)?;
            let op_name = self.expect_ident()?;

            self.expect(Token::Colon)?;
            let (params, return_type, _effects, _effect_row_var) = self.parse_annotated_signature()?;
            let op_end = self.tokens[self.pos - 1].span;

            let trailing_comment = self.take_trailing_comment(self.pos - 1);
            operations.push(Annotated {
                node: EffectOp {
                    doc: vec![],
                    name: op_name,
                    params,
                    return_type,
                    span: op_start.to(op_end),
                },
                leading_trivia: self.take_leading_trivia(start),
                trailing_comment,
                trailing_trivia: vec![],
            });
        }

        let dangling_trivia = self.take_leading_trivia(self.pos);
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::EffectDef {
            id: NodeId::fresh(),
            doc: vec![],
            public,
            name,
            dangling_trivia,
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

        let where_clause = self.parse_where_clause()?;

        self.expect(Token::LBrace)?;

        let mut arms = Vec::new();
        let mut recovered_arms = Vec::new();
        let mut return_clause = None;

        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let arm_start_pos = self.pos;
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
                    let trailing_comment = self.take_trailing_comment(self.pos - 1);
                    arms.push(Annotated {
                        node: HandlerArm {
                            op_name,
                            params,
                            body: Box::new(body),
                            span: arm_start.to(arm_end),
                        },
                        leading_trivia: self.take_leading_trivia(arm_start_pos),
                        trailing_comment,
                        trailing_trivia: vec![],
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
                        Token::Eq | Token::RBrace | Token::Eof
                    ) {
                        let pspan = self.tokens[self.pos].span;
                        if let Ok(p) = self.expect_ident() {
                            params.push((p, pspan));
                        } else {
                            break;
                        }
                    }
                    let end = self.tokens[self.pos.saturating_sub(1)].span;
                    let trailing_comment = self.take_trailing_comment(self.pos.saturating_sub(1));
                    recovered_arms.push(Annotated {
                        node: HandlerArm {
                            op_name,
                            params,
                            body: Box::new(Expr {
                                id: NodeId::fresh(),
                                kind: ExprKind::Lit { value: Lit::Unit },
                                span: end,
                            }),
                            span: arm_start.to(end),
                        },
                        leading_trivia: self.take_leading_trivia(arm_start_pos),
                        trailing_comment,
                        trailing_trivia: vec![],
                    });
                }
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    self.advance();
                }
            }
        }

        let dangling_trivia = self.take_leading_trivia(self.pos);
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::HandlerDef {
            id: NodeId::fresh(),
            doc: vec![],
            public,
            name,
            name_span,
            effects,
            needs,
            where_clause,
            arms,
            recovered_arms,
            return_clause,
            dangling_trivia,
            span: start.to(end),
        })
    }

    fn parse_trait_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'trait'
        let name_span = self.tokens[self.pos].span;
        let name = self.expect_upper_ident()?;
        // Parse type parameters: first is self, rest are extras
        // e.g. `trait ConvertTo a b` -> type_params = ["a", "b"]
        let mut type_params = vec![self.expect_ident()?];
        while matches!(self.peek(), Token::Ident(_))
            && !matches!(self.peek(), Token::Where)
        {
            type_params.push(self.expect_ident()?);
        }

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

        let mut methods = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let start_pos = self.pos;
            let method_start = self.tokens[self.pos].span;
            self.expect(Token::Fun)?;
            let method_name = self.expect_ident()?;

            self.expect(Token::Colon)?;
            let (params, return_type, _effects, _effect_row_var) = self.parse_annotated_signature()?;
            let method_end = self.tokens[self.pos - 1].span;

            let trailing_comment = self.take_trailing_comment(self.pos - 1);
            methods.push(Annotated {
                node: TraitMethod {
                    doc: vec![],
                    name: method_name,
                    params,
                    return_type,
                    span: method_start.to(method_end),
                },
                leading_trivia: self.take_leading_trivia(start_pos),
                trailing_comment,
                trailing_trivia: vec![],
            });
        }

        let dangling_trivia = self.take_leading_trivia(self.pos);
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::TraitDef {
            id: NodeId::fresh(),
            doc: vec![],
            public,
            name,
            name_span,
            type_params,
            supertraits,
            methods,
            dangling_trivia,
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
            // Parse optional type args after trait name: `ConvertTo b` in `a: ConvertTo b`
            // Stop at `+` (next trait), `,` (next bound), `}` (end of clause)
            let mut type_args = Vec::new();
            while matches!(self.peek(), Token::Ident(_))
                && !matches!(self.peek(), Token::Plus | Token::Comma | Token::RBrace)
            {
                type_args.push(self.expect_ident()?);
            }
            let mut traits = vec![(name, type_args, span)];
            while *self.peek() == Token::Plus {
                self.advance();
                let name = self.parse_upper_name()?;
                let span = self.tokens[self.pos - 1].span;
                let mut type_args = Vec::new();
                while matches!(self.peek(), Token::Ident(_))
                    && !matches!(self.peek(), Token::Plus | Token::Comma | Token::RBrace)
                {
                    type_args.push(self.expect_ident()?);
                }
                traits.push((name, type_args, span));
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

        // Parse optional trait type args: `impl ConvertTo NOK for USD`
        // These are uppercase names (concrete types) or lowercase (type vars) before `for`
        let mut trait_type_args = Vec::new();
        while !matches!(self.peek(), Token::For) {
            match self.peek() {
                Token::UpperIdent(_) => {
                    trait_type_args.push(self.parse_upper_name()?);
                }
                Token::Ident(_) => {
                    trait_type_args.push(self.expect_ident()?);
                }
                _ => break,
            }
        }

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

        let mut methods = Vec::new();
        while !matches!(self.peek(), Token::RBrace | Token::Eof) {
            let start_pos = self.pos;
            let name = self.expect_ident()?;
            let name_span = self.tokens[self.pos - 1].span;
            let mut params = Vec::new();
            while !matches!(self.peek(), Token::Eq | Token::Eof) {
                params.push(self.parse_pattern()?);
            }

            self.expect(Token::Eq)?;
            let body = self.parse_expr(0)?;
            let trailing_comment = self.take_trailing_comment(self.pos - 1);
            methods.push(Annotated {
                node: ImplMethod { name, name_span, params, body },
                leading_trivia: self.take_leading_trivia(start_pos),
                trailing_comment,
                trailing_trivia: vec![],
            });
        }

        let dangling_trivia = self.take_leading_trivia(self.pos);
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::ImplDef {
            id: NodeId::fresh(),
            doc: vec![],
            trait_name,
            trait_name_span,
            trait_type_args,
            target_type,
            target_type_span,
            type_params,
            where_clause,
            needs,
            methods,
            dangling_trivia,
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
        let mut effect_row_var = None;
        if matches!(self.peek(), Token::Needs) {
            self.advance();
            self.expect(Token::LBrace)?;
            while !matches!(self.peek(), Token::RBrace) {
                // Check for row variable: `..e`
                if matches!(self.peek(), Token::DotDot) {
                    let dot_span = self.tokens[self.pos].span;
                    self.advance(); // consume '..'
                    let name = self.expect_ident()?;
                    let end_span = self.tokens[self.pos - 1].span;
                    effect_row_var = Some((name, dot_span.to(end_span)));
                    // optional trailing comma
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                    break;
                }
                effects.push(self.parse_effect_ref()?);
                if matches!(self.peek(), Token::Comma) {
                    self.advance();
                }
            }
            self.expect(Token::RBrace)?;
        }

        if segments.len() < 2 {
            // No arrow at all, e.g. `fun x : Int` -- just a constant annotation
            let (_label, ty) = segments.pop().unwrap();
            return Ok((vec![], ty, effects, effect_row_var));
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

        Ok((params, return_type, effects, effect_row_var))
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
        // Stop at line boundaries to avoid consuming the next declaration.
        let seg_start = self.tokens[self.pos].span;
        let mut left = self.parse_type_atom()?;
        while self.can_start_type_atom() && !self.next_on_new_line() {
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
        // Stop at line boundaries to avoid consuming the next declaration.
        let mut left = self.parse_type_atom()?;
        while self.can_start_type_atom() && !self.next_on_new_line() {
            let arg = self.parse_type_atom()?;
            let span = start.to(arg.span());
            left = TypeExpr::App { func: Box::new(left), arg: Box::new(arg), span };
        }

        // Then: check for arrow (right-associative)
        if matches!(self.peek(), Token::Arrow) {
            self.advance();
            let right = self.parse_type_expr()?; // recurse = right-associative
            let mut needs = Vec::new();
            let mut row_var = None;
            if matches!(self.peek(), Token::Needs) {
                self.advance();
                self.expect(Token::LBrace)?;
                while !matches!(self.peek(), Token::RBrace) {
                    if matches!(self.peek(), Token::DotDot) {
                        let dot_span = self.tokens[self.pos].span;
                        self.advance();
                        let name = self.expect_ident()?;
                        let end_span = self.tokens[self.pos - 1].span;
                        row_var = Some((name, dot_span.to(end_span)));
                        if matches!(self.peek(), Token::Comma) {
                            self.advance();
                        }
                        break;
                    }
                    needs.push(self.parse_effect_ref()?);
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                }
                self.expect(Token::RBrace)?;
            }
            let end = self.tokens[self.pos - 1].span;
            let span = start.to(end);
            Ok(TypeExpr::Arrow { from: Box::new(left), to: Box::new(right), effects: needs, effect_row_var: row_var, span })
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
                                let mut fields = Vec::new();
                while !matches!(self.peek(), Token::RBrace | Token::Eof) {
                    let field_name = self.expect_ident()?;
                    self.expect(Token::Colon)?;
                    let field_type = self.parse_type_expr()?;
                    fields.push((field_name, field_type));
                                        if matches!(self.peek(), Token::RBrace) {
                        // last field, no trailing comma needed
                    } else {
                        self.expect(Token::Comma)?;
                                            }
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
