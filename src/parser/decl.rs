use crate::ast::*;
use crate::token::{Span, Token};

use super::{ParseError, Parser};

impl Parser {
    // Parse `Name` or `Module.Name`, returning the full qualified string.
    // Used where we want to preserve the qualification (e.g. needs lists).
    fn parse_effect_ref(&mut self) -> Result<EffectRef, ParseError> {
        let name = self.expect_upper_ident()?;
        let name = if matches!(self.peek(), Token::Dot) {
            self.advance(); // consume '.'
            let qualifier = self.expect_upper_ident()?;
            format!("{}.{}", name, qualifier)
        } else {
            name
        };
        let mut type_args = Vec::new();
        while self.can_start_type_atom() {
            type_args.push(self.parse_type_atom()?);
        }
        Ok(EffectRef { name, type_args })
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
                    span: start.to(value.span()),
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
            Token::Ident(_) => self.parse_fun_binding(),
            _ => Err(ParseError {
                message: format!("Expected declaration, got {:?}", self.peek()),
                span: self.tokens[self.pos].span,
            }),
        }
    }

    // Parses: record <Name> { <field>: <Type>, ... }
    fn parse_record_def(&mut self, public: bool) -> Result<Decl, ParseError> {
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
            public,
            name,
            fields,
            span: start.to(end),
        })
    }

    fn parse_type_def(&mut self, public: bool, opaque: bool) -> Result<Decl, ParseError> {
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
            if matches!(self.peek(), Token::Bar) {
                self.advance(); // skip optional `|` separator
            }
            variants.push(self.parse_type_constructor_def()?);
            self.skip_terminators();
        }
        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::TypeDef {
            public,
            opaque,
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

    // Parses: [pub] fun <name> (<p>: <Type>) ... -> <ReturnType> [needs {Effect, ...}]
    fn parse_fun_annotation(&mut self, public: bool, start: Span) -> Result<Decl, ParseError> {
        self.advance(); // consume 'fun'
        let name = self.expect_ident()?;

        let mut params = Vec::new();
        while matches!(self.peek(), Token::LParen) {
            self.advance(); // consume '('
            if matches!(self.peek(), Token::RParen) {
                // `()` -- unit parameter
                self.advance(); // consume ')'
                params.push(("_".into(), TypeExpr::Named("Unit".into())));
            } else {
                let param_name = self.expect_ident()?;
                self.expect(Token::Colon)?;
                let param_type = self.parse_type_expr()?;
                self.expect(Token::RParen)?;
                params.push((param_name, param_type));
            }
        }

        self.expect(Token::Arrow)?;
        let return_type = self.parse_type_expr()?;

        let mut effects = Vec::new();
        if matches!(self.peek(), Token::Needs) {
            self.advance(); // consume 'needs'
            self.expect(Token::LBrace)?;
            effects.push(self.parse_effect_ref()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                effects.push(self.parse_effect_ref()?);
            }
            self.expect(Token::RBrace)?;
        }

        // Parse optional `where {a: Show + Eq, b: Ord}`
        let where_clause = self.parse_where_clause()?;

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::FunAnnotation {
            public,
            name,
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

        let mut params = Vec::new();
        while matches!(self.peek(), Token::LParen) {
            self.advance(); // consume '('
            if matches!(self.peek(), Token::RParen) {
                // `()` -- unit parameter
                self.advance(); // consume ')'
                params.push(("_".into(), TypeExpr::Named("Unit".into())));
            } else {
                let param_name = self.expect_ident()?;
                self.expect(Token::Colon)?;
                let param_type = self.parse_type_expr()?;
                self.expect(Token::RParen)?;
                params.push((param_name, param_type));
            }
        }

        self.expect(Token::Arrow)?;
        let return_type = self.parse_type_expr()?;

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

        let where_clause = self.parse_where_clause()?;

        let end = self.tokens[self.pos - 1].span;
        Ok(Decl::ExternalFun {
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

            let mut params = Vec::new();
            // Allow zero-param ops: `fun get () -> Int`
            if matches!(self.peek(), Token::LParen) && matches!(self.peek_at(1), Token::RParen) {
                self.advance(); // consume '('
                self.advance(); // consume ')'
            } else {
                while matches!(self.peek(), Token::LParen) {
                    self.advance();
                    let param_name = self.expect_ident()?;
                    self.expect(Token::Colon)?;
                    let param_type = self.parse_type_expr()?;
                    self.expect(Token::RParen)?;
                    params.push((param_name, param_type));
                }
            }

            self.expect(Token::Arrow)?;
            let return_type = self.parse_type_expr()?;
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
            public,
            name,
            type_params,
            operations,
            span: start.to(end),
        })
    }

    // Parses: handler <name> for <Effect>, ... { <op> <params> -> <body> ... }
    fn parse_handler_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'handler'
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
                let op_name = self.expect_ident()?;
                let mut params = Vec::new();
                while !matches!(self.peek(), Token::Arrow | Token::Eof) {
                    // Skip `()` unit params (zero-param effect ops)
                    if matches!(self.peek(), Token::LParen)
                        && matches!(self.peek_at(1), Token::RParen)
                    {
                        self.advance(); // consume '('
                        self.advance(); // consume ')'
                        continue;
                    }
                    params.push(self.expect_ident()?);
                }
                self.expect(Token::Arrow)?;
                let body = self.parse_expr(0)?;
                let arm_end = body.span();
                arms.push(HandlerArm {
                    op_name,
                    params,
                    body: Box::new(body),
                    span: arm_start.to(arm_end),
                });
            }

            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::HandlerDef {
            public,
            name,
            effects,
            needs,
            arms,
            return_clause,
            span: start.to(end),
        })
    }

    fn parse_trait_def(&mut self, public: bool) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'trait'
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
                supertraits.push(self.parse_upper_name()?);

                while *self.peek() == Token::Plus {
                    self.advance();
                    supertraits.push(self.parse_upper_name()?);
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

            let mut params = Vec::new();
            while matches!(self.peek(), Token::LParen) {
                self.advance();
                if matches!(self.peek(), Token::RParen) {
                    self.advance();
                    params.push(("_".into(), TypeExpr::Named("Unit".into())));
                } else {
                    let param_name = self.expect_ident()?;
                    self.expect(Token::Colon)?;
                    let param_type = self.parse_type_expr()?;
                    self.expect(Token::RParen)?;
                    params.push((param_name, param_type));
                }
            }

            self.expect(Token::Arrow)?;
            let return_type = self.parse_type_expr()?;
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
            public,
            name,
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
            let mut traits = vec![self.parse_upper_name()?];
            while *self.peek() == Token::Plus {
                self.advance();
                traits.push(self.parse_upper_name()?);
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
        self.expect(Token::For)?;
        let target_type = self.parse_upper_name()?;

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
            let mut params = Vec::new();
            while !matches!(self.peek(), Token::Eq | Token::Eof) {
                params.push(self.parse_pattern()?);
            }

            self.expect(Token::Eq)?;
            let body = self.parse_expr(0)?;
            methods.push((name, params, body));
            self.skip_terminators();
        }

        let end = self.tokens[self.pos].span;
        self.expect(Token::RBrace)?;

        Ok(Decl::ImplDef {
            trait_name,
            target_type,
            type_params,
            where_clause,
            needs,
            methods,
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

    pub(super) fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
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
            Ok(TypeExpr::Arrow(Box::new(left), Box::new(right), needs))
        } else {
            Ok(left)
        }
    }

    fn parse_type_atom(&mut self) -> Result<TypeExpr, ParseError> {
        match self.advance() {
            Token::UpperIdent(s) => {
                // Support qualified type names: `Module.Type`
                if matches!(self.peek(), Token::Dot) {
                    self.advance(); // consume '.'
                    let name = self.expect_upper_ident()?;
                    Ok(TypeExpr::Named(format!("{}.{}", s, name)))
                } else {
                    Ok(TypeExpr::Named(s))
                }
            }
            Token::Ident(s) => Ok(TypeExpr::Var(s)),
            Token::LParen => {
                // () is the Unit type
                if matches!(self.peek(), Token::RParen) {
                    self.advance();
                    return Ok(TypeExpr::Named("Unit".to_string()));
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
                    self.expect(Token::RParen)?;
                    let mut result = TypeExpr::Named("Tuple".into());
                    for elem in elements {
                        result = TypeExpr::App(Box::new(result), Box::new(elem));
                    }
                    Ok(result)
                } else {
                    self.expect(Token::RParen)?;
                    Ok(first)
                }
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
            module_path,
            alias,
            exposing: exposing.map(|(items, _)| items),
            span: start.to(end),
        })
    }
}
