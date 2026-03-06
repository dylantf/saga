use crate::ast::*;
use crate::token::{Span, Token};

use super::{ParseError, Parser};

impl Parser {
    // --- Declarations ---

    pub(super) fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        match self.peek() {
            Token::Type => self.parse_type_def(),
            Token::Record => self.parse_record_def(),
            Token::Let => {
                let start = self.tokens[self.pos].span;
                self.advance(); // consume 'let'
                let mutable = matches!(self.peek(), Token::Mut);
                if mutable {
                    self.advance(); // consume 'mut'
                }
                let name = self.expect_ident()?;
                self.expect(Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Decl::Let {
                    span: start.to(value.span()),
                    name,
                    value,
                    mutable,
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
            Token::Effect => self.parse_effect_def(),
            Token::Handler => self.parse_handler_def(),
            Token::Trait => self.parse_trait_def(),
            Token::Impl => self.parse_impl_def(),
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
            if matches!(self.peek(), Token::Bar) {
                self.advance(); // skip optional `|` separator
            }
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
            effects.push(self.expect_upper_ident()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                effects.push(self.expect_upper_ident()?);
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

    // Parses: effect <Name> { fun <op> (<p>: <T>) ... -> <T> ... }
    fn parse_effect_def(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'effect'
        let name = self.expect_upper_ident()?;
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
            name,
            operations,
            span: start.to(end),
        })
    }

    // Parses: handler <name> for <Effect>, ... { <op> <params> -> <body> ... }
    fn parse_handler_def(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume 'handler'
        let name = self.expect_ident()?;
        self.expect(Token::For)?;

        let mut effects = vec![self.expect_upper_ident()?];
        while matches!(self.peek(), Token::Comma) {
            self.advance();
            effects.push(self.expect_upper_ident()?);
        }

        let mut needs = Vec::new();
        if matches!(self.peek(), Token::Needs) {
            self.advance(); // consume 'needs'
            self.expect(Token::LBrace)?;
            needs.push(self.expect_upper_ident()?);
            while matches!(self.peek(), Token::Comma) {
                self.advance();
                if matches!(self.peek(), Token::RBrace) {
                    break; // trailing comma
                }
                needs.push(self.expect_upper_ident()?);
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
            name,
            effects,
            needs,
            arms,
            return_clause,
            span: start.to(end),
        })
    }

    fn parse_trait_def(&mut self) -> Result<Decl, ParseError> {
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
                supertraits.push(self.expect_upper_ident()?);

                while *self.peek() == Token::Plus {
                    self.advance();
                    supertraits.push(self.expect_upper_ident()?);
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
            let mut traits = vec![self.expect_upper_ident()?];
            while *self.peek() == Token::Plus {
                self.advance();
                traits.push(self.expect_upper_ident()?);
            }
            bounds.push(crate::ast::TraitBound { type_var, traits });
        }
        self.expect(Token::RBrace)?;
        Ok(bounds)
    }

    fn parse_impl_def(&mut self) -> Result<Decl, ParseError> {
        let start = self.tokens[self.pos].span;
        self.advance(); // consume impl

        let trait_name = self.expect_upper_ident()?;
        self.expect(Token::For)?;
        let target_type = self.expect_upper_ident()?;

        // Parse optional type params: `impl Show for Box a b`
        let mut type_params = Vec::new();
        while matches!(self.peek(), Token::Ident(_)) {
            type_params.push(self.expect_ident()?);
        }

        let where_clause = self.parse_where_clause()?;

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
            let arrow = TypeExpr::Arrow(Box::new(left), Box::new(right));
            // Consume optional `needs { Effect1, Effect2 }` (ignored until type checker)
            if matches!(self.peek(), Token::Needs) {
                self.advance();
                self.expect(Token::LBrace)?;
                while !matches!(self.peek(), Token::RBrace) {
                    self.advance(); // consume effect name
                    if matches!(self.peek(), Token::Comma) {
                        self.advance();
                    }
                }
                self.expect(Token::RBrace)?;
            }
            Ok(arrow)
        } else {
            Ok(left)
        }
    }

    fn parse_type_atom(&mut self) -> Result<TypeExpr, ParseError> {
        match self.advance() {
            Token::UpperIdent(s) => Ok(TypeExpr::Named(s)),
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
}
