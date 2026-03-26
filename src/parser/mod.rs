use crate::ast::*;
use crate::token::{Span, Spanned, Token};

mod decl;
mod expr;
mod pat;

pub struct Parser {
    pub(super) tokens: Vec<Spanned>,
    pub(super) pos: usize,
    /// When true, `{` is not treated as starting a function argument.
    /// Used when parsing case scrutinees where `{` begins the branch block.
    pub(super) no_brace_app: bool,
    /// When true, `test`, `describe`, and `skip` followed by a string literal
    /// are desugared into function calls. Only enabled for test files.
    pub test_mode: bool,
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl Parser {
    // --- Helpers ---

    pub fn new(tokens: Vec<Spanned>) -> Self {
        Parser { tokens, pos: 0, no_brace_app: false, test_mode: false }
    }

    /// Allocate a fresh NodeId from the global counter.
    pub(super) fn next_id(&mut self) -> NodeId {
        NodeId::fresh()
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

    pub(super) fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].token.clone();
        self.pos += 1;
        tok
    }

    pub(super) fn expect(&mut self, expected: Token) -> Result<(), ParseError> {
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

    pub(super) fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::Ident(s) => Ok(s),
            tok => Err(ParseError {
                message: format!("expected identifier, got {:?}", tok),
                span: self.tokens[self.pos - 1].span,
            }),
        }
    }

    pub(super) fn expect_string(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::String(s) => Ok(s),
            tok => Err(ParseError {
                message: format!("expected string literal, got {:?}", tok),
                span: self.tokens[self.pos - 1].span,
            }),
        }
    }

    pub(super) fn expect_upper_ident(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::UpperIdent(s) => Ok(s),
            tok => Err(ParseError {
                message: format!("expected type, got {:?}", tok),
                span: self.tokens[self.pos - 1].span,
            }),
        }
    }

    /// Take the leading trivia from the token at the given position.
    pub(super) fn take_leading_trivia(&mut self, pos: usize) -> Vec<Trivia> {
        std::mem::take(&mut self.tokens[pos].leading_trivia)
    }

    /// Take the trailing comment from the token at the given position.
    pub(super) fn take_trailing_comment(&mut self, pos: usize) -> Option<String> {
        self.tokens[pos].trailing_comment.take()
    }

    /// Check if the next token is on a new line (at top-level nesting).
    /// Used to stop greedy parsing at line boundaries.
    pub(super) fn next_on_new_line(&self) -> bool {
        self.tokens[self.pos].preceded_by_newline
    }

    // Determines whether the next token can start a primary expression.
    // Used by parse_application to know when to keep consuming arguments.
    pub(super) fn can_start_primary(&self) -> bool {
        matches!(
            self.peek(),
            Token::Int(_)
                | Token::Float(_)
                | Token::String(_)
                | Token::InterpolatedString(_)
                | Token::True
                | Token::False
                | Token::Ident(_)
                | Token::UpperIdent(_)
                | Token::LParen
                | Token::LBracket
                | Token::EffectCall(_)
                | Token::Resume
                | Token::Do
        ) || (!self.no_brace_app && matches!(self.peek(), Token::LBrace))
    }

    pub(super) fn can_start_type_atom(&self) -> bool {
        matches!(
            self.peek(),
            Token::UpperIdent(_) | Token::Ident(_) | Token::LParen | Token::LBrace
        )
    }

    /// Like can_start_type_atom but excludes LBrace.
    /// Used in effect ref parsing where `{` starts the handler body, not a type.
    pub(super) fn can_start_type_atom_no_brace(&self) -> bool {
        matches!(
            self.peek(),
            Token::UpperIdent(_) | Token::Ident(_) | Token::LParen
        )
    }

    // --- Program ---

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let annotated = self.parse_program_annotated()?;
        Ok(strip_annotations(annotated))
    }

    /// Parse a program, preserving comments and blank lines as trivia on each declaration.
    pub fn parse_program_annotated(&mut self) -> Result<AnnotatedProgram, ParseError> {
        let mut decls = Vec::new();
        while !matches!(self.peek(), Token::Eof) {
            let start = self.pos;
            let decl = self.parse_decl()?;
            let leading = self.take_leading_trivia(start);
            let trailing = self.take_trailing_comment(self.pos - 1);
            decls.push(Annotated {
                node: decl,
                leading_trivia: leading,
                trailing_comment: trailing,
            });
        }
        // EOF token's leading trivia = comments at end of file
        let trailing = self.take_leading_trivia(self.pos);
        Ok(AnnotatedProgram {
            declarations: decls,
            trailing_trivia: trailing,
        })
    }
}

#[cfg(test)]
mod tests;
