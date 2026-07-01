use crate::ast::*;
use crate::token::{Span, Spanned, Token, Trivia};

mod decl;
mod expr;
mod pat;

/// Split a trivia list at the first BlankLines entry.
///
/// Returns (before_blank, blank_and_after):
///   - `before_blank`: comments that precede the first blank line (trailing on previous node)
///   - `blank_and_after`: the blank line + everything after (leading on next node)
///
/// If there's no BlankLines, everything goes into `before_blank` (all comments are trailing).
pub(super) fn split_trivia_at_blank_line(trivia: Vec<Trivia>) -> (Vec<Trivia>, Vec<Trivia>) {
    if let Some(pos) = trivia
        .iter()
        .position(|t| matches!(t, Trivia::BlankLines(_)))
    {
        let mut before = trivia;
        let after = before.split_off(pos);
        (before, after)
    } else {
        (trivia, vec![])
    }
}

/// Snapshot of parser state for speculative parsing with backtracking.
/// Captures position and all token trivia so destructive trivia operations
/// can be undone on restore.
pub(super) struct ParserSnapshot {
    pos: usize,
    trivia: Vec<(Vec<Trivia>, Option<String>)>,
}

pub struct Parser {
    pub(super) tokens: Vec<Spanned>,
    pub(super) pos: usize,
    /// When true, `{` is not treated as starting a function argument.
    /// Used when parsing case scrutinees where `{` begins the branch block.
    pub(super) no_brace_app: bool,
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl Parser {
    // --- Helpers ---

    pub fn new(tokens: Vec<Spanned>) -> Self {
        Parser {
            tokens,
            pos: 0,
            no_brace_app: false,
        }
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

    pub(super) fn expect_upper_ident(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::UpperIdent(s) => Ok(s),
            tok => Err(ParseError {
                message: format!("expected type, got {:?}", tok),
                span: self.tokens[self.pos - 1].span,
            }),
        }
    }

    /// Save parser state for speculative parsing. The returned snapshot
    /// captures the current position and a clone of all token trivia, so
    /// that `restore` can undo any destructive `take_leading_trivia` /
    /// `take_trailing_comment` calls made during the speculative parse.
    pub(super) fn save(&self) -> ParserSnapshot {
        ParserSnapshot {
            pos: self.pos,
            trivia: self
                .tokens
                .iter()
                .map(|t| (t.leading_trivia.clone(), t.trailing_comment.clone()))
                .collect(),
        }
    }

    /// Restore parser state from a snapshot, undoing any position and trivia
    /// changes made since `save()`.
    pub(super) fn restore(&mut self, snapshot: ParserSnapshot) {
        self.pos = snapshot.pos;
        for (i, (leading, trailing)) in snapshot.trivia.into_iter().enumerate() {
            self.tokens[i].leading_trivia = leading;
            self.tokens[i].trailing_comment = trailing;
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

    /// Steal trailing trivia from the next token's leading trivia.
    /// Comments before the first blank line are taken and returned;
    /// the blank line + remaining trivia stays on the token.
    pub(super) fn steal_trailing_trivia(&mut self) -> Vec<Trivia> {
        let leading = std::mem::take(&mut self.tokens[self.pos].leading_trivia);
        let (stolen, remaining) = split_trivia_at_blank_line(leading);
        self.tokens[self.pos].leading_trivia = remaining;
        stolen
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
            Token::Int(..)
                | Token::Float(..)
                | Token::String(..)
                | Token::InterpolatedString(..)
                | Token::True
                | Token::False
                | Token::Ident(_)
                | Token::UpperIdent(_)
                | Token::LParen
                | Token::LBracket
                | Token::EffectCall(_)
                | Token::Resume
                | Token::Do
                | Token::ComposeBack
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
    ///
    /// After parsing each declaration, the next token's leading trivia is split at the
    /// first blank line: comments before the blank line are trailing trivia on the previous
    /// declaration (they're visually associated with it), and the blank line + everything
    /// after becomes leading trivia on the next declaration.
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
                trailing_trivia: vec![],
            });
        }

        // Split trivia between declarations: comments before the first blank line
        // belong to the previous declaration as trailing_trivia.
        let eof_trivia = self.take_leading_trivia(self.pos);
        self.split_inter_decl_trivia(decls, eof_trivia)
    }

    /// Split leading trivia on each declaration: comments before the first BlankLines
    /// become trailing_trivia on the *previous* declaration. This handles the common
    /// pattern where comments immediately following a declaration (no blank line) are
    /// about that declaration, while a blank line starts a new "paragraph".
    ///
    /// TODO: Now that expression parsers (e.g. pipe) steal their own trailing trivia
    /// via `steal_trailing_trivia`, check whether this program-level pass is still
    /// needed or if it's redundant. It may still be needed for non-expression trailing
    /// comments (e.g. comments after a type def or handler def).
    fn split_inter_decl_trivia(
        &self,
        mut decls: Vec<Annotated<Decl>>,
        eof_trivia: Vec<Trivia>,
    ) -> Result<AnnotatedProgram, ParseError> {
        // Process declarations in reverse order so we can split trivia from
        // each declaration's leading and push it to the previous one's trailing.
        // We also need to handle EOF trivia the same way.
        // Split the EOF/final trivia: comments before first blank line go to last decl
        let (mut trailing_trivia_for_last, next_leading) = split_trivia_at_blank_line(eof_trivia);

        let final_trailing = next_leading; // what remains is true EOF trailing trivia

        // Now process declarations from last to first
        for i in (0..decls.len()).rev() {
            decls[i].trailing_trivia = trailing_trivia_for_last;

            // Split this declaration's own leading trivia
            let leading = std::mem::take(&mut decls[i].leading_trivia);
            let (before, after) = split_trivia_at_blank_line(leading);
            trailing_trivia_for_last = before;
            decls[i].leading_trivia = after;
        }

        // If there's still trailing_trivia_for_last but no previous decl,
        // it becomes leading trivia on the first decl (file-level comments)
        if !trailing_trivia_for_last.is_empty()
            && let Some(first) = decls.first_mut()
        {
            let mut combined = trailing_trivia_for_last;
            combined.append(&mut first.leading_trivia);
            first.leading_trivia = combined;
        }

        Ok(AnnotatedProgram {
            declarations: decls,
            trailing_trivia: final_trailing,
        })
    }
}

#[cfg(test)]
mod tests;
