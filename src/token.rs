#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    Int(i64),
    Float(f64),
    String(String),
    /// `$"hello {name}"` -- pre-tokenized interpolated string
    InterpolatedString(Vec<InterpPart>),

    // Identifiers
    Ident(String),
    UpperIdent(String),

    // Keywords
    True,
    False,
    Let,
    Type,
    Case,
    If,
    Then,
    Else,
    Fun,
    Pub,
    Opaque,
    Record,
    Effect,
    Handler,
    With,
    Where,
    Import,
    Module,
    As,
    Trait,
    Impl,
    Return,
    Resume,
    Needs,
    For,
    Do,
    Deriving,
    Receive,
    After,
    EffectCall(String),

    // Operators
    Plus,           // +
    Minus,          // -
    Star,           // *
    Slash,          // /
    Modulo,         // %
    Eq,             // =
    EqEq,           // ==
    NotEq,          // !=
    Lt,             // <
    Gt,             // >
    LtEq,           // <=
    GtEq,           // >=
    Arrow,          // ->
    LeftArrow,      // <-
    Pipe,           // |>
    PipeBack,       // <|
    Concat,         // <>
    ComposeForward, // >>
    ComposeBack,    // <<
    And,            // &&
    Or,             // ||
    Dot,            // .
    DotDot,         // ..
    Backslash,      // \
    Bar,            // |
    DoubleColon,    // ::

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
    Comma,    // ,
    Colon,    // :

    // Annotations
    At, // @

    // End of file
    Eof,
}

/// Byte offset span in source code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    /// Extend this span to cover up to the end of `other`.
    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start,
            end: other.end,
        }
    }
}

/// A segment of an interpolated string.
#[derive(Debug, Clone, PartialEq)]
pub enum InterpPart {
    /// Literal text between holes.
    Literal(String),
    /// `{expr}` -- pre-tokenized expression tokens (without surrounding braces).
    Hole(Vec<Spanned>),
}

/// A piece of trivia (comment or blank line) attached to a token.
#[derive(Debug, Clone, PartialEq)]
pub enum Trivia {
    BlankLines(u32),
    Comment(String),
    DocComment(String),
}

/// A token tagged with its location in source and attached trivia.
#[derive(Debug, Clone)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
    /// Trivia (blank lines, comments) appearing before this token.
    pub leading_trivia: Vec<Trivia>,
    /// A same-line comment appearing after this token (at most one).
    pub trailing_comment: Option<String>,
    /// True if there was a newline between the previous token and this one,
    /// at top-level nesting (outside parens/brackets). Used by the parser
    /// to stop greedy parsing (e.g. type application) at line boundaries.
    pub preceded_by_newline: bool,
}

impl PartialEq for Spanned {
    fn eq(&self, other: &Self) -> bool {
        self.token == other.token && self.span == other.span
    }
}
