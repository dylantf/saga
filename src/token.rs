#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals (source text, parsed value)
    Int(String, i64),
    Float(String, f64),
    String(String, StringKind),
    /// `$"hello {name}"` -- pre-tokenized interpolated string
    InterpolatedString(Vec<InterpPart>, StringKind),

    // Identifiers
    Ident(String),
    UpperIdent(String),

    // Keywords
    True,
    False,
    Let,
    Val,
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
    When,
    Finally,
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

/// Distinguishes the syntactic form of a string literal so the formatter can
/// round-trip the original delimiters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringKind {
    /// `"..."`
    Normal,
    /// `"""..."""`
    Multiline,
    /// `@"..."`
    Raw,
    /// `@"""..."""`
    RawMultiline,
    /// `$"..."`
    Interpolated,
    /// `$"""..."""`
    InterpolatedMultiline,
}

impl StringKind {
    /// True for triple-quoted variants that use `"""` delimiters.
    pub fn is_multiline(self) -> bool {
        matches!(self, StringKind::Multiline | StringKind::RawMultiline | StringKind::InterpolatedMultiline)
    }
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
