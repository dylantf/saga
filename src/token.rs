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

    // Comments
    Comment(String),    // # regular comment
    DocComment(String), // #@ doc comment

    // End of statement/line
    Terminator,
    /// An empty line in the source (consecutive newline after a Terminator/Comment/BlankLine)
    BlankLine,

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

/// A token tagged with its location in source
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
}
