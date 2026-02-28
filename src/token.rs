#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    Int(i64),
    Float(f64),
    String(String),

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
    Record,
    Effect,
    Handler,
    With,
    Where,
    Import,
    Module,
    Trait,
    Impl,
    Return,
    Resume,

    // Operators
    Plus,      // +
    Minus,     // -
    Star,      // *
    Slash,     // /
    Modulo,    // %
    Eq,        // =
    EqEq,      // ==
    NotEq,     // !=
    Lt,        // <
    Gt,        // >
    LtEq,      // <=
    GtEq,      // >=
    Arrow,     // ->
    ArrowBack, // <-
    Pipe,      // |>
    PipeBack,  // <|
    Concat,    // <>
    And,       // &&
    Or,        // ||
    Dot,       // .
    DotDot,    // ..
    Backslash, // \
    Bar,       // |

    // Delimiters
    LParen, // (
    RParen, // )
    LBrace, // {
    RBrace, // }
    Comma,  // ,
    Colon,  // :

    // End of statement/line
    Terminator,

    // End of file
    Eof,
}

/// Byte offset span in source code
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// A token tagged with its location in source
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
}
