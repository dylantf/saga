use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::lower::util::lower_string_to_binary;
use crate::token::Span;

/// Maps byte offsets to 1-based line numbers.
/// Simpler than the LSP LineIndex — we only need line numbers, not columns.
pub struct LineNumbers {
    /// Byte offset of the start of each line.
    line_starts: Vec<usize>,
}

impl LineNumbers {
    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        LineNumbers { line_starts }
    }

    /// Convert a byte offset to a 1-based line number.
    pub fn line_number(&self, offset: usize) -> usize {
        self.line_starts
            .partition_point(|&start| start <= offset)
            .max(1)
    }
}

/// The kind of error for structured error terms.
#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    Panic,
    Todo,
    AssertFail,
}

impl ErrorKind {
    pub fn as_atom(&self) -> &'static str {
        match self {
            ErrorKind::Panic => "panic",
            ErrorKind::Todo => "todo",
            ErrorKind::AssertFail => "assert_fail",
        }
    }
}

/// Source location info threaded into the lowerer.
pub struct SourceInfo {
    /// Relative path to the source file (e.g. "src/server.dy").
    pub file: String,
    /// Source text, kept for line number conversion.
    pub line_numbers: LineNumbers,
}

impl SourceInfo {
    pub fn new(file: String, source: &str) -> Self {
        SourceInfo {
            file,
            line_numbers: LineNumbers::new(source),
        }
    }

    pub fn line_number(&self, span: &Span) -> usize {
        self.line_numbers.line_number(span.start)
    }
}

/// Structured error term for dylang runtime errors.
///
/// Lowered to: `{dylang_error, Kind, Message, Module, Function, File, Line}`
///
/// All fields are atoms/binaries/integers so the runtime can pattern-match
/// without needing Erlang map support in Core Erlang.
pub struct ErrorInfo {
    pub kind: ErrorKind,
    /// The error message as a binary string.
    pub message: CExpr,
    /// Source module name (e.g. "MyApp.Server").
    pub module: String,
    /// Source function name (e.g. "handle_request").
    pub function: String,
    /// Source file path (e.g. "src/server.dy").
    pub file: String,
    /// 1-based source line number.
    pub line: usize,
}

impl ErrorInfo {
    /// Build the Core Erlang tuple: `{dylang_error, Kind, Msg, Module, Fun, File, Line}`
    pub fn to_cexpr(&self) -> CExpr {
        CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("dylang_error".into())),
            CExpr::Lit(CLit::Atom(self.kind.as_atom().into())),
            self.message.clone(),
            lower_string_to_binary(&self.module),
            lower_string_to_binary(&self.function),
            lower_string_to_binary(&self.file),
            CExpr::Lit(CLit::Int(self.line as i64)),
        ])
    }
}
