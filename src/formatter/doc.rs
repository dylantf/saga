/// A document tree for pretty-printing. Based on Wadler-Lindig.
///
/// Build a `Doc` tree describing the ideal layout of your code, then call
/// `pretty(width, doc)` to render it to a string. The algorithm decides
/// where to insert line breaks to fit within the given width.
#[derive(Debug, Clone)]
pub enum Doc {
    /// Empty document -- produces no output.
    Nil,
    /// Literal text. Must not contain newlines.
    Text(String),
    /// A potential line break. In flat mode becomes `flat_alt` (default: space).
    /// In break mode becomes a newline followed by current indentation.
    Line { flat_alt: String },
    /// A forced line break. Always breaks, even inside a flattened group.
    HardLine,
    /// Concatenation of two documents.
    Concat(Box<Doc>, Box<Doc>),
    /// Increase indentation by `indent` spaces for the inner document.
    Nest(usize, Box<Doc>),
    /// Try to lay out the inner document on a single line (flat mode).
    /// If it doesn't fit, fall back to break mode.
    Group(Box<Doc>),
    /// Emit `broken` in break mode, `flat` in flat mode.
    /// Useful for trailing commas, trailing separators, etc.
    IfBreak { broken: Box<Doc>, flat: Box<Doc> },
}

// --- Constructors ---

impl Doc {
    /// Literal text (must not contain newlines).
    pub fn text(s: impl Into<String>) -> Doc {
        let s = s.into();
        if s.is_empty() { Doc::Nil } else { Doc::Text(s) }
    }

    /// A potential line break: space when flat, newline when broken.
    pub fn line() -> Doc {
        Doc::Line {
            flat_alt: " ".into(),
        }
    }

    /// A potential line break: empty when flat, newline when broken.
    /// Useful for trailing separators where you don't want a space.
    pub fn softline() -> Doc {
        Doc::Line {
            flat_alt: String::new(),
        }
    }

    /// A forced line break. Always produces a newline, even in flat mode.
    pub fn hardline() -> Doc {
        Doc::HardLine
    }

    /// Indent the inner document by `n` additional spaces.
    pub fn nest(n: usize, doc: Doc) -> Doc {
        Doc::Nest(n, Box::new(doc))
    }

    /// Try to fit the inner document on one line.
    pub fn group(doc: Doc) -> Doc {
        Doc::Group(Box::new(doc))
    }

    /// Emit `broken` in break mode, `flat` in flat mode.
    pub fn if_break(broken: Doc, flat: Doc) -> Doc {
        Doc::IfBreak { broken: Box::new(broken), flat: Box::new(flat) }
    }

    /// Structurally flatten a document: remove all group-breaking decisions
    /// so the result always renders on a single line. Used for contexts where
    /// line breaks would change semantics (e.g. expressions inside string
    /// interpolation holes).
    pub fn flat(doc: Doc) -> Doc {
        match doc {
            Doc::Nil | Doc::Text(_) => doc,
            Doc::HardLine => Doc::HardLine,
            Doc::Line { flat_alt } => Doc::text(flat_alt),
            Doc::Concat(a, b) => Doc::Concat(
                Box::new(Doc::flat(*a)),
                Box::new(Doc::flat(*b)),
            ),
            Doc::Nest(n, inner) => Doc::Nest(n, Box::new(Doc::flat(*inner))),
            Doc::Group(inner) => Doc::flat(*inner),
            Doc::IfBreak { flat, .. } => Doc::flat(*flat),
        }
    }

    /// Concatenate a sequence of docs with a separator between each pair.
    pub fn join(sep: Doc, docs: Vec<Doc>) -> Doc {
        let mut result = Doc::Nil;
        for (i, doc) in docs.into_iter().enumerate() {
            if i > 0 {
                result = Doc::Concat(Box::new(result), Box::new(sep.clone()));
            }
            result = Doc::Concat(Box::new(result), Box::new(doc));
        }
        result
    }

    /// Concatenate a sequence of docs with a line break between each pair.
    /// In flat mode the breaks become spaces; in break mode they become newlines.
    pub fn intersperse_line(docs: Vec<Doc>) -> Doc {
        Doc::join(Doc::line(), docs)
    }

    /// Concatenate two documents.
    pub fn append(self, other: Doc) -> Doc {
        match (&self, &other) {
            (Doc::Nil, _) => other,
            (_, Doc::Nil) => self,
            _ => Doc::Concat(Box::new(self), Box::new(other)),
        }
    }
}

/// Concatenate multiple docs.
#[macro_export]
macro_rules! docs {
    () => { $crate::formatter::Doc::Nil };
    ($single:expr) => { $single };
    ($first:expr, $($rest:expr),+ $(,)?) => {
        $first$(.append($rest))+
    };
}

// --- Rendering ---

/// Render a document to a string, fitting within `width` columns.
pub fn pretty(width: usize, doc: &Doc) -> String {
    let mut output = String::new();
    let mut stack: Vec<(usize, Mode, &Doc)> = vec![(0, Mode::Break, doc)];
    let mut col: usize = 0;

    while let Some((indent, mode, doc)) = stack.pop() {
        match doc {
            Doc::Nil => {}
            Doc::Text(s) => {
                output.push_str(s);
                col += s.len();
            }
            Doc::Line { flat_alt } => match mode {
                Mode::Flat => {
                    output.push_str(flat_alt);
                    col += flat_alt.len();
                }
                Mode::Break => {
                    output.push('\n');
                    output.extend(std::iter::repeat_n(' ', indent));
                    col = indent;
                }
            },
            Doc::HardLine => {
                output.push('\n');
                output.extend(std::iter::repeat_n(' ', indent));
                col = indent;
            }
            Doc::Concat(a, b) => {
                // Push b first so a is processed first (stack is LIFO)
                stack.push((indent, mode, b));
                stack.push((indent, mode, a));
            }
            Doc::Nest(n, inner) => {
                stack.push((indent + n, mode, inner));
            }
            Doc::Group(inner) => {
                // Build the measurement stack: the group's content (flat) + everything
                // remaining on the main stack (which will follow on the same line).
                let mut measure: Vec<(usize, Mode, &Doc)> = stack.clone();
                measure.push((indent, Mode::Flat, inner));
                if fits(width as isize - col as isize, &measure) {
                    stack.push((indent, Mode::Flat, inner));
                } else {
                    stack.push((indent, Mode::Break, inner));
                }
            }
            Doc::IfBreak { broken, flat } => match mode {
                Mode::Break => stack.push((indent, mode, broken)),
                Mode::Flat => stack.push((indent, mode, flat)),
            },
        }
    }

    // Trim trailing whitespace from each line
    let trimmed: Vec<&str> = output.lines().map(|l| l.trim_end()).collect();
    let mut result = trimmed.join("\n");
    // Ensure trailing newline
    if !result.ends_with('\n') {
        result.push('\n');
    }
    result
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Mode {
    Flat,
    Break,
}

/// Check whether a document fits within `remaining` columns when laid out in
/// the given mode. Walks the document tree, consuming horizontal space for
/// text and flat-mode line alternatives. Returns false as soon as remaining
/// goes negative or a hard break is hit in flat mode.
fn fits(remaining: isize, initial: &[(usize, Mode, &Doc)]) -> bool {
    let mut remaining = remaining;
    let mut stack: Vec<(usize, Mode, &Doc)> = initial.to_vec();

    while let Some((indent, mode, doc)) = stack.pop() {
        if remaining < 0 {
            return false;
        }
        match doc {
            Doc::Nil => {}
            Doc::Text(s) => {
                remaining -= s.len() as isize;
            }
            Doc::Line { flat_alt } => match mode {
                Mode::Flat => {
                    remaining -= flat_alt.len() as isize;
                }
                Mode::Break => {
                    // Line in break mode always fits (produces a newline)
                    return true;
                }
            },
            Doc::HardLine => {
                // HardLine can't be flattened
                return mode == Mode::Break;
            }
            Doc::Concat(a, b) => {
                stack.push((indent, mode, b));
                stack.push((indent, mode, a));
            }
            Doc::Nest(n, inner) => {
                stack.push((indent + n, mode, inner));
            }
            Doc::Group(inner) => {
                // When measuring fit, assume flat
                stack.push((indent, Mode::Flat, inner));
            }
            Doc::IfBreak { broken, flat } => match mode {
                Mode::Break => stack.push((indent, mode, broken)),
                Mode::Flat => stack.push((indent, mode, flat)),
            },
        }
    }

    remaining >= 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_text() {
        let doc = Doc::text("hello");
        assert_eq!(pretty(80, &doc), "hello\n");
    }

    #[test]
    fn group_fits_on_one_line() {
        // [1, 2, 3] -- fits in 80 cols
        let doc = Doc::group(docs![
            Doc::text("["),
            Doc::nest(
                2,
                docs![
                    Doc::softline(),
                    Doc::text("1,"),
                    Doc::line(),
                    Doc::text("2,"),
                    Doc::line(),
                    Doc::text("3"),
                ]
            ),
            Doc::softline(),
            Doc::text("]"),
        ]);
        assert_eq!(pretty(80, &doc), "[1, 2, 3]\n");
    }

    #[test]
    fn group_breaks_when_too_wide() {
        // Same doc but width=8 forces breaking (flat form "[1, 2, 3]" is 9 chars)
        let doc = Doc::group(docs![
            Doc::text("["),
            Doc::nest(
                2,
                docs![
                    Doc::softline(),
                    Doc::text("1,"),
                    Doc::line(),
                    Doc::text("2,"),
                    Doc::line(),
                    Doc::text("3"),
                ]
            ),
            Doc::softline(),
            Doc::text("]"),
        ]);
        assert_eq!(pretty(8, &doc), "[\n  1,\n  2,\n  3\n]\n");
    }

    #[test]
    fn hardline_always_breaks() {
        let doc = Doc::group(docs![Doc::text("a"), Doc::hardline(), Doc::text("b"),]);
        assert_eq!(pretty(80, &doc), "a\nb\n");
    }

    #[test]
    fn nested_groups() {
        // Outer group breaks, inner group stays flat
        let inner = Doc::group(docs![
            Doc::text("("),
            Doc::nest(2, docs![Doc::softline(), Doc::text("x"),]),
            Doc::softline(),
            Doc::text(")"),
        ]);
        let doc = Doc::group(docs![
            Doc::text("f"),
            Doc::nest(2, docs![Doc::line(), inner.clone(), Doc::line(), inner,]),
        ]);
        // At width 80, everything fits on one line
        assert_eq!(pretty(80, &doc), "f (x) (x)\n");
        // At width 8, outer breaks but inner groups stay flat (each "(x)" is 3 chars)
        assert_eq!(pretty(8, &doc), "f\n  (x)\n  (x)\n");
    }

    #[test]
    fn join_with_separator() {
        let items = vec![Doc::text("a"), Doc::text("b"), Doc::text("c")];
        let doc = Doc::join(Doc::text(", "), items);
        assert_eq!(pretty(80, &doc), "a, b, c\n");
    }

    #[test]
    fn empty_doc() {
        assert_eq!(pretty(80, &Doc::Nil), "\n");
    }

    #[test]
    fn record_like_structure() {
        // record User { name: String, age: Int }
        let fields = vec![Doc::text("name: String"), Doc::text("age: Int")];
        let doc = Doc::group(docs![
            Doc::text("record User {"),
            Doc::nest(
                2,
                docs![
                    Doc::line(),
                    Doc::join(docs![Doc::text(","), Doc::line()], fields),
                ]
            ),
            Doc::line(),
            Doc::text("}"),
        ]);
        // Fits on one line at width 80
        assert_eq!(pretty(80, &doc), "record User { name: String, age: Int }\n");
        // Breaks at narrow width
        assert_eq!(
            pretty(20, &doc),
            "record User {\n  name: String,\n  age: Int\n}\n"
        );
    }
}
