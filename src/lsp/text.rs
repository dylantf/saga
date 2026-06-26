use tower_lsp::lsp_types::{Location, Position, Range};

#[derive(Clone)]
pub(super) struct LineIndex {
    line_starts: Vec<usize>,
}

impl LineIndex {
    pub(super) fn new(text: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Self { line_starts }
    }

    pub(super) fn offset_to_position(&self, offset: usize, source: &str) -> Position {
        let offset = clamp_to_char_boundary(source, offset.min(source.len()));
        let line = self
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1);
        let line_start = self.line_starts.get(line).copied().unwrap_or(0);
        let line_text = &source[line_start..offset];
        let utf16_col: usize = line_text.chars().map(|c| c.len_utf16()).sum();
        Position::new(line as u32, utf16_col as u32)
    }

    pub(super) fn position_to_offset(&self, position: Position, source: &str) -> usize {
        let line = position.line as usize;
        let Some(&line_start) = self.line_starts.get(line) else {
            return source.len();
        };
        let line_end = self
            .line_starts
            .get(line + 1)
            .copied()
            .unwrap_or(source.len());
        let line_text = &source[line_start..line_end];
        let target_col = position.character as usize;
        let mut utf16_col = 0;

        for (byte_offset, ch) in line_text.char_indices() {
            if utf16_col >= target_col {
                return line_start + byte_offset;
            }
            utf16_col += ch.len_utf16();
        }

        line_end
    }
}

pub(super) fn clamp_to_char_boundary(source: &str, mut offset: usize) -> usize {
    while offset > 0 && !source.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

pub(super) fn span_to_range(
    span: &saga::token::Span,
    line_index: &LineIndex,
    source: &str,
) -> Range {
    Range {
        start: line_index.offset_to_position(span.start, source),
        end: line_index.offset_to_position(span.end, source),
    }
}

pub(super) fn range_contains_position(range: &Range, position: Position) -> bool {
    position_leq(range.start, position) && position_leq(position, range.end)
}

fn position_leq(a: Position, b: Position) -> bool {
    a.line < b.line || (a.line == b.line && a.character <= b.character)
}

pub(super) fn range_width(range: &Range) -> u32 {
    range
        .end
        .line
        .saturating_sub(range.start.line)
        .saturating_mul(u32::MAX / 2)
        .saturating_add(range.end.character.saturating_sub(range.start.character))
}

pub(super) fn sort_and_dedup_locations(locations: &mut Vec<Location>) {
    locations.sort_by(|a, b| {
        a.uri
            .as_str()
            .cmp(b.uri.as_str())
            .then(a.range.start.line.cmp(&b.range.start.line))
            .then(a.range.start.character.cmp(&b.range.start.character))
            .then(a.range.end.line.cmp(&b.range.end.line))
            .then(a.range.end.character.cmp(&b.range.end.character))
    });
    locations.dedup_by(|a, b| {
        a.uri == b.uri && a.range.start == b.range.start && a.range.end == b.range.end
    });
}

pub(super) fn extract_prefix(source: &str, offset: usize) -> &str {
    let offset = clamp_to_char_boundary(source, offset.min(source.len()));
    let before = &source[..offset];
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
        .map(|i| i + 1)
        .unwrap_or(0);
    &before[start..]
}

pub(super) fn source_text_at(source: &str, span: saga::token::Span) -> &str {
    if span.start < span.end
        && span.end <= source.len()
        && source.is_char_boundary(span.start)
        && source.is_char_boundary(span.end)
    {
        &source[span.start..span.end]
    } else {
        ""
    }
}

pub(super) fn full_document_range(source: &str) -> Range {
    let line_index = LineIndex::new(source);
    Range {
        start: Position::new(0, 0),
        end: line_index.offset_to_position(source.len(), source),
    }
}
