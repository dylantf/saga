/// Maps byte offsets to line:column positions.
#[derive(Clone)]
pub struct LineIndex {
    /// Byte offset of the start of each line.
    line_starts: Vec<usize>,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        LineIndex { line_starts }
    }

    /// Convert a byte offset to (line, utf16_column), both 0-based.
    pub fn offset_to_line_col(&self, offset: usize, source: &str) -> (usize, usize) {
        let line = self
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1);
        let line_start = self.line_starts[line];
        let line_text = &source[line_start..offset];
        let utf16_col: usize = line_text.chars().map(|c| c.len_utf16()).sum();
        (line, utf16_col)
    }

    /// Convert (line, utf16_column) to a byte offset. Both 0-based.
    pub fn line_col_to_offset(&self, line: usize, col: usize, source: &str) -> usize {
        if line >= self.line_starts.len() {
            return *self.line_starts.last().unwrap_or(&0);
        }
        let line_start = self.line_starts[line];
        let line_end = self
            .line_starts
            .get(line + 1)
            .copied()
            .unwrap_or(source.len());
        let line_text = &source[line_start..line_end];
        let mut utf16_count = 0;
        for (byte_offset, ch) in line_text.char_indices() {
            if utf16_count >= col {
                return line_start + byte_offset;
            }
            utf16_count += ch.len_utf16();
        }
        line_end
    }
}
