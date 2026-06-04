#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompileOptions {
    pub selective_no_fallback: bool,
}

impl CompileOptions {
    pub fn with_selective_no_fallback(mut self, enabled: bool) -> Self {
        self.selective_no_fallback = enabled;
        self
    }
}
