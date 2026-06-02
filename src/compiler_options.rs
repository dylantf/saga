#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompileOptions {
    pub diagnostics: DiagnosticOptions,
}

impl CompileOptions {
    pub fn with_monadic_stats(mut self, mode: MonadicStatsMode) -> Self {
        self.diagnostics.monadic_stats = mode;
        self
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DiagnosticOptions {
    pub monadic_stats: MonadicStatsMode,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum MonadicStatsMode {
    #[default]
    Off,
    Summary,
    Full,
}

impl MonadicStatsMode {
    pub fn is_enabled(self) -> bool {
        !matches!(self, Self::Off)
    }
}
