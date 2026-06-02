#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompileOptions {
    pub diagnostics: DiagnosticOptions,
    pub codegen_backend: CodegenBackend,
    pub selective_no_fallback: bool,
}

impl CompileOptions {
    pub fn with_monadic_stats(mut self, mode: MonadicStatsMode) -> Self {
        self.diagnostics.monadic_stats = mode;
        self
    }

    pub fn with_codegen_backend(mut self, backend: CodegenBackend) -> Self {
        self.codegen_backend = backend;
        self
    }

    pub fn with_selective_no_fallback(mut self, enabled: bool) -> Self {
        self.selective_no_fallback = enabled;
        if enabled {
            self.codegen_backend = CodegenBackend::Selective;
        }
        self
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum CodegenBackend {
    #[default]
    Uniform,
    Selective,
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
