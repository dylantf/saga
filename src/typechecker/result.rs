//! Typechecker output: the public result of typechecking a program.
//!
//! Downstream consumers (elaborator, lowerer, LSP) depend on CheckResult
//! instead of reaching into Checker internals. The Checker builds this
//! at the end of check_program.

use std::collections::{HashMap, HashSet};

use super::{
    Checker, Diagnostic, EffectDefInfo, HandlerInfo, ModuleContext, Scheme, Severity, Substitution,
    TraitEvidence, TraitInfo, TypeEnv,
};

/// The public output of typechecking. Downstream consumers (elaborator, lowerer,
/// LSP) read from this instead of reaching into Checker internals.
#[derive(Clone)]
pub struct CheckResult {
    /// Type environment: function and constructor type schemes.
    pub env: TypeEnv,
    /// Substitution (for resolving display types in the LSP).
    pub sub: Substitution,
    /// Constructor type schemes (for LSP hover/completion).
    pub constructors: HashMap<String, Scheme>,
    /// Trait evidence for elaboration (dictionary passing).
    pub evidence: Vec<TraitEvidence>,
    /// All diagnostics (errors and warnings) from typechecking.
    pub diagnostics: Vec<Diagnostic>,
    /// Module system output (codegen info, parsed programs, module map).
    pub(crate) modules: ModuleContext,
    /// Trait definitions (for elaboration).
    pub traits: HashMap<String, TraitInfo>,
    /// Effect definitions (for LSP completion, lowerer).
    pub effects: HashMap<String, EffectDefInfo>,
    /// Handler definitions (for LSP completion, lowerer).
    pub handlers: HashMap<String, HandlerInfo>,
    /// Effect requirements per function.
    pub fun_effects: HashMap<String, HashSet<String>>,
    /// Per-span type information for LSP hover.
    /// Types may contain unresolved variables; use `type_at()` to get resolved types.
    pub type_at_span: HashMap<crate::token::Span, super::Type>,
    /// Maps handler arm span -> (effect op definition span, source module) (LSP go-to-def, level 2).
    pub handler_arm_targets: HashMap<crate::token::Span, (crate::token::Span, Option<String>)>,
    /// Maps effect call span -> (handler arm span, source module) (LSP go-to-def, level 1).
    pub effect_call_targets: HashMap<crate::token::Span, (crate::token::Span, Option<String>)>,
    /// For each `with` body span: the set of op names reachable within it, plus
    /// a bool indicating whether codegen should conservatively emit all arms.
    pub with_reachable_ops: HashMap<crate::token::Span, (HashSet<String>, bool)>,
}

impl CheckResult {
    /// Whether typechecking found any errors.
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| matches!(d.severity, Severity::Error))
    }

    /// All errors.
    pub fn errors(&self) -> Vec<&Diagnostic> {
        self.diagnostics.iter().filter(|d| matches!(d.severity, Severity::Error)).collect()
    }

    /// All warnings.
    pub fn warnings(&self) -> Vec<&Diagnostic> {
        self.diagnostics.iter().filter(|d| matches!(d.severity, Severity::Warning)).collect()
    }

    /// Effect names for LSP completion.
    pub fn effect_names(&self) -> Vec<String> {
        self.effects.keys().cloned().collect()
    }

    /// Handler names for LSP completion.
    pub fn handler_names(&self) -> Vec<String> {
        self.handlers.keys().cloned().collect()
    }

    /// Codegen info for all typechecked modules.
    pub fn codegen_info(&self) -> &std::collections::HashMap<String, super::ModuleCodegenInfo> {
        &self.modules.codegen_info
    }

    /// Cached parsed programs for typechecked modules.
    pub fn programs(&self) -> &std::collections::HashMap<String, crate::ast::Program> {
        &self.modules.programs
    }

    /// Module map (module name -> file path).
    pub fn module_map(&self) -> Option<&super::check_module::ModuleMap> {
        self.modules.map.as_ref()
    }

    /// Look up the resolved type at a span, applying the substitution.
    pub fn type_at(&self, span: &crate::token::Span) -> Option<String> {
        let ty = self.type_at_span.get(span)?;
        let resolved = self.sub.apply(ty);
        Some(format!("{}", resolved))
    }
}

impl Checker {
    /// Extract the public-facing result from the current checker state.
    /// Clones the output-relevant fields, leaving the Checker intact
    /// (needed because with_prelude continues using the Checker after
    /// checking the prelude).
    pub fn to_result(&self) -> CheckResult {
        let diagnostics = self.collected_diagnostics.clone();
        CheckResult {
            env: self.env.clone(),
            sub: self.sub.clone(),
            constructors: self.constructors.clone(),
            evidence: self.evidence.clone(),
            diagnostics,
            modules: self.modules.clone(),
            traits: self.traits.clone(),
            effects: self.effects.clone(),
            handlers: self.handlers.clone(),
            fun_effects: self.fun_effects.clone(),
            type_at_span: self.type_at_span.clone(),
            handler_arm_targets: self.handler_arm_targets.clone(),
            effect_call_targets: self.effect_call_targets.clone(),
            with_reachable_ops: self.with_reachable_ops.clone(),
        }
    }
}
