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
    /// Per-node type information for Expr nodes (LSP hover).
    /// Types may contain unresolved variables; use `type_at_node()` to get resolved types.
    pub type_at_node: HashMap<crate::ast::NodeId, super::Type>,
    /// Per-span type information for Pat bindings (LSP hover).
    pub type_at_span: HashMap<crate::token::Span, super::Type>,
    /// Maps handler arm span -> (effect op definition span, source module) (LSP go-to-def, level 2).
    pub handler_arm_targets: HashMap<crate::token::Span, (crate::token::Span, Option<String>)>,
    /// Maps effect call span -> (handler arm span, source module) (LSP go-to-def, level 1).
    pub effect_call_targets: HashMap<crate::token::Span, (crate::token::Span, Option<String>)>,
    /// Dict params for let bindings with trait constraints: name -> (params, value_arity).
    pub let_dict_params: HashMap<String, (Vec<(String, String)>, usize)>,
    /// Deferred effects for let bindings that partially apply effectful functions.
    /// name -> effect names. Used by the lowerer to register effectful local vars.
    pub let_effect_bindings: HashMap<String, Vec<String>>,
    /// Resolution map: usage NodeId -> definition NodeId (for find-all-references).
    pub references: HashMap<crate::ast::NodeId, crate::ast::NodeId>,
    /// NodeId -> Span map for recorded nodes (for resolving NodeIds to locations).
    pub node_spans: HashMap<crate::ast::NodeId, crate::token::Span>,
    /// Import origins: binding name -> source module name (for cross-module find-references).
    pub import_origins: HashMap<String, String>,
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

    /// Cached per-module CheckResults (from typecheck_import, avoids re-typechecking).
    pub fn module_check_results(&self) -> &std::collections::HashMap<String, CheckResult> {
        &self.modules.check_results
    }

    /// Module map (module name -> file path).
    pub fn module_map(&self) -> Option<&super::check_module::ModuleMap> {
        self.modules.map.as_ref()
    }

    /// Look up the resolved type at a node ID, applying the substitution.
    /// Remaining free type variables are prettified (a, b, c, ...).
    pub fn type_at_node(&self, node_id: &crate::ast::NodeId) -> Option<String> {
        let ty = self.type_at_node.get(node_id)?;
        Some(format!("{}", self.prettify(ty)))
    }

    /// Look up the resolved type at a span (for Pat bindings), applying the substitution.
    /// Remaining free type variables are prettified (a, b, c, ...).
    pub fn type_at_span(&self, span: &crate::token::Span) -> Option<String> {
        let ty = self.type_at_span.get(span)?;
        Some(format!("{}", self.prettify(ty)))
    }

    /// Apply substitution and rename any remaining free vars to a, b, c, ...
    fn prettify(&self, ty: &super::Type) -> super::Type {
        let resolved = self.sub.apply(ty);
        let mut vars = Vec::new();
        super::collect_free_vars(&resolved, &mut vars);
        if vars.is_empty() {
            return resolved;
        }
        let names: std::collections::HashMap<u32, String> = vars
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, ((b'a' + i as u8) as char).to_string()))
            .collect();
        super::rename_vars(&resolved, &names)
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
            traits: self.trait_state.traits.clone(),
            effects: self.effects.clone(),
            handlers: self.handlers.clone(),
            fun_effects: self.effect_state.fun_effects.clone(),
            type_at_node: self.lsp.type_at_node.clone(),
            type_at_span: self.lsp.type_at_span.clone(),
            handler_arm_targets: self.lsp.handler_arm_targets.clone(),
            effect_call_targets: self.lsp.effect_call_targets.clone(),
            let_dict_params: self.let_dict_params.clone(),
            let_effect_bindings: self.effect_state.let_bindings.clone(),
            references: self.lsp.references.clone(),
            node_spans: self.lsp.node_spans.clone(),
            import_origins: self.lsp.import_origins.clone(),
        }
    }
}
