//! Typechecker output: the public result of typechecking a program.
//!
//! Downstream consumers (elaborator, lowerer, LSP) depend on CheckResult
//! instead of reaching into Checker internals. The Checker builds this
//! at the end of check_program.

use std::collections::{HashMap, HashSet};

use super::{
    Checker, Diagnostic, EffectDefInfo, HandlerInfo, ModuleContext, Scheme, Severity, Substitution,
    TraitEvidence, TraitInfo, Type, TypeEnv,
};

/// Prettified effect op: (op_name, [(label, type)], return_type).
pub type PrettifiedOp = (String, Vec<(String, Type)>, Type);

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
    /// Record definitions: record name -> field info (for LSP completion).
    pub records: HashMap<String, super::RecordInfo>,
    /// Resolution map: usage NodeId -> definition NodeId (for find-all-references).
    pub references: HashMap<crate::ast::NodeId, crate::ast::NodeId>,
    /// NodeId -> Span map for recorded nodes (for resolving NodeIds to locations).
    pub node_spans: HashMap<crate::ast::NodeId, crate::token::Span>,
    /// Type/effect name references: (span, name) for find-references on types.
    pub type_references: Vec<(crate::token::Span, String)>,
    /// Constructor name -> definition NodeId (for symbol index).
    pub constructor_def_ids: HashMap<String, crate::ast::NodeId>,
    /// Doc comments from imported declarations: name -> doc lines.
    pub imported_docs: HashMap<String, Vec<String>>,
    /// Import declarations from the prelude (so the lowerer knows which
    /// stdlib names are actually in scope for user code).
    pub prelude_imports: Vec<crate::ast::Decl>,
    /// Name resolution map: user-visible names -> canonical names.
    pub scope_map: super::ScopeMap,
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

    /// Look up an effect by name, resolving bare/aliased names through the scope_map.
    pub fn resolve_effect(&self, name: &str) -> Option<&EffectDefInfo> {
        self.effects.get(name).or_else(|| {
            self.scope_map.resolve_effect(name)
                .and_then(|canonical| self.effects.get(canonical))
        }).or_else(|| {
            // Suffix match for qualified names (e.g. "Fail.Fail" -> "Std.Fail.Fail")
            if name.contains('.') {
                let suffix = format!(".{}", name);
                self.effects.iter()
                    .find(|(k, _)| k.ends_with(&suffix))
                    .map(|(_, v)| v)
            } else {
                None
            }
        })
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

    /// Cached module exports (module name -> exports) for all typechecked modules.
    pub fn module_exports(&self) -> &std::collections::HashMap<String, super::ModuleExports> {
        &self.modules.exports
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

    /// Prettify record field types with consistent variable naming.
    /// Returns field `(name, type)` pairs with free vars renamed to a, b, c, ...
    pub fn prettify_record(
        &self,
        info: &super::RecordInfo,
    ) -> Vec<(String, super::Type)> {
        let resolved: Vec<(String, super::Type)> = info
            .fields
            .iter()
            .map(|(name, ty)| (name.clone(), self.sub.apply(ty)))
            .collect();

        let mut vars = Vec::new();
        for (_, ty) in &resolved {
            super::collect_free_vars(ty, &mut vars);
        }
        if vars.is_empty() {
            return resolved;
        }

        let names: std::collections::HashMap<u32, String> = vars
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, ((b'a' + i as u8) as char).to_string()))
            .collect();

        resolved
            .into_iter()
            .map(|(name, ty)| (name, super::rename_vars(&ty, &names)))
            .collect()
    }

    /// Prettify all types in an effect definition with consistent variable naming.
    /// Returns `(params, return_type)` pairs for each op, with free vars renamed to a, b, c, ...
    pub fn prettify_effect(
        &self,
        info: &super::EffectDefInfo,
    ) -> Vec<PrettifiedOp> {
        // Resolve all types through substitution first
        let resolved_ops: Vec<PrettifiedOp> = info
            .ops
            .iter()
            .map(|op| {
                let params: Vec<(String, super::Type)> = op
                    .params
                    .iter()
                    .map(|(label, ty)| (label.clone(), self.sub.apply(ty)))
                    .collect();
                let ret = self.sub.apply(&op.return_type);
                (op.name.clone(), params, ret)
            })
            .collect();

        // Collect all free vars across all ops for consistent naming
        let mut vars = Vec::new();
        for (_, params, ret) in &resolved_ops {
            for (_, ty) in params {
                super::collect_free_vars(ty, &mut vars);
            }
            super::collect_free_vars(ret, &mut vars);
        }
        if vars.is_empty() {
            return resolved_ops;
        }

        let names: std::collections::HashMap<u32, String> = vars
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, ((b'a' + i as u8) as char).to_string()))
            .collect();

        resolved_ops
            .into_iter()
            .map(|(name, params, ret)| {
                let params = params
                    .into_iter()
                    .map(|(label, ty)| (label, super::rename_vars(&ty, &names)))
                    .collect();
                let ret = super::rename_vars(&ret, &names);
                (name, params, ret)
            })
            .collect()
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
            fun_effects: {
                let mut fun_effects = HashMap::new();
                for name in &self.effect_meta.known_funs {
                    if let Some(scheme) = self.env.get(name) {
                        let resolved = self.sub.apply(&scheme.ty);
                        let effects = super::effects_from_type(&resolved);
                        // Canonicalize bare effect names using the effects map
                        let effects: HashSet<String> = effects
                            .into_iter()
                            .map(|e| {
                                if let Some(info) = self.effects.get(&e) {
                                    if let Some(src) = &info.source_module {
                                        format!("{}.{}", src, e)
                                    } else if let Some(m) = &self.current_module {
                                        format!("{}.{}", m, e)
                                    } else {
                                        e
                                    }
                                } else {
                                    e
                                }
                            })
                            .collect();
                        fun_effects.insert(name.clone(), effects);
                    }
                }
                fun_effects
            },
            type_at_node: self.lsp.type_at_node.clone(),
            type_at_span: self.lsp.type_at_span.clone(),
            handler_arm_targets: self.lsp.handler_arm_targets.clone(),
            effect_call_targets: self.lsp.effect_call_targets.clone(),
            let_dict_params: self.let_dict_params.clone(),
            let_effect_bindings: {
                let mut let_effect_bindings = HashMap::new();
                for name in &self.effect_meta.known_let_bindings {
                    if let Some(scheme) = self.env.get(name) {
                        let resolved = self.sub.apply(&scheme.ty);
                        let effects: HashSet<String> = super::effects_from_type(&resolved);
                        if !effects.is_empty() {
                            let mut sorted: Vec<String> = effects.into_iter().collect();
                            sorted.sort();
                            let_effect_bindings.insert(name.clone(), sorted);
                        }
                    }
                }
                let_effect_bindings
            },
            records: self.records.clone(),
            references: self.lsp.references.clone(),
            node_spans: self.lsp.node_spans.clone(),
            type_references: self.lsp.type_references.clone(),
            constructor_def_ids: self.lsp.constructor_def_ids.clone(),
            imported_docs: self.lsp.imported_docs.clone(),
            prelude_imports: self.prelude_imports.clone(),
            scope_map: self.scope_map.clone(),
        }
    }
}
