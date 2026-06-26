mod builtins;
mod check_decl;
mod check_module;
mod core;
pub use check_module::{
    BUILTIN_MODULES, HeaderEffectDecl, HeaderEffectOp, HeaderEffectRef, HeaderExposedItem,
    HeaderExposing, HeaderFunction, HeaderHandlerDecl, HeaderImport, HeaderReExport,
    HeaderReExportAll, HeaderRecordDecl, HeaderTraitBound, HeaderTraitDecl, HeaderTraitMethod,
    HeaderTraitRef, HeaderTypeDecl, HeaderTypeExpr, HeaderTypeParam, HeaderVisibility, ModuleGraph,
    ModuleHeader, ModuleMap, ModuleVisibility, ModuleVisibilityMap, build_module_graph,
    builtin_module_source, import_modules_for_program, scan_project_modules, scan_source_dir,
};
mod check_traits;
mod effects;
pub(crate) mod exhaustiveness;
mod handlers;
mod infer;
mod patterns;
mod records;
mod resolve;
mod result;
mod state;
mod unify;
pub use check_module::{EffectDef, EffectOpDef, ModuleCodegenInfo, ModuleExports, TraitImplDict};
pub use core::*;
pub(crate) use resolve::{ResolutionResult, ResolvedValue};
pub use result::{
    CheckResult, LetDictInfo, effect_operation_signature_from_info,
    trait_method_signature_from_info,
};
pub use state::*;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, ExprKind, Kind};
use crate::token::Span;

/// Canonical stdlib trait name for type-level symbol reflection.
pub(crate) const KNOWN_SYMBOL_TRAIT: &str = "Std.Base.KnownSymbol";

/// Returns the span of the first effect call found in `expr`, if any.
/// Used to reject effect calls inside guard expressions.
pub(crate) fn find_effect_call(expr: &Expr) -> Option<Span> {
    match &expr.kind {
        ExprKind::EffectCall { .. } => Some(expr.span),
        ExprKind::App { func, arg, .. } => find_effect_call(func).or_else(|| find_effect_call(arg)),
        ExprKind::BinOp { left, right, .. } => {
            find_effect_call(left).or_else(|| find_effect_call(right))
        }
        ExprKind::UnaryMinus { expr: inner, .. } => find_effect_call(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_effect_call(cond)
            .or_else(|| find_effect_call(then_branch))
            .or_else(|| find_effect_call(else_branch)),
        _ => None,
    }
}

impl Default for Checker {
    fn default() -> Self {
        Self::new()
    }
}

impl Checker {
    pub fn new() -> Self {
        let mut checker = Checker {
            next_var: 0,
            sub: Substitution::new(),
            env: TypeEnv::new(),
            constructors: HashMap::new(),
            records: HashMap::new(),
            effects: HashMap::new(),
            handlers: HashMap::new(),
            handler_funs: HashMap::new(),
            let_binding_handlers: HashMap::new(),
            resume_type: None,
            resume_return_type: None,
            effect_meta: EffectMeta::default(),
            effect_row: EffectRow::empty(),
            trait_forward_row_vars: std::collections::HashMap::new(),
            trait_state: TraitState::default(),
            field_candidates: HashMap::new(),
            modules: ModuleContext::default(),
            adt_variants: HashMap::new(),
            type_arity: HashMap::new(),
            type_param_kinds: HashMap::new(),
            type_aliases: HashMap::new(),
            var_kinds: HashMap::new(),
            outer_named_type_vars: HashMap::new(),
            fun_type_param_vars: HashMap::new(),
            scope_map: ScopeMap::default(),
            resolution: ResolutionResult::default(),
            evidence: Vec::new(),
            let_dict_params: HashMap::new(),
            collected_diagnostics: Vec::new(),
            pending_warnings: Vec::new(),
            internal_handler_normalization_warnings: HashSet::new(),
            lsp: LspState::default(),
            allow_bodyless_annotations: false,
            current_module: None,
            prelude_imports: Vec::new(),
            needs_ets_ref_table: false,
            needs_vec_table: false,
        };
        checker.register_builtins();
        checker
    }

    pub fn with_project_root(root: std::path::PathBuf) -> Self {
        let mut checker = Self::new();
        checker.modules.project_root = Some(root);
        checker
    }

    /// Snapshot current trait impls as the base layer (from Std.saga).
    /// Called after loading Std.saga so builtin module checkers inherit these impls.
    pub fn snapshot_base_trait_impls(&mut self) {
        self.modules.base_trait_impls = self.trait_state.impls.clone();
    }

    /// Create a checker with the prelude loaded and (optionally) a project
    /// root with its module map. This is the standard entry point for both
    /// the CLI and the LSP.
    pub fn with_prelude(
        project_root: Option<std::path::PathBuf>,
    ) -> std::result::Result<Self, Diagnostic> {
        let mut checker = match &project_root {
            Some(root) => Self::with_project_root(root.clone()),
            None => Self::new(),
        };

        if let Some(root) = &project_root
            && let Ok(module_map) = check_module::scan_project_modules(root)
        {
            checker.set_module_map(module_map);
        }

        // Load prelude (which imports Std first, then stdlib modules).
        // Std.saga defines base traits (Show, Ord) and is loaded as a real module
        // via `import Std` in the prelude.
        let prelude_src = include_str!("../stdlib/prelude.saga");
        let prelude_tokens = crate::lexer::Lexer::new(prelude_src)
            .lex()
            .expect("prelude lex");
        let mut prelude_program = crate::parser::Parser::new(prelude_tokens)
            .parse_program()
            .expect("prelude parse");
        crate::derive::expand_derives(&mut prelude_program, &crate::derive::ImportedDecls::empty());
        crate::desugar::desugar_program(&mut prelude_program);
        checker
            .check_program_inner(&mut prelude_program)
            .map_err(|errs| errs.into_iter().next().unwrap())?;

        // Save the prelude's import declarations so the lowerer can register
        // only the names the prelude actually exposes.
        checker.prelude_imports = prelude_program
            .into_iter()
            .filter(|d| matches!(d, crate::ast::Decl::Import { .. }))
            .collect();

        checker.modules.prelude_snapshot = Some(Box::new(checker.clone()));
        Ok(checker)
    }

    /// Remove a module's cached exports and trait impls from this checker.
    /// Used by the LSP to avoid false "duplicate impl" errors when re-checking
    /// a stdlib file that was already loaded via the prelude.
    pub fn evict_module(&mut self, module_name: &str) {
        let exports = self.modules.exports.remove(module_name).or_else(|| {
            self.modules
                .prelude_snapshot
                .as_ref()
                .and_then(|snapshot| snapshot.modules.exports.get(module_name).cloned())
        });
        if let Some(exports) = exports {
            for key in exports.trait_impls.keys() {
                self.trait_state.impls.remove(key);
            }
        }
        self.modules.codegen_info.remove(module_name);
        self.modules.programs.remove(module_name);
        self.modules.check_results.remove(module_name);
        self.modules.registered_canonical.remove(module_name);
    }

    /// Drain errors from collected_diagnostics, leaving warnings in place.
    pub(crate) fn drain_errors(&mut self) -> Vec<Diagnostic> {
        let (errors, rest): (Vec<_>, Vec<_>) = std::mem::take(&mut self.collected_diagnostics)
            .into_iter()
            .partition(|d| matches!(d.severity, Severity::Error));
        self.collected_diagnostics = rest;
        errors
    }

    /// Record the type of an expression node (by NodeId).
    pub(crate) fn record_type(&mut self, node_id: crate::ast::NodeId, ty: &Type) {
        self.lsp
            .type_at_node
            .entry(node_id)
            .or_insert_with(|| ty.clone());
    }

    /// Record the type of a pattern binding (by Span).
    pub(crate) fn record_type_at_span(&mut self, span: Span, ty: &Type) {
        self.lsp
            .type_at_span
            .entry(span)
            .or_insert_with(|| ty.clone());
    }

    /// Record a name resolution: usage_id references def_id.
    pub(crate) fn record_reference(
        &mut self,
        usage_id: crate::ast::NodeId,
        usage_span: Span,
        def_id: crate::ast::NodeId,
    ) {
        self.lsp.references.insert(usage_id, def_id);
        self.lsp.node_spans.insert(usage_id, usage_span);
    }

    /// Record a type/effect name reference from an EffectRef AST node.
    pub(crate) fn record_effect_ref(&mut self, effect_ref: &crate::ast::EffectRef) {
        let name_end = effect_ref.span.start + effect_ref.name.len();
        self.lsp.type_references.push((
            Span {
                start: effect_ref.span.start,
                end: name_end,
            },
            effect_ref.name.clone(),
        ));
    }

    pub(crate) fn resolved_value_name(&self, node_id: crate::ast::NodeId, source: &str) -> String {
        match self.resolution.value(node_id) {
            Some(ResolvedValue::Local { name, .. }) => name.clone(),
            Some(ResolvedValue::Global { lookup_name }) => lookup_name.clone(),
            None => source.to_string(),
        }
    }

    pub(crate) fn resolved_constructor_name(
        &self,
        node_id: crate::ast::NodeId,
        source: &str,
    ) -> String {
        self.resolution
            .constructor(node_id)
            .unwrap_or(source)
            .to_string()
    }

    pub(crate) fn resolved_type_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.type_ref(id).unwrap_or(source).to_string()
    }

    pub(crate) fn resolved_record_type_name(
        &self,
        node_id: crate::ast::NodeId,
        source: &str,
    ) -> String {
        self.resolution
            .record_type(node_id)
            .unwrap_or(source)
            .to_string()
    }

    pub(crate) fn resolved_trait_name_at(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.trait_ref(id).unwrap_or(source).to_string()
    }

    pub(crate) fn resolved_impl_trait_name(
        &self,
        node_id: crate::ast::NodeId,
        source: &str,
    ) -> String {
        self.resolution
            .impl_trait_ref(node_id)
            .unwrap_or(source)
            .to_string()
    }

    pub(crate) fn resolved_effect_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.effect_ref(id).unwrap_or(source).to_string()
    }

    pub(crate) fn resolved_impl_target_type_name(
        &self,
        node_id: crate::ast::NodeId,
        source: &str,
    ) -> String {
        self.resolution
            .impl_target_type_ref(node_id)
            .unwrap_or(source)
            .to_string()
    }

    pub(crate) fn resolved_handler_name(
        &self,
        node_id: crate::ast::NodeId,
        source: &str,
    ) -> String {
        match self.resolution.handler_ref(node_id) {
            Some(ResolvedValue::Local { name, .. }) => name.clone(),
            Some(ResolvedValue::Global { lookup_name }) => lookup_name.clone(),
            None => source.to_string(),
        }
    }

    /// Emit warnings for module-level functions that are never referenced.
    pub(crate) fn check_unused_functions(&mut self) {
        let used: std::collections::HashSet<crate::ast::NodeId> =
            self.lsp.references.values().copied().collect();
        for (def_id, name, span, public) in &self.lsp.fun_definitions {
            if *public || name == "main" || name.starts_with('_') {
                continue;
            }
            if !used.contains(def_id) {
                self.pending_warnings.push(PendingWarning::UnusedFunction {
                    span: *span,
                    name: name.clone(),
                });
            }
        }
    }

    /// Emit warnings for local variable bindings that are never referenced.
    pub(crate) fn check_unused_variables(&mut self) {
        let used: std::collections::HashSet<crate::ast::NodeId> =
            self.lsp.references.values().copied().collect();
        for (def_id, name, span) in &self.lsp.definitions {
            if name.starts_with('_') {
                continue;
            }
            if !used.contains(def_id) {
                self.pending_warnings.push(PendingWarning::UnusedVariable {
                    span: *span,
                    name: name.clone(),
                });
            }
        }
    }

    /// "Zonk" pass: apply final substitutions to deferred warnings and emit
    /// only those that are still relevant. Named after GHC's zonking pass.
    pub(crate) fn zonk_warnings(&mut self) {
        for warning in std::mem::take(&mut self.pending_warnings) {
            match warning {
                PendingWarning::DiscardedValue { span, ty } => {
                    let resolved = self.sub.apply(&ty);
                    let is_unit = matches!(&resolved, Type::Con(n, args) if n == canonicalize_type_name("Unit") && args.is_empty());
                    if !is_unit && !matches!(resolved, Type::Var(_) | Type::Error) {
                        let display_ty = self.prettify_type(&ty);
                        self.collected_diagnostics.push(Diagnostic::warning_at(
                            span,
                            format!(
                                "value of type `{}` is discarded; use `let _ = ...` to suppress",
                                display_ty
                            ),
                        ));
                    }
                }
                PendingWarning::UnusedVariable { span, name } => {
                    self.collected_diagnostics.push(Diagnostic::warning_at(
                        span,
                        format!("unused variable: `{}`", name),
                    ));
                }
                PendingWarning::UnusedFunction { span, name } => {
                    self.collected_diagnostics.push(Diagnostic::warning_at(
                        span,
                        format!("unused function: `{}`", name),
                    ));
                }
                PendingWarning::UnusedEffects {
                    span,
                    fun_name,
                    effects,
                } => {
                    self.collected_diagnostics.push(Diagnostic::warning_at(
                        span,
                        format!(
                            "function '{}' declares needs {{{}}} but never uses {}",
                            fun_name,
                            effects.join(", "),
                            if effects.len() == 1 { "it" } else { "them" },
                        ),
                    ));
                }
            }
        }
    }

    pub fn effect_names(&self) -> Vec<String> {
        self.effects.keys().cloned().collect()
    }

    pub fn handler_names(&self) -> Vec<String> {
        self.handlers.keys().cloned().collect()
    }

    pub fn set_current_module(&mut self, name: String) {
        self.current_module = Some(name);
    }

    pub fn set_module_map(&mut self, map: check_module::ModuleMap) {
        self.modules.map = Some(map);
        self.modules.module_graph = None;
    }

    pub fn set_source_overlay(&mut self, overlay: HashMap<std::path::PathBuf, String>) {
        self.modules.source_overlay = overlay;
        self.modules.module_graph = None;
    }

    pub fn module_map(&self) -> Option<&check_module::ModuleMap> {
        self.modules.map.as_ref()
    }

    pub fn module_map_mut(&mut self) -> Option<&mut check_module::ModuleMap> {
        self.modules.module_graph = None;
        self.modules.map.as_mut()
    }

    pub fn set_module_visibility(&mut self, vis: check_module::ModuleVisibilityMap) {
        self.modules.visibility = Some(vis);
    }

    pub fn module_visibility(&self) -> Option<&check_module::ModuleVisibilityMap> {
        self.modules.visibility.as_ref()
    }

    pub fn set_private_modules(&mut self, m: HashMap<String, check_module::ModuleMap>) {
        self.modules.private_modules = Some(m);
    }

    pub fn private_modules(&self) -> Option<&HashMap<String, check_module::ModuleMap>> {
        self.modules.private_modules.as_ref()
    }

    /// Seed this checker with a previously computed module cache entry.
    ///
    /// Project-level drivers such as the LSP use this to reuse clean imported
    /// module interfaces across fresh checker clones. The caller is responsible
    /// for validating that the cached entry still matches the current source
    /// and dependency context.
    pub fn seed_module_cache(
        &mut self,
        module_name: String,
        exports: ModuleExports,
        codegen_info: Option<ModuleCodegenInfo>,
        program: Option<crate::ast::Program>,
        check_result: Option<CheckResult>,
    ) {
        self.modules.exports.insert(module_name.clone(), exports);
        if let Some(codegen_info) = codegen_info {
            self.modules
                .codegen_info
                .insert(module_name.clone(), codegen_info);
        }
        if let Some(program) = program {
            self.modules.programs.insert(module_name.clone(), program);
        }
        if let Some(check_result) = check_result {
            self.modules.check_results.insert(module_name, check_result);
        }
    }

    /// Clear cached module semantic products while preserving project maps,
    /// visibility metadata, source overlays, and the prelude snapshot.
    ///
    /// LSP project state keeps module interfaces separately and seeds fresh
    /// checker clones as needed. Keeping these large caches inside the base
    /// checker makes every edit pay a large clone cost.
    pub fn clear_module_semantic_caches(&mut self) {
        self.modules.exports.clear();
        self.modules.codegen_info.clear();
        self.modules.programs.clear();
        self.modules.check_results.clear();
        self.modules.registered_canonical.clear();
    }

    /// Typecheck a module by name, triggering the full dependency walk.
    /// Used for library builds where there is no Main.saga entry point.
    pub fn try_typecheck_import_by_name(
        &mut self,
        module_name: &str,
    ) -> std::result::Result<(), Diagnostic> {
        let parts: Vec<String> = module_name.split('.').map(|s| s.to_string()).collect();
        let span = crate::token::Span { start: 0, end: 0 };
        self.typecheck_import(&parts, None, None, span)
    }

    /// Typecheck a module by name, triggering the full dependency walk.
    /// Used for library builds where there is no Main.saga entry point.
    pub fn typecheck_import_by_name(&mut self, module_name: &str) {
        if let Err(e) = self.try_typecheck_import_by_name(module_name) {
            eprintln!("Error typechecking module '{}': {}", module_name, e);
            std::process::exit(1);
        }
    }

    pub(crate) fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    /// Allocate a fresh type variable of the given kind. Star-kinded vars
    /// are the default and not recorded; Symbol-kinded vars are tracked in
    /// `var_kinds` so unification can enforce kind correctness.
    pub(crate) fn fresh_var_of_kind(&mut self, kind: Kind) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        if kind != Kind::Star {
            self.var_kinds.insert(id, kind);
        }
        Type::Var(id)
    }

    /// Kind of a type variable. Defaults to `Kind::Star` for vars not in
    /// `var_kinds` (the overwhelmingly common case).
    pub(crate) fn var_kind(&self, id: u32) -> Kind {
        self.var_kinds.get(&id).copied().unwrap_or(Kind::Star)
    }

    /// Best-effort kind of a type. For `Var`, look up `var_kinds`. For
    /// `Symbol`, kind is `Symbol`. Everything else is `Star` (for now).
    pub(crate) fn kind_of(&self, ty: &Type) -> Kind {
        match ty {
            Type::Symbol(_) => Kind::Symbol,
            Type::Var(id) => self.var_kind(*id),
            _ => Kind::Star,
        }
    }

    /// Instantiate a record's type parameters to fresh variables.
    /// Returns (instantiated field types, result Type::Con with fresh args).
    pub(crate) fn instantiate_record(
        &mut self,
        name: &str,
        info: &RecordInfo,
    ) -> (Vec<(String, Type)>, Type) {
        let mapping: HashMap<u32, Type> = info
            .type_params
            .iter()
            .map(|&id| (id, self.fresh_var()))
            .collect();
        let fields = info
            .fields
            .iter()
            .map(|(fname, ty)| (fname.clone(), Self::replace_vars(ty, &mapping)))
            .collect();
        let result_ty = Type::Con(
            name.into(),
            info.type_params
                .iter()
                .map(|id| mapping[id].clone())
                .collect(),
        );
        (fields, result_ty)
    }

    /// Push effects onto the accumulator, deduplicating by name.
    pub(crate) fn emit_effects(&mut self, effs: &EffectRow) {
        for entry in &effs.effects {
            if !self
                .effect_row
                .effects
                .iter()
                .any(|e| e.same_instantiation(entry))
            {
                self.effect_row.effects.push(entry.clone());
            }
        }
    }

    /// Push a single named effect onto the accumulator, deduplicating by exact instantiation.
    pub(crate) fn emit_effect(&mut self, name: String, args: Vec<Type>) {
        if !self
            .effect_row
            .effects
            .iter()
            .any(|e| e.name == name && e.args == args)
        {
            self.effect_row
                .effects
                .push(EffectEntry::unnamed(name, args));
        }
    }

    pub(crate) fn current_effect_args(&self, effect_name: &str) -> Vec<Type> {
        let Some(info) = self.effects.get(effect_name) else {
            return vec![];
        };
        let Some(cache) = self.effect_meta.type_param_cache.get(effect_name) else {
            return vec![];
        };
        info.type_params
            .iter()
            .filter_map(|param_id| cache.get(param_id))
            .map(|ty| self.sub.apply(ty))
            .collect()
    }

    pub(crate) fn prettify_effect_entry(&self, entry: &EffectEntry) -> String {
        let short = entry
            .name
            .rsplit('.')
            .next()
            .unwrap_or(entry.name.as_str())
            .to_string();
        format!(
            "{}",
            self.prettify_type(&Type::Con(short, entry.args.clone()))
        )
    }

    /// Save the current effect accumulator and start a fresh one.
    /// Returns the saved EffectRow so the caller can restore it later.
    pub(crate) fn save_effects(&mut self) -> EffectRow {
        std::mem::replace(&mut self.effect_row, EffectRow::empty())
    }

    /// Restore a previously saved effect accumulator, returning what
    /// accumulated since the save.
    pub(crate) fn restore_effects(&mut self, saved: EffectRow) -> EffectRow {
        std::mem::replace(&mut self.effect_row, saved)
    }

    /// Enter an isolated inference scope. Saves and clears
    /// effect_type_param_cache, field_candidates, resume_type, and
    /// resume_return_type. Call `exit_scope` to restore and collect
    /// what the scope accumulated.
    pub(crate) fn enter_scope(&mut self) -> InferScope {
        InferScope {
            effect_cache: std::mem::take(&mut self.effect_meta.type_param_cache),
            field_candidates: std::mem::take(&mut self.field_candidates),
            resume_type: self.resume_type.take(),
            resume_return_type: self.resume_return_type.take(),
        }
    }

    /// Exit an inference scope, restoring saved state and returning what
    /// accumulated during the scope's lifetime.
    pub(crate) fn exit_scope(&mut self, scope: InferScope) -> InferScopeResult {
        let result = InferScopeResult {
            effect_cache: std::mem::replace(
                &mut self.effect_meta.type_param_cache,
                scope.effect_cache,
            ),
            field_candidates: std::mem::replace(&mut self.field_candidates, scope.field_candidates),
        };
        self.resume_type = scope.resume_type;
        self.resume_return_type = scope.resume_return_type;
        result
    }
}

/// Build a canonical dotted name by joining a parent path with a child segment.
///
/// Used wherever the typechecker mints canonical names: `Module.Item`,
/// `Module.Trait.method`, `Module.Effect.op`. Centralizes the join convention
/// so all callers agree on separator and ordering.
pub fn canonical_join(parent: &str, child: &str) -> String {
    format!("{}.{}", parent, child)
}

/// Extract all effect names from a type by walking Fun nodes' effect rows.
pub fn effects_from_type(ty: &Type) -> HashSet<String> {
    let mut effects = HashSet::new();
    fn walk(ty: &Type, out: &mut HashSet<String>) {
        if let Type::Fun(_, ret, row) = ty {
            for entry in &row.effects {
                out.insert(entry.name.clone());
            }
            walk(ret, out);
        }
    }
    walk(ty, &mut effects);
    effects
}

/// Collect exact effect entries from a callback parameter type's effect rows.
/// For `() -> a needs {Fail String, Log}`, collects those concrete entries.
/// Only collects statically declared row entries (not row variables).
pub fn collect_callback_effect_entries(ty: &Type, out: &mut Vec<EffectEntry>) {
    if let Type::Fun(_, ret, row) = ty {
        for entry in &row.effects {
            if !out.iter().any(|seen| seen.same_instantiation(entry)) {
                out.push(entry.clone());
            }
        }
        collect_callback_effect_entries(ret, out);
    }
}

/// Collect effect names from a callback parameter type's effect rows.
/// For `() -> a needs {Fail, Log}`, collects `{"Fail", "Log"}`.
/// Only collects from closed-row effects (not row variables).
pub fn collect_callback_effects(ty: &Type, out: &mut HashSet<String>) {
    if let Type::Fun(_, ret, row) = ty {
        for entry in &row.effects {
            out.insert(entry.name.clone());
        }
        collect_callback_effects(ret, out);
    }
}

// Re-export from unify module so other files can use `super::collect_free_vars`
pub(crate) use unify::collect_free_vars;
use unify::rename_vars;
