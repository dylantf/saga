pub mod anf;
pub mod cerl;
pub mod external;
pub mod handler_analysis;
pub mod lower;
pub mod monadic;
pub mod native_effects;
pub mod resolve;
pub mod runtime_shape;
mod source_spans;
#[cfg(test)]
mod tests;
pub mod type_shape;

use crate::ast;
use crate::compiler_options::{CompileOptions, MonadicStatsMode};
use crate::typechecker::{CheckResult, ModuleCodegenInfo};
use std::collections::HashMap;

/// Result of compiling a single module: codegen metadata, elaborated AST,
/// and pre-computed name resolution.
#[derive(Clone, Default)]
pub struct CompiledModule {
    pub codegen_info: ModuleCodegenInfo,
    pub elaborated: ast::Program,
    pub resolution: resolve::ResolutionMap,
    /// Front-end name resolution from the typechecker.
    pub front_resolution: crate::typechecker::ResolutionResult,
}

pub struct ModuleSemantics<'a> {
    pub codegen_info: &'a ModuleCodegenInfo,
    pub elaborated: &'a ast::Program,
    pub resolution: &'a resolve::ResolutionMap,
    pub front_resolution: &'a crate::typechecker::ResolutionResult,
}

/// Bundles the cross-module information needed by the lowerer.
#[derive(Default)]
pub struct CodegenContext {
    /// All compiled modules (Std + user), keyed by module name.
    pub modules: HashMap<String, CompiledModule>,
    /// Deferred effects for let bindings that partially apply effectful functions.
    pub let_effect_bindings: HashMap<String, Vec<String>>,
    /// Import declarations from the prelude, so the resolver knows
    /// which stdlib names are actually in scope for user code.
    pub prelude_imports: Vec<ast::Decl>,
}

impl CodegenContext {
    /// Get codegen info for all modules (for backward compat with resolve/init).
    pub fn codegen_info(&self) -> HashMap<String, ModuleCodegenInfo> {
        self.modules
            .iter()
            .map(|(k, v)| (k.clone(), v.codegen_info.clone()))
            .collect()
    }

    /// Get elaborated program for a specific module.
    pub fn elaborated_module(&self, name: &str) -> Option<&ast::Program> {
        self.modules.get(name).map(|m| &m.elaborated)
    }

    pub fn module_semantics(&self, name: &str) -> Option<ModuleSemantics<'_>> {
        self.modules.get(name).map(|m| ModuleSemantics {
            codegen_info: &m.codegen_info,
            elaborated: &m.elaborated,
            resolution: &m.resolution,
            front_resolution: &m.front_resolution,
        })
    }

    pub fn modules_semantics(&self) -> impl Iterator<Item = (&str, ModuleSemantics<'_>)> + '_ {
        self.modules.iter().map(|(name, m)| {
            (
                name.as_str(),
                ModuleSemantics {
                    codegen_info: &m.codegen_info,
                    elaborated: &m.elaborated,
                    resolution: &m.resolution,
                    front_resolution: &m.front_resolution,
                },
            )
        })
    }
}

/// Compile a single module from a CheckResult into a CompiledModule.
/// Used by the build pipeline and integration tests.
pub fn compile_module_from_result(
    module_name: &str,
    result: &crate::typechecker::CheckResult,
) -> Option<CompiledModule> {
    let program = result.programs().get(module_name)?;
    let mod_result = result.module_check_results().get(module_name)?;
    let codegen_info = result.codegen_info();
    let info = codegen_info.get(module_name).cloned().unwrap_or_default();
    let elaborated = crate::elaborate::elaborate_module(program, mod_result, module_name);

    // Store the raw elaborated AST. ANF runs at emit time inside
    // `emit_module_with_context`, and backend resolution is keyed to the same
    // raw elaborated NodeIds.
    let resolution = resolve::resolve_names(
        module_name,
        &elaborated,
        codegen_info,
        &result.prelude_imports,
        &mod_result.resolution,
    );
    let stored = elaborated;

    Some(CompiledModule {
        codegen_info: info,
        elaborated: stored,
        resolution,
        front_resolution: mod_result.resolution.clone(),
    })
}

/// Source file path and source text for error location tracking.
pub struct SourceFile {
    /// Relative path to the source file (e.g. "src/server.saga").
    pub path: String,
    /// Full source text (used to compute line numbers).
    pub source: String,
}

pub struct EmitModuleOutput {
    pub core_src: String,
    pub monadic_stats: Option<monadic::stats::StatsReport>,
}

pub fn emit_module_with_context(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
    check_result: &crate::typechecker::CheckResult,
    source_file: Option<&SourceFile>,
    entry_export: Option<&str>,
) -> String {
    emit_module_with_context_options(
        module_name,
        program,
        ctx,
        check_result,
        source_file,
        entry_export,
        &CompileOptions::default(),
    )
    .core_src
}

pub fn emit_module_with_context_options(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
    check_result: &crate::typechecker::CheckResult,
    source_file: Option<&SourceFile>,
    entry_export: Option<&str>,
    options: &CompileOptions,
) -> EmitModuleOutput {
    // The uniform path consumes the raw elaborated AST, runs ANF + monadic
    // translation + effect optimization, then lowers via
    // `lower::Lowerer`. Bootstrap evidence emission is on only for
    // the entry-point module (`entry_export.is_some()`).
    emit_module_via_new_path(
        module_name,
        program,
        ctx,
        check_result,
        source_file,
        entry_export,
        options,
    )
}

// -------------------------------------------------------------------------
// New-path helpers (Phase 1, step 8)
// -------------------------------------------------------------------------

/// Storage for the narrowed [`monadic::ir::EffectInfo`] view's
/// `effect_ops` field. The view itself borrows; this struct owns the
/// underlying map so the borrow stays alive for the duration of one
/// emit.
pub struct EffectOpsTable {
    pub map: HashMap<String, Vec<String>>,
}

fn insert_effect_ops_entry(
    map: &mut HashMap<String, Vec<String>>,
    name: &str,
    source_module: Option<&str>,
    ops: Vec<String>,
) {
    map.insert(name.to_string(), ops.clone());
    let bare = name.rsplit('.').next().unwrap_or(name);
    if bare != name {
        map.entry(bare.to_string()).or_insert_with(|| ops.clone());
    }
    if let Some(src_mod) = source_module {
        let canonical = format!("{}.{}", src_mod, bare);
        if canonical != name {
            map.insert(canonical, ops);
        }
    }
}

fn insert_module_effect_defs(
    map: &mut HashMap<String, Vec<String>>,
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
) {
    for info in codegen_info.values() {
        for effect_def in &info.effect_defs {
            let mut ops: Vec<String> = effect_def.ops.iter().map(|op| op.name.clone()).collect();
            ops.sort();
            let source_module = effect_def.name.rsplit_once('.').map(|(module, _)| module);
            insert_effect_ops_entry(map, &effect_def.name, source_module, ops);
        }
    }
}

/// Build the canonical effect-name → ops list from `CheckResult.effects`.
/// Both the bare effect name and the fully-qualified `Module.Name` form
/// are inserted so callers can look up by either spelling.
pub fn build_effect_ops_table(check_result: &CheckResult) -> EffectOpsTable {
    let mut map: HashMap<String, Vec<String>> = HashMap::new();
    for (name, info) in &check_result.effects {
        let mut ops: Vec<String> = info.ops.iter().map(|op| op.name.clone()).collect();
        ops.sort();
        // `check_result.effects` may key by either bare (`Stdio`) or canonical
        // (`Std.IO.Stdio`) names depending on where the entry was inserted
        // (see `check_decl.rs:2219` for the canonical branch). Insert under
        // both spellings so downstream lookups succeed either way, but avoid
        // re-prepending the source module to a name that already contains it
        // — `format!("Std.IO.{}", "Std.IO.Stdio")` would produce
        // `Std.IO.Std.IO.Stdio` and poison the canonical lookup.
        insert_effect_ops_entry(&mut map, name, info.source_module.as_deref(), ops);
    }

    // Imported/dependency effect definitions may be visible through module
    // metadata without being present in the entry module's `effects` map. The
    // translator needs the same op-index table for those cross-module effects.
    insert_module_effect_defs(&mut map, check_result.codegen_info());
    EffectOpsTable { map }
}

/// Build the narrowed [`monadic::ir::EffectInfo`] view from a
/// `CheckResult` plus per-module `ResolutionResult`.
///
/// All fields are borrowed from the inputs except `effect_ops`, which is
/// synthesized into `ops_storage` and then borrowed back into the view.
/// The caller owns `ops_storage` and must keep it alive while the view
/// is in use.
pub fn build_effect_info<'a>(
    check_result: &'a CheckResult,
    module_check_result: &'a CheckResult,
    ops_storage: &'a EffectOpsTable,
    handler_effects_storage: &'a HashMap<String, Vec<String>>,
    let_handler_effects_storage: &'a HashMap<ast::NodeId, Vec<String>>,
) -> monadic::ir::EffectInfo<'a> {
    monadic::ir::EffectInfo {
        effect_calls: &module_check_result.resolution.effect_calls,
        handler_arms: &module_check_result.resolution.handler_arms,
        constructors: &module_check_result.resolution.constructors,
        fun_effects: &check_result.fun_effects,
        let_effect_bindings: &check_result.let_effect_bindings,
        type_at_node: &check_result.type_at_node,
        records: &check_result.records,
        effect_ops: &ops_storage.map,
        handler_effects: handler_effects_storage,
        handler_refs: &module_check_result.resolution.handlers,
        let_handler_effects: let_handler_effects_storage,
    }
}

/// Build handler name → effects mapping from `CheckResult.handlers`.
pub fn build_handler_effects(check_result: &CheckResult) -> HashMap<String, Vec<String>> {
    check_result
        .handlers
        .iter()
        .map(|(name, info)| (name.clone(), info.effects.clone()))
        .collect()
}

/// Build pattern NodeId → effects mapping from `CheckResult.let_binding_handlers`.
pub fn build_let_handler_effects(check_result: &CheckResult) -> HashMap<ast::NodeId, Vec<String>> {
    check_result
        .let_binding_handlers
        .iter()
        .map(|(id, info)| (*id, info.effects.clone()))
        .collect()
}

/// New-path emit. Sequence:
///   a. resolution_map = resolve::resolve_names(module_name, raw_elaborated, …)
///   b. effect_info  = build_effect_info(check_result, module_check_result)
///   c. handler_info = handler_analysis::analyze(raw_elaborated)
///   d. anf_program  = anf::normalize(raw_elaborated.clone())
///   e. monadic      = monadic::translate(&anf_program, &resolution_map, &effect_info)
///   f. optimized    = monadic::effect_opt::run(monadic, &handler_info, &effect_info)
///   g. cmod         = lower::Lowerer::new(…)
///                         .with_bootstrap_emission(entry_export.is_some())
///                         .lower_module(module_name, &optimized)
///   h. cerl::print_module(&cmod)
///
/// `program` should be the raw elaborated AST (no `normalize_effects`
/// applied). Bootstrap emission is on iff `entry_export.is_some()` — the
/// only module the build pipeline passes an entry-export name to is the
/// designated entry-point module.
pub fn emit_module_via_new_path(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
    check_result: &crate::typechecker::CheckResult,
    source_file: Option<&SourceFile>,
    entry_export: Option<&str>,
    options: &CompileOptions,
) -> EmitModuleOutput {
    let _ = entry_export; // currently consumed only via is_main below
    let codegen_info = ctx.codegen_info();
    let constructor_atoms =
        resolve::build_constructor_atoms(module_name, program, &codegen_info, &ctx.prelude_imports);
    let front_resolution = check_result
        .module_check_results()
        .get(module_name)
        .map(|m| &m.resolution)
        .unwrap_or(&check_result.resolution);
    let mut resolution_map = resolve::resolve_names(
        module_name,
        program,
        &codegen_info,
        &ctx.prelude_imports,
        front_resolution,
    );
    for compiled in ctx.modules.values() {
        resolution_map.extend(compiled.resolution.iter().map(|(k, v)| (*k, v.clone())));
    }

    // Effect info: build the ops table once (borrowed by the view).
    let mut ops_storage = build_effect_ops_table(check_result);
    insert_module_effect_defs(&mut ops_storage.map, &codegen_info);
    // Per-module CheckResult yields the per-module ResolutionResult that
    // carries effect_calls / handler_arms. Script/test contexts (no module
    // registered) fall back to the top-level check_result.
    let mod_check_ref: &CheckResult = check_result
        .module_check_results()
        .get(module_name)
        .unwrap_or(check_result);
    let mut combined_effect_calls = mod_check_ref.resolution.effect_calls.clone();
    let mut combined_handler_arms = mod_check_ref.resolution.handler_arms.clone();
    let combined_handler_refs = mod_check_ref.resolution.handlers.clone();
    let mut combined_constructors = mod_check_ref.resolution.constructors.clone();
    for compiled in ctx.modules.values() {
        combined_effect_calls.extend(
            compiled
                .front_resolution
                .effect_calls
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        combined_handler_arms.extend(
            compiled
                .front_resolution
                .handler_arms
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        combined_constructors.extend(
            compiled
                .front_resolution
                .constructors
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
    }
    let handler_effects_storage = build_handler_effects(check_result);
    let let_handler_effects_storage = build_let_handler_effects(check_result);
    let effect_info = monadic::ir::EffectInfo {
        effect_calls: &combined_effect_calls,
        handler_arms: &combined_handler_arms,
        constructors: &combined_constructors,
        fun_effects: &check_result.fun_effects,
        let_effect_bindings: &check_result.let_effect_bindings,
        type_at_node: &check_result.type_at_node,
        records: &check_result.records,
        effect_ops: &ops_storage.map,
        handler_effects: &handler_effects_storage,
        handler_refs: &combined_handler_refs,
        let_handler_effects: &let_handler_effects_storage,
    };

    let mut handler_info = handler_analysis::analyze(program);
    let anf_program = anf::normalize(program.clone(), Some(&resolution_map));
    // Collect imported handler bodies so `with <imported_handler>` translates
    // to `Static` (arms inlined) instead of falling back to `Dynamic` with an
    // empty effect list — the lowerer's Dynamic path requires a concrete
    // effect tag for `insert_canonical`.
    //
    // Imported `elaborated` programs are NOT ANF-normalized (each module was
    // ANF'd at its own emit time but the result isn't persisted), so we
    // re-ANF each before extracting handler bodies — the translator expects
    // every reachable expression (including inlined handler arm bodies) to
    // satisfy the ANF atomicity invariant.
    let mut imported_handler_decls: HashMap<String, ast::HandlerBody> = HashMap::new();
    let mut imported_function_variants = HashMap::new();
    let mut imported_handler_factories = HashMap::new();
    let mut imported_dict_constructors = HashMap::new();
    for (imported_module_name, compiled) in &ctx.modules {
        let anf_imported = anf::normalize(compiled.elaborated.clone(), Some(&compiled.resolution));
        for decl in &anf_imported {
            if let ast::Decl::HandlerDef { name, body, .. } = decl {
                imported_handler_decls
                    .entry(name.clone())
                    .or_insert_with(|| body.clone());
                for canonical in &compiled.codegen_info.handler_defs {
                    if canonical.rsplit('.').next() == Some(name.as_str()) {
                        imported_handler_decls
                            .entry(canonical.clone())
                            .or_insert_with(|| body.clone());
                    }
                }
            }
        }
        if imported_module_name != module_name {
            handler_info
                .resumption
                .extend(handler_analysis::analyze(&compiled.elaborated).resumption);
            let (imported_monadic, _) =
                monadic::translate::translate(&anf_imported, &compiled.resolution, &effect_info);
            imported_function_variants.extend(
                monadic::effect_opt::collect_imported_function_variant_candidates(
                    imported_module_name,
                    &imported_monadic,
                    &compiled.resolution,
                    &compiled.codegen_info,
                ),
            );
            imported_handler_factories.extend(
                monadic::effect_opt::collect_imported_handler_factory_candidates(
                    imported_module_name,
                    &imported_monadic,
                    &compiled.resolution,
                    &compiled.codegen_info,
                ),
            );
            imported_dict_constructors.extend(
                monadic::effect_opt::collect_imported_dict_constructors(
                    imported_module_name,
                    &imported_monadic,
                    &compiled.resolution,
                    &compiled.codegen_info,
                ),
            );
        }
    }
    let (monadic_prog, handler_value_map) = monadic::translate::translate_with_imports(
        &anf_program,
        &resolution_map,
        &effect_info,
        &imported_handler_decls,
    );
    let before_stats = options
        .diagnostics
        .monadic_stats
        .is_enabled()
        .then(|| monadic_prog.clone());
    let optimized = monadic::effect_opt::run_with_context(
        monadic_prog,
        &handler_info,
        &effect_info,
        monadic::effect_opt::OptimizerContext {
            resolution: resolution_map.clone(),
            imported_function_variants,
            imported_handler_factories,
            imported_dict_constructors,
        },
    );
    let monadic_stats = before_stats.map(|before_program| {
        let before = monadic::stats::Stats::collect_program(&before_program);
        let after = monadic::stats::Stats::collect_program(&optimized);
        let roots = entry_export.into_iter().collect::<Vec<_>>();
        let reachable = if roots.is_empty() {
            None
        } else {
            let before_reachable =
                monadic::stats::Stats::collect_reachable_program(&before_program, &roots);
            let after_reachable =
                monadic::stats::Stats::collect_reachable_program(&optimized, &roots);
            (before_reachable.decls > 0 || after_reachable.decls > 0)
                .then(|| monadic::stats::StatsDiff::new(before_reachable, after_reachable))
        };
        monadic::stats::StatsReport::with_module_graph(
            monadic::stats::StatsDiff::new(before, after),
            reachable,
            &before_program,
            &optimized,
            &resolution_map,
        )
    });

    let is_main = entry_export.is_some();
    let mut lowerer = lower::Lowerer::new(
        &resolution_map,
        &constructor_atoms,
        ctx,
        &handler_info,
        &effect_info,
        &handler_value_map,
    );
    if let Some(source_file) = source_file {
        let source_spans = source_spans::for_program(&anf_program, &check_result.node_spans);
        lowerer = lowerer.with_source_info(lower::SourceInfo::new(
            source_file.path.clone(),
            &source_file.source,
            source_spans,
        ));
    }
    let cmod = lowerer
        .with_bootstrap_emission(is_main)
        .lower_module(module_name, &optimized);
    let core_src = cerl::print_module(&cmod);
    match options.diagnostics.monadic_stats {
        MonadicStatsMode::Off => EmitModuleOutput {
            core_src,
            monadic_stats: None,
        },
        MonadicStatsMode::Summary | MonadicStatsMode::Full => EmitModuleOutput {
            core_src,
            monadic_stats,
        },
    }
}
