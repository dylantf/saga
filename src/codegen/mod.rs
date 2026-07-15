pub mod call_effects;
pub mod cerl;
pub mod generic_fold;
pub mod handler_analysis;
pub mod lower;
pub mod normalize;
pub mod optimize;
pub mod resolve;
pub mod runtime_shape;
#[cfg(test)]
mod tests;
pub mod trait_dispatch;

use crate::ast;
use crate::typechecker::ModuleCodegenInfo;
use std::collections::HashMap;
use std::time::Instant;

fn build_trace_enabled() -> bool {
    std::env::var_os("SAGA_BUILD_TRACE").is_some()
}

fn trace_codegen_phase(module: &str, phase: &str, duration: std::time::Duration) {
    if build_trace_enabled() {
        eprintln!(
            "[saga-codegen] module={} phase={} elapsed={:.1}ms",
            module,
            phase,
            duration.as_secs_f64() * 1000.0
        );
    }
}

fn timed_codegen_phase<T>(module: &str, phase: &str, f: impl FnOnce() -> T) -> T {
    if !build_trace_enabled() {
        return f();
    }
    let start = Instant::now();
    let out = f();
    trace_codegen_phase(module, phase, start.elapsed());
    out
}

/// Result of compiling a single module: codegen metadata, elaborated AST,
/// and pre-computed name resolution.
#[derive(Clone, Default)]
pub struct CompiledModule {
    pub codegen_info: std::sync::Arc<ModuleCodegenInfo>,
    pub elaborated: ast::Program,
    pub resolution: resolve::ResolutionMap,
    /// Front-end name resolution from the typechecker.
    pub front_resolution: crate::typechecker::ResolutionResult,
    /// Exact applied effect selected for effect calls and handler arms.
    pub effect_at_node: HashMap<ast::NodeId, crate::typechecker::EffectEntry>,
    /// Resolved expression types used when lowering imported handler bodies.
    pub type_at_node: HashMap<ast::NodeId, crate::typechecker::Type>,
    /// Resolved binding/pattern types used by contextual ABI planning inside
    /// imported handler bodies.
    pub type_at_span: HashMap<crate::token::Span, crate::typechecker::Type>,
    /// NodeId-keyed callable ABI metadata produced by the effect-ABI pre-pass.
    /// Keeping calls and function values together is required for imported
    /// handler bodies and other cross-module lowering paths.
    pub effect_abi_plan: call_effects::EffectAbiPlan,
    /// True when `effect_abi_plan` has deliberately been populated. An empty
    /// plan is valid for modules without calls or function values.
    pub effect_abi_plan_ready: bool,
    /// Post-classifier optimizer facts for this module. Empty facts mean
    /// lowering should take the normal direct-first/evidence path.
    pub optimization: optimize::OptimizationFacts,
}

pub struct ModuleSemantics<'a> {
    pub codegen_info: &'a ModuleCodegenInfo,
    pub elaborated: &'a ast::Program,
    pub resolution: &'a resolve::ResolutionMap,
    pub front_resolution: &'a crate::typechecker::ResolutionResult,
    pub effect_at_node: &'a HashMap<ast::NodeId, crate::typechecker::EffectEntry>,
    pub type_at_node: &'a HashMap<ast::NodeId, crate::typechecker::Type>,
    pub type_at_span: &'a HashMap<crate::token::Span, crate::typechecker::Type>,
    pub optimization: &'a optimize::OptimizationFacts,
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

/// Per-build emit indexes derived from a `CodegenContext`.
///
/// These are intentionally separate from `CodegenContext`: the Generic-fold
/// external maps borrow module ASTs and resolution maps from `ctx.modules`, so
/// storing them inside the owning context would be self-referential.
pub struct PreparedEmitContext<'a> {
    pub ctx: &'a CodegenContext,
    pub codegen_info: HashMap<String, std::sync::Arc<ModuleCodegenInfo>>,
    pub external_ctors: generic_fold::ExternalCtors<'a>,
    pub external_funs: generic_fold::ExternalFuns<'a>,
    pub module_resolution: resolve::ResolutionMap,
}

impl CodegenContext {
    /// Get codegen info for all modules (for backward compat with resolve/init).
    pub fn codegen_info(&self) -> HashMap<String, std::sync::Arc<ModuleCodegenInfo>> {
        self.modules
            .iter()
            .map(|(k, v)| (k.clone(), std::sync::Arc::clone(&v.codegen_info)))
            .collect()
    }

    pub fn prepare_emit(&self) -> PreparedEmitContext<'_> {
        let module_resolution = self
            .modules
            .values()
            .flat_map(|compiled| compiled.resolution.iter().map(|(k, v)| (*k, v.clone())))
            .collect();
        PreparedEmitContext {
            ctx: self,
            codegen_info: self.codegen_info(),
            external_ctors: generic_fold::external_ctors_from_modules(&self.modules),
            external_funs: generic_fold::external_funs_from_modules(&self.modules),
            module_resolution,
        }
    }

    /// Get elaborated program for a specific module.
    pub fn elaborated_module(&self, name: &str) -> Option<&ast::Program> {
        self.modules.get(name).map(|m| &m.elaborated)
    }

    pub fn module_semantics(&self, name: &str) -> Option<ModuleSemantics<'_>> {
        self.modules.get(name).map(|m| ModuleSemantics {
            codegen_info: m.codegen_info.as_ref(),
            elaborated: &m.elaborated,
            resolution: &m.resolution,
            front_resolution: &m.front_resolution,
            effect_at_node: &m.effect_at_node,
            type_at_node: &m.type_at_node,
            type_at_span: &m.type_at_span,
            optimization: &m.optimization,
        })
    }

    pub fn modules_semantics(&self) -> impl Iterator<Item = (&str, ModuleSemantics<'_>)> + '_ {
        self.modules.iter().map(|(name, m)| {
            (
                name.as_str(),
                ModuleSemantics {
                    codegen_info: m.codegen_info.as_ref(),
                    elaborated: &m.elaborated,
                    resolution: &m.resolution,
                    front_resolution: &m.front_resolution,
                    effect_at_node: &m.effect_at_node,
                    type_at_node: &m.type_at_node,
                    type_at_span: &m.type_at_span,
                    optimization: &m.optimization,
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
    // Local-only fold here (no cross-module context); the cross-module fold runs
    // at emit, which re-folds with `ctx.modules` supplied.
    let normalized = generic_fold::fold_program(
        &normalize::normalize_effects(&elaborated),
        &generic_fold::ExternalCtors::new(),
        &generic_fold::ExternalFuns::new(),
    )
    .program;
    let resolution = resolve::resolve_names(
        module_name,
        &normalized,
        codegen_info,
        &result.prelude_imports,
        &mod_result.resolution,
        &HashMap::new(),
    );
    let optimization = optimize::analyze(module_name, &normalized, &resolution);
    Some(CompiledModule {
        codegen_info: info,
        elaborated: normalized,
        resolution,
        front_resolution: mod_result.resolution.clone(),
        effect_at_node: mod_result.effect_at_node.clone(),
        type_at_node: mod_result.type_at_node.clone(),
        type_at_span: mod_result.type_at_span.clone(),
        effect_abi_plan: call_effects::EffectAbiPlan::default(),
        effect_abi_plan_ready: false,
        optimization,
    })
}

pub fn precompute_context_call_effects(
    ctx: &mut CodegenContext,
    result: &crate::typechecker::CheckResult,
) {
    let module_names: Vec<String> = ctx.modules.keys().cloned().collect();
    let computed: Vec<(String, call_effects::EffectAbiPlan)> = module_names
        .into_iter()
        .filter_map(|module_name| {
            let compiled = ctx.modules.get(&module_name)?;
            if compiled.effect_abi_plan_ready {
                return None;
            }
            if module_name == "Main" {
                return Some((module_name, call_effects::EffectAbiPlan::default()));
            }
            let check_result = result
                .module_check_results()
                .get(&module_name)
                .map(|module_result| module_result.as_ref())
                .unwrap_or(result);
            let effect_abi_plan =
                timed_codegen_phase(&module_name, "precompute_call_effects", || {
                    lower::precompute_call_effects(
                        ctx,
                        &module_name,
                        &compiled.elaborated,
                        compiled.resolution.clone(),
                        check_result,
                    )
                });
            Some((module_name, effect_abi_plan))
        })
        .collect();

    for (module_name, effect_abi_plan) in computed {
        if let Some(compiled) = ctx.modules.get_mut(&module_name) {
            compiled.effect_abi_plan = effect_abi_plan;
            compiled.effect_abi_plan_ready = true;
        }
    }
}

/// Source file path and source text for error location tracking.
pub struct SourceFile {
    /// Relative path to the source file (e.g. "src/server.saga").
    pub path: String,
    /// Full source text (used to compute line numbers).
    pub source: String,
}

pub fn emit_module_with_context(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
    check_result: &crate::typechecker::CheckResult,
    source_file: Option<&SourceFile>,
    entry_export: Option<&str>,
) -> String {
    let prepared = timed_codegen_phase(module_name, "prepare_emit_context", || ctx.prepare_emit());
    emit_module_with_prepared_context(
        module_name,
        program,
        &prepared,
        check_result,
        source_file,
        entry_export,
    )
}

pub fn emit_module_with_prepared_context(
    module_name: &str,
    program: &ast::Program,
    prepared: &PreparedEmitContext<'_>,
    check_result: &crate::typechecker::CheckResult,
    source_file: Option<&SourceFile>,
    entry_export: Option<&str>,
) -> String {
    let ctx = prepared.ctx;
    // Generic fold, with cross-module impls supplied from the other compiled
    // modules. Inlined cross-module nodes carry the producer's resolution, merged
    // below after `resolve_names`.
    let normalized = timed_codegen_phase(module_name, "normalize_effects", || {
        normalize::normalize_effects(program)
    });
    let fold_out = timed_codegen_phase(module_name, "generic_fold_cross_module", || {
        generic_fold::fold_program(
            &normalized,
            &prepared.external_ctors,
            &prepared.external_funs,
        )
    });
    let generic_fold::FoldOutput {
        program,
        carried_resolution,
        carried_record_types,
        carried_constructors,
        carried_constructor_names,
        carried_names,
    } = fold_out;
    let constructor_atoms = timed_codegen_phase(module_name, "build_constructor_atoms", || {
        resolve::build_constructor_atoms(
            module_name,
            &program,
            &prepared.codegen_info,
            &ctx.prelude_imports,
        )
    });
    let front_resolution = check_result
        .module_check_results()
        .get(module_name)
        .map(|m| &m.resolution)
        .unwrap_or(&check_result.resolution);
    let mut resolution_map = timed_codegen_phase(module_name, "resolve_codegen_names", || {
        resolve::resolve_names(
            module_name,
            &program,
            &prepared.codegen_info,
            &ctx.prelude_imports,
            front_resolution,
            &carried_names,
        )
    });
    // Merge in pre-computed resolution maps from all compiled modules.
    // Their NodeIds don't overlap with ours, so this is a simple extend.
    timed_codegen_phase(module_name, "merge_module_resolution", || {
        resolution_map.extend(
            prepared
                .module_resolution
                .iter()
                .map(|(id, symbol)| (*id, symbol.clone())),
        );
    });
    // Carried resolution for inlined cross-module nodes: keyed by fresh NodeIds,
    // so this overrides any consumer-scope resolution `resolve_names` guessed for
    // them (e.g. a producer-private helper unknown in this module's scope).
    timed_codegen_phase(module_name, "merge_carried_resolution", || {
        resolution_map.extend(carried_resolution);
    });
    let optimization = timed_codegen_phase(module_name, "analyze_optimization", || {
        optimize::analyze(module_name, &program, &resolution_map)
    });
    let source_info = timed_codegen_phase(module_name, "build_source_info", || {
        source_file.map(|sf| lower::errors::SourceInfo::new(sf.path.clone(), &sf.source))
    });
    let cmod = timed_codegen_phase(module_name, "lower_module", || {
        lower::Lowerer::new(
            ctx,
            constructor_atoms,
            lower::LowererResolution {
                symbols: resolution_map,
                carried_record_types,
                carried_constructors,
                carried_constructor_names,
            },
            check_result,
            optimization,
            source_info,
            entry_export.map(str::to_string),
        )
        .lower_module(module_name, &program)
    });
    timed_codegen_phase(module_name, "print_core", || cerl::print_module(&cmod))
}
