pub mod anf;
pub mod cerl;
pub(crate) mod ets_tables;
pub mod external;
pub mod handler_analysis;
pub mod lower;
pub mod lower_selective;
pub mod monadic;
pub mod native_effects;
pub mod resolve;
pub mod runtime_shape;
mod source_spans;
#[cfg(test)]
mod tests;
pub mod type_shape;

use crate::ast;
use crate::compiler_options::CompileOptions;
use crate::typechecker::{CheckResult, ModuleCodegenInfo};
use std::collections::{HashMap, HashSet};

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
    // The selective path consumes the raw elaborated AST, runs ANF + monadic
    // translation once, lowers direct-first selective Core, and overlays it on
    // the raw monadic fallback unless `--selective-no-fallback` is enabled.
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

fn declared_module_name(program: &ast::Program) -> Option<String> {
    program.iter().find_map(|decl| match decl {
        ast::Decl::ModuleDecl { path, .. } => Some(path.join(".")),
        _ => None,
    })
}

fn program_imports_module(program: &ast::Program, module_name: &str) -> bool {
    program.iter().any(|decl| {
        matches!(
            decl,
            ast::Decl::Import { module_path, .. }
                if module_path.join(".") == module_name
        )
    })
}

fn resolution_references_module(resolution: &resolve::ResolutionMap, module_name: &str) -> bool {
    resolution
        .values()
        .any(|resolved| resolved.source_module.as_deref() == Some(module_name))
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
        traits: &check_result.traits,
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

/// Selective emit. Sequence:
///   a. resolution_map = resolve::resolve_names(module_name, raw_elaborated, …)
///   b. effect_info  = build_effect_info(check_result, module_check_result)
///   c. handler_info = handler_analysis::analyze(raw_elaborated)
///   d. anf_program  = anf::normalize(raw_elaborated.clone())
///   e. monadic      = monadic::translate(&anf_program, &resolution_map, &effect_info)
///   f. selective    = lower_selective::lower_module(…)
///   g. fallback     = lower::Lowerer::new(…).lower_module(module_name, &monadic)
///   h. cmod         = merge(fallback, selective), unless fallback is disabled
///   i. cerl::print_module(&cmod)
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
    let source_module_name =
        declared_module_name(program).unwrap_or_else(|| module_name.to_string());
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
        traits: &check_result.traits,
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
        if imported_module_name != &source_module_name
            && (program_imports_module(program, imported_module_name)
                || resolution_references_module(&resolution_map, imported_module_name))
        {
            handler_info
                .resumption
                .extend(handler_analysis::analyze(&compiled.elaborated).resumption);
            let (imported_monadic, _) =
                monadic::translate::translate(&anf_imported, &compiled.resolution, &effect_info);
            let imported_private = lower_selective::collect_imported_private_helper_candidates(
                imported_module_name,
                &imported_monadic,
                &compiled.resolution,
                &compiled.codegen_info,
            );
            let imported_private_names = imported_private
                .values()
                .map(|binding| binding.name.clone())
                .collect::<std::collections::HashSet<_>>();
            imported_dict_constructors.extend(lower_selective::collect_imported_dict_constructors(
                imported_module_name,
                &imported_monadic,
                &compiled.resolution,
                &compiled.codegen_info,
                &imported_private_names,
            ));
        }
    }
    let imported_dict_constructors = if source_module_name.starts_with("Std.") {
        HashMap::new()
    } else {
        imported_dict_constructors
    };
    let (monadic_prog, handler_value_map) = monadic::translate::translate_with_imports(
        &anf_program,
        &resolution_map,
        &effect_info,
        &imported_handler_decls,
    );

    let selective_cmod = lower_selective::lower_module_with_entry_export_and_imported_dicts(
        module_name,
        &monadic_prog,
        &resolution_map,
        &constructor_atoms,
        ctx,
        &handler_info,
        &effect_info,
        entry_export,
        &handler_value_map,
        imported_dict_constructors.clone(),
        lower_selective::LoweringOptions {
            require_all_functions: options.selective_no_fallback,
        },
    );
    let cmod = if options.selective_no_fallback {
        selective_cmod
    } else {
        let mut fallback_lowerer = lower::Lowerer::new(
            &resolution_map,
            &constructor_atoms,
            ctx,
            &handler_info,
            &effect_info,
            &handler_value_map,
        );
        if let Some(source_file) = source_file {
            let source_spans = source_spans::for_program(&anf_program, &check_result.node_spans);
            fallback_lowerer = fallback_lowerer.with_source_info(lower::SourceInfo::new(
                source_file.path.clone(),
                &source_file.source,
                source_spans,
            ));
        }
        let fallback_cmod = fallback_lowerer
            .with_bootstrap_emission(entry_export.is_some())
            .lower_module(module_name, &monadic_prog);
        let fallback_direct_adapters =
            selective_fallback_direct_adapters(&monadic_prog, &effect_info);
        merge_selective_core_modules(fallback_cmod, selective_cmod, &fallback_direct_adapters)
    };
    EmitModuleOutput {
        core_src: cerl::print_module(&cmod),
    }
}

fn merge_selective_core_modules(
    fallback: cerl::CModule,
    selective: cerl::CModule,
    direct_adapters: &HashMap<String, DirectFallbackAdapter>,
) -> cerl::CModule {
    let fallback_exports: HashSet<(String, usize)> = fallback.exports.iter().cloned().collect();

    let mut funs: Vec<cerl::CFunDef> = fallback
        .funs
        .into_iter()
        .map(|fun| {
            fallback_duplicate_dict_source(&selective.name, &fun.name, direct_adapters)
                .and_then(|(source_name, adapter)| {
                    build_duplicate_dict_alias(&fun.name, fun.arity, &source_name, adapter)
                })
                .unwrap_or(fun)
        })
        .collect();
    let mut fun_indexes: HashMap<(String, usize), usize> = funs
        .iter()
        .enumerate()
        .map(|(index, fun)| ((fun.name.clone(), fun.arity), index))
        .collect();
    let fallback_fun_keys: HashSet<(String, usize)> = fun_indexes.keys().cloned().collect();

    for fun in selective.funs {
        let key = (fun.name.clone(), fun.arity);
        if let Some(index) = fun_indexes.get(&key).copied() {
            funs[index] = fun;
        } else {
            fun_indexes.insert(key, funs.len());
            funs.push(fun);
        }
    }

    let mut exports = Vec::new();
    let mut export_seen = HashSet::new();
    for export in fallback.exports {
        push_export(&mut exports, &mut export_seen, export);
    }
    for export in selective.exports {
        push_export(&mut exports, &mut export_seen, export);
    }

    for (name, adapter) in direct_adapters {
        let direct_key = (name.clone(), adapter.direct_arity());
        let fallback_key = (name.clone(), adapter.uniform_arity());
        if !fallback_fun_keys.contains(&fallback_key) || fun_indexes.contains_key(&direct_key) {
            continue;
        }
        let adapter = build_direct_fallback_adapter(name, adapter);
        fun_indexes.insert(direct_key.clone(), funs.len());
        funs.push(adapter);
        if fallback_exports.contains(&fallback_key) {
            push_export(&mut exports, &mut export_seen, direct_key);
        }
    }

    cerl::CModule {
        name: selective.name,
        exports,
        funs,
    }
}

fn fallback_duplicate_dict_source<'a>(
    module_name: &str,
    fallback_name: &str,
    direct_adapters: &'a HashMap<String, DirectFallbackAdapter>,
) -> Option<(String, &'a DirectFallbackAdapter)> {
    if !fallback_name.starts_with("__dict_") {
        return None;
    }

    let erlang_module = erlang_module_name_for_core(module_name);
    let marker = format!("_{erlang_module}");
    let marker_index = fallback_name.find(&marker)?;
    let mut source_name = fallback_name.to_string();
    source_name.replace_range(marker_index..marker_index + marker.len(), "");

    let adapter = direct_adapters.get(&source_name)?;
    matches!(adapter, DirectFallbackAdapter::Dict { .. }).then_some((source_name, adapter))
}

fn build_duplicate_dict_alias(
    fallback_name: &str,
    arity: usize,
    source_name: &str,
    adapter: &DirectFallbackAdapter,
) -> Option<cerl::CFunDef> {
    let direct_arity = adapter.direct_arity();
    if arity == direct_arity {
        let params: Vec<String> = (0..direct_arity)
            .map(|index| format!("_DictAliasArg{index}"))
            .collect();
        let args = params.iter().cloned().map(cerl::CExpr::Var).collect();
        return Some(cerl::CFunDef {
            name: fallback_name.to_string(),
            arity,
            body: cerl::CExpr::Fun(
                params,
                Box::new(cerl::CExpr::Apply(
                    Box::new(cerl::CExpr::FunRef(source_name.to_string(), direct_arity)),
                    args,
                )),
            ),
        });
    }

    if arity == adapter.uniform_arity() {
        let direct_params: Vec<String> = (0..direct_arity)
            .map(|index| format!("_DictAliasArg{index}"))
            .collect();
        let evidence = "_DictAliasEvidence".to_string();
        let return_k = "_DictAliasK".to_string();
        let mut params = direct_params.clone();
        params.push(evidence);
        params.push(return_k.clone());
        let direct_args = direct_params
            .iter()
            .cloned()
            .map(cerl::CExpr::Var)
            .collect();
        let direct_call = cerl::CExpr::Apply(
            Box::new(cerl::CExpr::FunRef(source_name.to_string(), direct_arity)),
            direct_args,
        );
        return Some(cerl::CFunDef {
            name: fallback_name.to_string(),
            arity,
            body: cerl::CExpr::Fun(
                params,
                Box::new(cerl::CExpr::Apply(
                    Box::new(cerl::CExpr::Var(return_k)),
                    vec![direct_call],
                )),
            ),
        });
    }

    None
}

fn erlang_module_name_for_core(module_name: &str) -> String {
    module_name
        .split('.')
        .map(str::to_lowercase)
        .collect::<Vec<_>>()
        .join("_")
}

#[derive(Clone)]
enum DirectFallbackAdapter {
    Function {
        source_arity: usize,
    },
    Dict {
        constructor: monadic::ir::MDictConstructor,
    },
}

impl DirectFallbackAdapter {
    fn direct_arity(&self) -> usize {
        match self {
            Self::Function { source_arity } => *source_arity,
            Self::Dict { constructor } => constructor.dict_params.len(),
        }
    }

    fn uniform_arity(&self) -> usize {
        self.direct_arity() + 2
    }
}

fn selective_fallback_direct_adapters(
    program: &monadic::ir::MProgram,
    effect_info: &monadic::ir::EffectInfo<'_>,
) -> HashMap<String, DirectFallbackAdapter> {
    let mut adapters = HashMap::new();
    for decl in program {
        match decl {
            monadic::ir::MDecl::FunBinding(fb)
                if effect_info
                    .fun_effects
                    .get(&fb.name)
                    .is_some_and(|effects| effects.is_empty()) =>
            {
                adapters
                    .entry(fb.name.clone())
                    .or_insert(DirectFallbackAdapter::Function {
                        source_arity: fb.params.len(),
                    });
            }
            monadic::ir::MDecl::DictConstructor(dc) => {
                adapters.insert(
                    dc.name.clone(),
                    DirectFallbackAdapter::Dict {
                        constructor: dc.clone(),
                    },
                );
            }
            monadic::ir::MDecl::FunBinding(_)
            | monadic::ir::MDecl::Val(_)
            | monadic::ir::MDecl::Passthrough(_) => {}
        }
    }
    adapters
}

fn push_export(
    exports: &mut Vec<(String, usize)>,
    seen: &mut HashSet<(String, usize)>,
    export: (String, usize),
) {
    if seen.insert(export.clone()) {
        exports.push(export);
    }
}

fn build_direct_fallback_adapter(name: &str, adapter: &DirectFallbackAdapter) -> cerl::CFunDef {
    match adapter {
        DirectFallbackAdapter::Function { source_arity } => {
            build_direct_function_fallback_adapter(name, *source_arity)
        }
        DirectFallbackAdapter::Dict { constructor } => {
            build_direct_dict_fallback_adapter(constructor)
        }
    }
}

fn build_direct_function_fallback_adapter(name: &str, direct_arity: usize) -> cerl::CFunDef {
    let params: Vec<String> = (0..direct_arity)
        .map(|index| format!("_DictArg{index}"))
        .collect();
    let mut args: Vec<cerl::CExpr> = params.iter().cloned().map(cerl::CExpr::Var).collect();
    args.push(cerl::CExpr::Tuple(vec![]));
    args.push(identity_continuation("_DictResult"));
    let body = cerl::CExpr::Apply(
        Box::new(cerl::CExpr::FunRef(name.to_string(), direct_arity + 2)),
        args,
    );
    cerl::CFunDef {
        name: name.to_string(),
        arity: direct_arity,
        body: cerl::CExpr::Fun(params, Box::new(body)),
    }
}

fn build_direct_dict_fallback_adapter(dc: &monadic::ir::MDictConstructor) -> cerl::CFunDef {
    let params = dc.dict_params.clone();
    let mut fallback_args: Vec<cerl::CExpr> =
        params.iter().cloned().map(cerl::CExpr::Var).collect();
    fallback_args.push(cerl::CExpr::Tuple(vec![]));
    fallback_args.push(identity_continuation("_DictResult"));
    let fallback_var = "_FallbackDict".to_string();
    let fallback_dict = cerl::CExpr::Apply(
        Box::new(cerl::CExpr::FunRef(
            dc.name.clone(),
            dc.dict_params.len() + 2,
        )),
        fallback_args,
    );
    let methods = dc
        .methods
        .iter()
        .enumerate()
        .map(|(index, method)| {
            let old_method = cerl::CExpr::Call(
                "erlang".to_string(),
                "element".to_string(),
                vec![
                    cerl::CExpr::Lit(cerl::CLit::Int((index + 1) as i64)),
                    cerl::CExpr::Var(fallback_var.clone()),
                ],
            );
            if dc
                .method_effects
                .get(index)
                .is_some_and(|effects| !effects.is_empty())
                || dc.method_open_rows.get(index).copied().unwrap_or(false)
            {
                return old_method;
            }

            let monadic::ir::MExpr::Pure(monadic::ir::Atom::Lambda { params, .. }) = method else {
                panic!("dict fallback adapter expected lambda method");
            };
            let method_params: Vec<String> = (0..params.len())
                .map(|arg_index| format!("_Method{index}Arg{arg_index}"))
                .collect();
            let mut args: Vec<cerl::CExpr> = method_params
                .iter()
                .cloned()
                .map(cerl::CExpr::Var)
                .collect();
            args.push(cerl::CExpr::Tuple(vec![]));
            args.push(identity_continuation("_MethodResult"));
            cerl::CExpr::Fun(
                method_params,
                Box::new(cerl::CExpr::Apply(Box::new(old_method), args)),
            )
        })
        .collect();
    let body = cerl::CExpr::Let(
        fallback_var,
        Box::new(fallback_dict),
        Box::new(cerl::CExpr::Tuple(methods)),
    );
    cerl::CFunDef {
        name: dc.name.clone(),
        arity: dc.dict_params.len(),
        body: cerl::CExpr::Fun(params, Box::new(body)),
    }
}

fn identity_continuation(param: &str) -> cerl::CExpr {
    cerl::CExpr::Fun(
        vec![param.to_string()],
        Box::new(cerl::CExpr::Var(param.to_string())),
    )
}
