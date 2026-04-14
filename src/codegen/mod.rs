pub mod cerl;
pub mod lower;
pub mod normalize;
pub mod resolve;
#[cfg(test)]
mod tests;

use crate::ast;
use crate::typechecker::ModuleCodegenInfo;
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

    pub fn modules_semantics(
        &self,
    ) -> impl Iterator<Item = (&str, ModuleSemantics<'_>)> + '_ {
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
    let normalized = normalize::normalize_effects(&elaborated);
    let resolution = resolve::resolve_names(
        module_name,
        &normalized,
        codegen_info,
        &result.prelude_imports,
        &mod_result.resolution,
    );
    Some(CompiledModule {
        codegen_info: info,
        elaborated: normalized,
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

pub fn emit_module_with_context(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
    check_result: &crate::typechecker::CheckResult,
    source_file: Option<&SourceFile>,
    entry_export: Option<&str>,
) -> String {
    let codegen_info = ctx.codegen_info();
    let program = normalize::normalize_effects(program);
    let constructor_atoms = resolve::build_constructor_atoms(
        module_name,
        &program,
        &codegen_info,
        &ctx.prelude_imports,
    );
    let front_resolution = check_result
        .module_check_results()
        .get(module_name)
        .map(|m| &m.resolution)
        .unwrap_or(&check_result.resolution);
    let mut resolution_map = resolve::resolve_names(
        module_name,
        &program,
        &codegen_info,
        &ctx.prelude_imports,
        front_resolution,
    );
    // Merge in pre-computed resolution maps from all compiled modules.
    // Their NodeIds don't overlap with ours, so this is a simple extend.
    for compiled in ctx.modules.values() {
        resolution_map.extend(compiled.resolution.iter().map(|(k, v)| (*k, v.clone())));
    }
    let source_info =
        source_file.map(|sf| lower::errors::SourceInfo::new(sf.path.clone(), &sf.source));
    let cmod = lower::Lowerer::new(
        ctx,
        constructor_atoms,
        resolution_map,
        check_result,
        source_info,
        entry_export.map(str::to_string),
    )
    .lower_module(module_name, &program);
    cerl::print_module(&cmod)
}
