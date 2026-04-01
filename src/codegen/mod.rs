pub mod cerl;
pub mod lower;
pub mod normalize;
pub mod resolve;
#[cfg(test)]
mod tests;

use crate::ast;
use crate::typechecker::ModuleCodegenInfo;
use crate::typechecker::Type;
use std::collections::HashMap;

/// Result of compiling a single module: codegen metadata, elaborated AST,
/// and pre-computed name resolution.
#[derive(Clone, Default)]
pub struct CompiledModule {
    pub codegen_info: ModuleCodegenInfo,
    pub elaborated: ast::Program,
    pub resolution: resolve::ResolutionMap,
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

}

pub fn emit_module(module_name: &str, program: &ast::Program) -> String {
    let ctx = CodegenContext::default();
    emit_module_with_context(module_name, program, &ctx, HashMap::new(), None)
}

/// Source file path and source text for error location tracking.
pub struct SourceFile {
    /// Relative path to the source file (e.g. "src/server.dy").
    pub path: String,
    /// Full source text (used to compute line numbers).
    pub source: String,
}

pub fn emit_module_with_context(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
    current_resolved_types: HashMap<ast::NodeId, Type>,
    source_file: Option<&SourceFile>,
) -> String {
    let codegen_info = ctx.codegen_info();
    let program = normalize::normalize_effects(program);
    let constructor_atoms = resolve::build_constructor_atoms(
        module_name,
        &program,
        &codegen_info,
        &ctx.prelude_imports,
    );
    let mut resolution_map = resolve::resolve_names(&program, &codegen_info, &ctx.prelude_imports);
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
        current_resolved_types,
        source_info,
    )
        .lower_module(module_name, &program);
    cerl::print_module(&cmod)
}
