pub mod cerl;
pub mod lower;
pub mod normalize;
#[cfg(test)]
mod tests;

use crate::ast;
use crate::typechecker::ModuleCodegenInfo;
use std::collections::HashMap;

/// Bundles the cross-module information needed by the lowerer.
#[derive(Default)]
pub struct CodegenContext {
    /// Codegen info for imported modules (from typechecker).
    pub codegen_info: HashMap<String, ModuleCodegenInfo>,
    /// Elaborated programs per module (for cross-module handler lookup).
    pub elaborated_modules: HashMap<String, ast::Program>,
    /// Deferred effects for let bindings that partially apply effectful functions.
    pub let_effect_bindings: HashMap<String, Vec<String>>,
}

pub fn emit_module(module_name: &str, program: &ast::Program) -> String {
    let ctx = CodegenContext::default();
    emit_module_with_context(module_name, program, &ctx)
}

pub fn emit_module_with_context(
    module_name: &str,
    program: &ast::Program,
    ctx: &CodegenContext,
) -> String {
    let program = normalize::normalize_effects(program);
    let cmod = lower::Lowerer::new(ctx).lower_module(module_name, &program);
    cerl::print_module(&cmod)
}
