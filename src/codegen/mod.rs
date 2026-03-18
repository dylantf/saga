pub mod cerl;
pub mod lower;
pub mod normalize;
#[cfg(test)]
mod tests;

use crate::ast;
use crate::token::Span;
use crate::typechecker::ModuleCodegenInfo;
use std::collections::{HashMap, HashSet};

pub fn emit_module(module_name: &str, program: &ast::Program) -> String {
    emit_module_with_imports(module_name, program, &HashMap::new(), &HashMap::new(), &HashMap::new())
}

pub fn emit_module_with_imports(
    module_name: &str,
    program: &ast::Program,
    codegen_info: &HashMap<String, ModuleCodegenInfo>,
    elaborated_modules: &HashMap<String, ast::Program>,
    with_reachable_ops: &HashMap<Span, (HashSet<String>, bool)>,
) -> String {
    let program = normalize::normalize_effects(program);
    let cmod =
        lower::Lowerer::new(codegen_info, elaborated_modules, with_reachable_ops).lower_module(module_name, &program);
    cerl::print_module(&cmod)
}
