pub mod cerl;
pub mod lower;
pub mod normalize;
#[cfg(test)]
mod tests;

use crate::ast;

pub fn emit_module(module_name: &str, program: &ast::Program) -> String {
    let program = normalize::normalize_effects(program);
    let cmod = lower::Lowerer::new().lower_module(module_name, &program);
    cerl::print_module(&cmod)
}
