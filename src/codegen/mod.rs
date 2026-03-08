pub mod cerl;
pub mod lower;
#[cfg(test)]
mod tests;

use crate::ast;

pub fn emit_module(module_name: &str, program: &ast::Program) -> String {
    let cmod = lower::Lowerer::new().lower_module(module_name, program);
    cerl::print_module(&cmod)
}
