//! Post-classifier optimizer facts.
//!
//! This phase is deliberately metadata-first. It records facts that lowering
//! may consume for narrow fast paths, while default lowering remains correct
//! when no optimization fact is present.

use crate::ast;

#[derive(Clone, Debug, Default)]
pub struct OptimizationFacts {
    pub handler_analysis: super::handler_analysis::HandlerAnalysis,
}

pub fn analyze(
    _module_name: &str,
    program: &ast::Program,
    _resolution: &super::resolve::ResolutionMap,
) -> OptimizationFacts {
    OptimizationFacts {
        handler_analysis: super::handler_analysis::analyze(program),
    }
}
