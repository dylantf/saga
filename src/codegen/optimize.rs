//! Post-classifier optimizer facts.
//!
//! This phase is deliberately metadata-first. It records facts that lowering
//! may consume for narrow fast paths, while default lowering remains correct
//! when no optimization fact is present.

use crate::ast::{self, Decl, Expr, Pat};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct HelperFact {
    pub params: Vec<Pat>,
    pub body: Expr,
    pub source_module: String,
}

#[derive(Clone, Debug, Default)]
pub struct OptimizationFacts {
    pub handler_analysis: super::handler_analysis::HandlerAnalysis,
    /// Single-clause helper bodies. Importing modules filter these through
    /// `ModuleCodegenInfo.exports` before considering cross-module variants;
    /// the optimizer fact pass runs after elaboration/normalization, where
    /// source `pub` signatures are no longer the best publicness authority.
    pub public_helpers: HashMap<String, HelperFact>,
}

pub fn analyze(
    module_name: &str,
    program: &ast::Program,
    _resolution: &super::resolve::ResolutionMap,
) -> OptimizationFacts {
    OptimizationFacts {
        handler_analysis: super::handler_analysis::analyze(program),
        public_helpers: collect_public_helper_facts(module_name, program),
    }
}

fn source_module_name(module_name: &str, program: &ast::Program) -> String {
    program
        .iter()
        .find_map(|decl| match decl {
            Decl::ModuleDecl { path, .. } => Some(path.join(".")),
            _ => None,
        })
        .unwrap_or_else(|| module_name.to_string())
}

fn helper_params_supported(params: &[Pat]) -> bool {
    params.iter().all(|param| {
        matches!(
            param,
            Pat::Var { .. }
                | Pat::Wildcard { .. }
                | Pat::Lit {
                    value: ast::Lit::Unit,
                    ..
                }
        )
    })
}

fn collect_public_helper_facts(
    module_name: &str,
    program: &ast::Program,
) -> HashMap<String, HelperFact> {
    let source_module = source_module_name(module_name, program);
    let mut seen: HashSet<String> = HashSet::new();
    let mut duplicate_names: HashSet<String> = HashSet::new();
    let mut helpers = HashMap::new();

    for decl in program {
        let Decl::FunBinding {
            name,
            params,
            guard,
            body,
            ..
        } = decl
        else {
            continue;
        };
        if !seen.insert(name.clone()) {
            duplicate_names.insert(name.clone());
            helpers.remove(name);
            helpers.remove(&format!("{}.{}", source_module, name));
            continue;
        }
        if guard.is_some() || !helper_params_supported(params) {
            continue;
        }

        let fact = HelperFact {
            params: params.clone(),
            body: body.clone(),
            source_module: source_module.clone(),
        };
        helpers.insert(name.clone(), fact.clone());
        helpers.insert(format!("{}.{}", source_module, name), fact);
    }

    for name in duplicate_names {
        helpers.remove(&name);
        helpers.remove(&format!("{}.{}", source_module, name));
    }

    helpers
}
