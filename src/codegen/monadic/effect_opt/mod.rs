// effect_opt/ — monadic IR optimization stage.
//
// Currently a no-op identity (step 6). Filled in by:
//   - step 9:  bind_collapse.rs   — Bind(Pure(a), x, B) → B[x := a]
//   - step 10: bind_to_let.rs     — Bind → Let where value is pure
//   - step 11: direct_call.rs     — tail-resumptive Yield → inlined arm body
//
// See docs/planning/uniform-effect-translation/effect-optimization-spec.md
// for rewrite specifications, soundness conditions, and fixpoint
// strategy. The orchestrator below is identity; when the three
// rewrites land it becomes a shared bottom-up fixpoint loop.

use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{EffectInfo, MProgram};

/// Run the effect-optimization stage with default options.
pub fn run(m: MProgram, h: &HandlerAnalysis, e: &EffectInfo) -> MProgram {
    run_with_options(m, h, e, RunOptions::default())
}

/// Run the effect-optimization stage with caller-supplied options.
///
/// With the optimizer as identity, both `run` and `run_with_options`
/// return `m` unchanged. The shape is in place for the spec's
/// "skip Pass 3" debug switch.
pub fn run_with_options(
    m: MProgram,
    _h: &HandlerAnalysis,
    _e: &EffectInfo,
    _opts: RunOptions,
) -> MProgram {
    m
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RunOptions {
    /// Emit no-op even after rewrites land. Useful for benchmarking and
    /// bisecting miscompiles between the translator and the optimizer.
    pub skip: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::monadic::ir::MProgram;
    use crate::typechecker::ResolvedEffectOp;
    use std::collections::{HashMap, HashSet};

    struct Fixture {
        h: HandlerAnalysis,
        effect_calls: HashMap<crate::ast::NodeId, ResolvedEffectOp>,
        handler_arms: HashMap<crate::ast::NodeId, ResolvedEffectOp>,
        fun_effects: HashMap<String, HashSet<String>>,
        let_effect_bindings: HashMap<String, Vec<String>>,
        type_at_node: HashMap<crate::ast::NodeId, crate::typechecker::Type>,
        effect_ops: HashMap<String, Vec<String>>,
    }

    impl Fixture {
        fn new() -> Self {
            Self {
                h: HandlerAnalysis::default(),
                effect_calls: HashMap::new(),
                handler_arms: HashMap::new(),
                fun_effects: HashMap::new(),
                let_effect_bindings: HashMap::new(),
                type_at_node: HashMap::new(),
                effect_ops: HashMap::new(),
            }
        }

        fn info(&self) -> EffectInfo<'_> {
            EffectInfo {
                effect_calls: &self.effect_calls,
                handler_arms: &self.handler_arms,
                fun_effects: &self.fun_effects,
                let_effect_bindings: &self.let_effect_bindings,
                type_at_node: &self.type_at_node,
                effect_ops: &self.effect_ops,
            }
        }
    }

    #[test]
    fn run_is_identity() {
        let f = Fixture::new();
        let info = f.info();
        let prog: MProgram = vec![];
        assert_eq!(run(prog.clone(), &f.h, &info), prog);
    }

    #[test]
    fn run_with_options_identity_both_toggles() {
        let f = Fixture::new();
        let info = f.info();
        let prog: MProgram = vec![];
        assert_eq!(
            run_with_options(prog.clone(), &f.h, &info, RunOptions { skip: true }),
            prog
        );
        assert_eq!(
            run_with_options(prog.clone(), &f.h, &info, RunOptions { skip: false }),
            prog
        );
    }

    #[test]
    fn mprogram_default_smoke() {
        let prog: MProgram = MProgram::default();
        assert!(prog.is_empty());
    }
}
