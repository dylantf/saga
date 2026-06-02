// effect_opt/ — monadic IR optimization stage.
//
// Currently implements steps 9-11:
//   - bind collapse — Bind(Pure(a), x, B) → B[x := a]
//   - Bind→Let promotion — non-yielding binders become direct lets
//   - dead pure-let cleanup — remove unused pure lets
//   - step 11: direct_call.rs     — tail-resumptive Yield → inlined arm body
//
// See docs/planning/uniform-effect-translation/effect-optimization-spec.md
// for rewrite specifications, soundness conditions, and fixpoint strategy.

use crate::ast::{
    ComprehensionQualifier, Expr, ExprKind, Handler, HandlerItem, Pat, Stmt, StringPart,
};
use crate::codegen::handler_analysis::{HandlerAnalysis, ResumptionKind};
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, MArm, MDecl, MDictConstructor, MExpr, MFunBinding, MHandler, MHandlerArm,
    MProgram, MVal, MVar,
};
use crate::codegen::native_effects::{NativeArgTransform, native_op};
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use crate::codegen::type_shape;
use crate::typechecker::ModuleCodegenInfo;
use std::collections::{HashMap, HashSet};

/// Run the effect-optimization stage with default options.
pub fn run(m: MProgram, h: &HandlerAnalysis, e: &EffectInfo) -> MProgram {
    run_with_options(m, h, e, RunOptions::default())
}

/// Run the effect-optimization stage with caller-supplied options.
///
/// With `skip`, this returns the monadic program unchanged. Otherwise it runs
/// the currently-enabled optimizer rewrites.
pub fn run_with_options(
    m: MProgram,
    h: &HandlerAnalysis,
    _e: &EffectInfo,
    opts: RunOptions,
) -> MProgram {
    run_with_options_and_context(m, h, _e, opts, OptimizerContext::default())
}

pub fn run_with_context(
    m: MProgram,
    h: &HandlerAnalysis,
    e: &EffectInfo,
    context: OptimizerContext,
) -> MProgram {
    run_with_options_and_context(m, h, e, RunOptions::default(), context)
}

pub fn run_with_options_and_context(
    m: MProgram,
    h: &HandlerAnalysis,
    _e: &EffectInfo,
    opts: RunOptions,
    context: OptimizerContext,
) -> MProgram {
    if opts.skip {
        return m;
    }

    let mut optimizer = Optimizer::new(opts, h, _e, context);
    optimizer.optimize_program(m)
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RunOptions {
    /// Emit no-op even after rewrites land. Useful for benchmarking and
    /// bisecting miscompiles between the translator and the optimizer.
    pub skip: bool,
}

#[derive(Debug, Clone, Default)]
pub struct OptimizerContext {
    pub current_module: Option<String>,
    pub resolution: ResolutionMap,
    pub imported_function_variants: HashMap<String, ImportedFunctionVariantCandidate>,
    pub imported_handler_factories: HashMap<String, ImportedHandlerFactoryCandidate>,
    pub imported_dict_constructors: HashMap<String, MDictConstructor>,
    pub imported_private_helpers: HashMap<String, ImportedPrivateHelperCandidate>,
}

#[derive(Debug, Clone)]
pub struct ImportedFunctionVariantCandidate {
    pub source_module: String,
    pub binding: MFunBinding,
    pub public_names: HashSet<String>,
}

#[derive(Debug, Clone)]
pub struct ImportedHandlerFactoryCandidate {
    pub source_module: String,
    pub params: Vec<Pat>,
    pub body: MExpr,
}

#[derive(Debug, Clone)]
pub struct ImportedPrivateHelperCandidate {
    pub source_module: String,
    pub binding: MFunBinding,
}

struct Optimizer<'info, 'data> {
    opts: RunOptions,
    context: OptimizerContext,
    handler_analysis: &'info HandlerAnalysis,
    effect_info: &'info EffectInfo<'data>,
    handler_stack: Vec<HandlerFrame>,
    handler_value_bindings: Vec<(String, Option<HandlerValueCandidate>)>,
    dict_value_bindings: Vec<(String, Option<DictValueCandidate>)>,
    dict_method_bindings: Vec<(String, Option<InlineCandidate>)>,
    pure_atom_bindings: Vec<(String, Option<Atom>)>,
    inline_candidates: HashMap<String, InlineCandidate>,
    handler_factory_candidates: HashMap<String, InlineCandidate>,
    dict_constructors: HashMap<String, MDictConstructor>,
    variant_candidates: HashMap<String, VariantCandidate>,
    generated_variant_names: HashSet<String>,
    in_progress_private_helpers: HashSet<String>,
    pending_variants: Vec<MDecl>,
    inline_blocked_names: Vec<String>,
}

#[derive(Debug, Clone)]
enum HandlerFrame {
    Static {
        effects: Vec<String>,
        arms: Vec<MHandlerArm>,
    },
    Native {
        effects: Vec<String>,
        handler: String,
    },
    Blocking {
        effects: Vec<String>,
    },
}

impl HandlerFrame {
    fn effects(&self) -> &[String] {
        match self {
            HandlerFrame::Static { effects, .. }
            | HandlerFrame::Native { effects, .. }
            | HandlerFrame::Blocking { effects } => effects,
        }
    }

    fn handles_effect(&self, effect: &str) -> bool {
        self.effects()
            .iter()
            .any(|frame_effect| effect_names_match(frame_effect, effect))
    }
}

#[derive(Debug, Clone)]
struct InlineCandidate {
    params: Vec<Pat>,
    body: MExpr,
}

#[derive(Debug, Clone)]
struct HandlerValueCandidate {
    effects: Vec<String>,
    arms: Vec<MHandlerArm>,
    return_clause: Option<Box<MHandlerArm>>,
    source: crate::ast::NodeId,
}

#[derive(Debug, Clone)]
struct HandlerFactoryPrefixBinding {
    var: MVar,
    value: MExpr,
    mode: Option<crate::codegen::monadic::ir::BindMode>,
}

#[derive(Debug, Clone)]
struct VariantCandidate {
    binding: MFunBinding,
}

#[derive(Debug, Clone)]
struct DictValueCandidate {
    atom: Atom,
    methods: Vec<Atom>,
    key: String,
}

#[derive(Debug, Clone)]
struct DictParamReplacement {
    target: MVar,
    replacement: Atom,
    key: String,
}

#[derive(Debug, Clone)]
struct ValueParamReplacement {
    target: MVar,
    replacement: Atom,
    key: String,
}

#[derive(Debug, Clone)]
struct CallbackParamReplacement {
    target: MVar,
    candidate: InlineCandidate,
    key: String,
    captures: Vec<String>,
}

#[derive(Debug, Clone, Copy)]
struct VariantSpecializations<'a> {
    dict: &'a [DictParamReplacement],
    values: &'a [ValueParamReplacement],
    callbacks: &'a [CallbackParamReplacement],
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct EffectSummary {
    erasable_yields: usize,
    residual_yields: usize,
    summarized_calls: usize,
    blockers: usize,
}

impl EffectSummary {
    fn add_assign(&mut self, other: Self) {
        self.erasable_yields += other.erasable_yields;
        self.residual_yields += other.residual_yields;
        self.summarized_calls += other.summarized_calls;
        self.blockers += other.blockers;
    }

    fn has_specialization_opportunity(&self) -> bool {
        self.erasable_yields > 0 || self.summarized_calls > 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Change {
    Unchanged,
    Changed,
}

impl Change {
    fn mark_if(&mut self, other: Change) {
        if other == Change::Changed {
            *self = Change::Changed;
        }
    }
}

#[derive(Debug)]
struct SubstOutcome<T> {
    value: T,
    changed: bool,
    blocked: bool,
}

impl<T> SubstOutcome<T> {
    fn unchanged(value: T) -> Self {
        Self {
            value,
            changed: false,
            blocked: false,
        }
    }

    fn changed(value: T) -> Self {
        Self {
            value,
            changed: true,
            blocked: false,
        }
    }

    fn blocked(value: T) -> Self {
        Self {
            value,
            changed: false,
            blocked: true,
        }
    }
}

impl RunOptions {
    fn bind_collapse(self) -> bool {
        !self.skip
    }

    fn bind_to_let(self) -> bool {
        !self.skip
    }

    fn direct_call(self) -> bool {
        !self.skip
    }

    fn handler_value_specialization(self) -> bool {
        !self.skip
    }

    fn handler_factory_inline(self) -> bool {
        !self.skip
    }

    fn native_direct_call(self) -> bool {
        !self.skip
    }

    fn helper_inline(self) -> bool {
        !self.skip
    }

    fn native_function_variants(self) -> bool {
        !self.skip
    }

    fn static_function_variants(self) -> bool {
        !self.skip
    }

    fn dead_pure_let(self) -> bool {
        !self.skip
    }

    fn dead_pure_with(self) -> bool {
        !self.skip
    }
}

fn optimize_optional_expr_with(
    optimizer: &mut Optimizer,
    expr: Option<MExpr>,
) -> (Option<MExpr>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr(expr);
            (Some(expr), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn optimize_optional_expr_with_blocked_names(
    optimizer: &mut Optimizer,
    expr: Option<MExpr>,
    names: Vec<String>,
) -> (Option<MExpr>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr_with_blocked_names(names, expr);
            (Some(expr), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn optimize_optional_boxed_expr_with_blocked_names(
    optimizer: &mut Optimizer,
    expr: Option<Box<MExpr>>,
    names: Vec<String>,
) -> (Option<Box<MExpr>>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr_with_blocked_names(names, *expr);
            (Some(Box::new(expr)), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn optimize_optional_atom_with(
    optimizer: &mut Optimizer,
    atom: Option<Atom>,
) -> (Option<Atom>, Change) {
    match atom {
        Some(atom) => {
            let (atom, change) = optimizer.optimize_atom(atom);
            (Some(atom), change)
        }
        None => (None, Change::Unchanged),
    }
}

mod analysis;
mod collect;
mod direct;
mod names;
mod native;
mod optimizer;
mod patterns;
mod rewrite;
mod shape;
mod subst;

use analysis::*;
use collect::*;
use direct::*;
use names::*;
use native::*;
use patterns::*;
use rewrite::*;
use shape::*;
use subst::*;

pub use collect::{
    collect_imported_dict_constructors, collect_imported_function_variant_candidates,
    collect_imported_handler_factory_candidates, collect_imported_private_helper_candidates,
};
pub(crate) use names::is_generated_variant_name;

#[cfg(test)]
mod tests;
