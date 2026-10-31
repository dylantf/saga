pub(crate) mod beam_interop;
mod anf;
mod build;
mod builtins;
mod calls;
mod effects;
pub mod errors;
mod evidence;
mod exprs;
mod function_values;
mod hof;
pub(crate) mod init;
mod module;
mod pats;
mod semantic;
mod static_helpers;
mod tagged;
mod trait_spec_stats;
pub mod util;

use crate::ast::{self, Expr, ExprKind, HandlerArm, Lit, NodeId, Pat};
use crate::codegen::call_effects::CallEffectInfo;
use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::runtime_shape::CallableAbi;
use crate::typechecker::TraitInfo;
use std::collections::HashMap;

use errors::{ErrorInfo, ErrorKind, SourceInfo};
pub(super) use evidence::EvidenceFrame;
pub(crate) use tagged::consumed_arrows_effectful as tagged_consumed_arrows_effectful;
use util::{cerl_call, core_var, lower_string_to_binary};

pub(super) type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);

/// A perform-site frame captured by an operation callback, and the effects
/// the callback's parameter type names.
pub(super) type CapturedCallbackEvidence = (EvidenceFrame, Vec<String>);

/// Lower a simple expression used as a bitstring segment size.
/// Handles integer literals and variable references — the common cases
/// for pattern-position sizes like `<<len:8, data:len/binary>>`.
pub(crate) fn lower_size_expr(expr: &Expr) -> CExpr {
    match &expr.kind {
        ExprKind::Lit {
            value: Lit::Int(_, n),
            ..
        } => CExpr::Lit(CLit::Int(*n)),
        ExprKind::Var { name, .. } => CExpr::Var(core_var(name)),
        _ => unreachable!("bitstring segment size must be an integer literal or variable"),
    }
}

#[derive(Clone)]
pub(crate) struct StaticTailResumeOp {
    arm: HandlerArm,
    source_module: Option<String>,
    effect_name: Option<String>,
    captures: Vec<(String, Expr)>,
}

/// Stored handler definition for CPS inlining at `with` sites.
#[derive(Clone)]
pub(crate) struct HandlerInfo {
    effects: Vec<String>,
    arms: Vec<HandlerArm>,
    return_clause: Option<Box<HandlerArm>>,
    /// The module this handler was defined in (e.g. "Std.Actor").
    /// Used to identify BEAM-native handlers that need special lowering.
    source_module: Option<String>,
    /// Simple factory argument captures recovered at a let-bound handler value.
    captures: Vec<(String, Expr)>,
}

#[derive(Clone)]
struct HandlerFactoryInfo {
    params: Vec<String>,
    body: crate::ast::HandlerBody,
    source_module: Option<String>,
}

#[derive(Clone)]
struct LocalHelperInfo {
    params: Vec<Pat>,
    body: Expr,
    source_module: String,
}

struct GeneratedHelperVariant {
    name: String,
    arity: usize,
    body: CExpr,
}

/// A trait impl method hoisted out of its dict tuple into a top-level function,
/// so statically-known dispatch sites can call it directly instead of building
/// the dict tuple and extracting via `element/2` (Phase 2 trait specialization).
/// Keyed by `(dict_constructor_name, method_index)`. Only local, nullary
/// (non-parameterized) dicts are hoisted, so the method body captures nothing.
#[derive(Clone)]
struct HoistedDictMethod {
    /// Generated top-level function name (e.g. `__saga_dictmethod_<dict>_<idx>`).
    fn_name: String,
    /// User-argument arity of the method (excludes `_Evidence`/`_ReturnK`).
    /// Used to require a saturated call site before specializing.
    user_arity: usize,
    /// Whether the method's runtime ABI is CPS (`user_arity + 2` params).
    is_cps: bool,
}

struct GeneratedHofVariant {
    name: String,
    arity: usize,
    body: CExpr,
    export: bool,
}

#[derive(Clone)]
struct DirectHofValueBinding {
    specialization: super::optimize::HofDirectSpecialization,
    source_module: Option<String>,
}

/// Stored effect definition: maps op_name -> lowering metadata.
struct EffectInfo {
    ops: HashMap<String, EffectOpInfo>,
}

#[derive(Debug, Clone, Default)]
struct EffectOpInfo {
    /// Source-level parameter count before erasing `Unit` placeholders.
    source_param_count: usize,
    /// Runtime parameter count after erasing `Unit` placeholders.
    runtime_param_count: usize,
    /// Indices of source params that survive runtime erasure.
    runtime_param_positions: Vec<usize>,
    /// For callback parameters, the effects absorbed by that parameter.
    param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// Callback parameters with an open effect row. Kept separately because
    /// an open-only row has no named effects in `param_absorbed_effects`.
    param_open_rows: std::collections::HashSet<usize>,
    /// Dictionary parameter names for the operation's own `where` constraints
    /// (e.g. `set : a -> Unit where {a: PgType}` yields `["__dict_PgType_a"]`).
    /// These are threaded as trailing op arguments at each call site and bound
    /// as trailing closure params in the handler arm (before the continuation).
    dict_param_names: Vec<String>,
}

/// CPS metadata for a top-level function. Used by the lowerer to determine
/// how to thread evidence and return continuations through effectful calls.
/// This is NOT name resolution -- name resolution is handled by the
/// ResolutionMap. FunInfo only tracks arity/effects needed for CPS
/// transformation.
#[derive(Debug, Clone, Default)]
struct FunInfo {
    /// The single runtime calling convention for this function. Compatibility
    /// registration still receives expanded arity/effect parts, but they are
    /// normalized into this value immediately.
    abi: crate::codegen::runtime_shape::CallableAbi,
    /// For EffArrow params: param_index -> absorbed effects. Used to inject
    /// evidence threading into lambdas passed to effectful higher-order
    /// functions.
    param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// Number of dictionary arguments prepended by elaboration for `where`
    /// clauses. These runtime arguments are not present in the source-level
    /// function type, so expected user parameter types start after this offset.
    dict_param_count: usize,
}

impl FunInfo {
    fn from_abi(
        abi: crate::codegen::runtime_shape::CallableAbi,
        param_absorbed_effects: HashMap<usize, Vec<String>>,
        dict_param_count: usize,
    ) -> Self {
        Self {
            abi,
            param_absorbed_effects,
            dict_param_count,
        }
    }

    fn arity(&self) -> usize {
        self.abi.expanded_arity()
    }

    fn effects(&self) -> &[String] {
        self.abi
            .evidence
            .as_ref()
            .map_or(&[], |evidence| evidence.static_slots())
    }

    fn is_open_row(&self) -> bool {
        self.abi
            .evidence
            .as_ref()
            .is_some_and(crate::codegen::runtime_shape::EvidenceAbi::is_open)
    }
}

#[derive(Default)]
pub(super) struct LowererResolution {
    pub(super) symbols: super::resolve::ResolutionMap,
    pub(super) origins: super::generic_fold::NodeOrigins,
    pub(super) carried_record_types: HashMap<crate::ast::NodeId, String>,
    pub(super) carried_constructors: HashMap<crate::ast::NodeId, String>,
    pub(super) carried_constructor_names: HashMap<String, String>,
}

/// Previous handler-binding entries for one name; see `handler_binding_undo`.
type HandlerBindingUndo = (
    String,
    Option<String>,
    Option<(String, CExpr, String, String)>,
    Option<(String, Vec<String>, bool)>,
);

pub struct Lowerer<'a> {
    counter: usize,
    /// Numbers the temporaries effect normalization introduces, across all
    /// the bodies of the module.
    anf_counter: usize,
    /// Set while a BEAM guard expression is being lowered (`lower_guard`).
    in_beam_guard: bool,
    /// The lambda with this id is lowered as a raw fun with
    /// the given convention (CPS or direct) instead of deciding from its own
    /// type. Set by dictionary-method lowering, which owns the slot's
    /// representation.
    forced_lambda_cps: Option<(NodeId, bool)>,
    /// Cross-module codegen context (compiled modules, effect bindings, prelude imports).
    ctx: &'a super::CodegenContext,
    /// Source location info for error terms. None for stdlib modules (no user source).
    source_info: Option<SourceInfo>,
    /// Current Erlang module name being emitted (e.g. "my_app_server").
    current_module: String,
    /// Current Saga source module name (e.g. "MyApp.Server").
    current_source_module: String,
    /// Current function being lowered (e.g. "handle_request"). Set per function.
    current_function: String,
    /// Maps module alias -> Erlang module atom (e.g. "List" -> "std_list").
    /// The builder's module for a qualified head that has no resolution entry.
    module_aliases: HashMap<String, String>,
    /// Names declared as `pub` in the current module (for export filtering).
    pub_names: std::collections::HashSet<String>,
    /// Maps record name -> ordered field names (from RecordDef declarations).
    record_fields: HashMap<String, Vec<String>>,
    /// CPS metadata for top-level functions. Populated from FunBinding/FunSignature
    /// during init_module. NOT used for name resolution (that's the ResolutionMap).
    fun_info: HashMap<String, FunInfo>,
    /// Maps effect name -> EffectInfo (op names and param counts).
    effect_defs: HashMap<String, EffectInfo>,
    /// Maps handler name -> handler arms + return clause.
    handler_defs: HashMap<String, HandlerInfo>,
    /// Same-module handler factories whose body is exactly a handler expression.
    handler_factory_defs: HashMap<String, HandlerFactoryInfo>,
    /// Same-module single-clause function bodies admitted for tiny static
    /// handler helper islands.
    local_helper_defs: HashMap<String, LocalHelperInfo>,
    helper_inline_stack: Vec<String>,
    generated_helper_variants: Vec<GeneratedHelperVariant>,
    /// Trait impl methods hoisted to top-level functions for direct dispatch.
    /// Planned before body lowering (so call sites can reference them) and
    /// emitted during dict-constructor lowering. Empty when no local nullary
    /// dict has a statically-known call site.
    dict_method_hoists: HashMap<(String, usize), HoistedDictMethod>,
    /// Per-module trait-specialization outcome counts (SAGA_STATS=trait-spec).
    trait_spec_stats: trait_spec_stats::TraitSpecStats,
    generated_hof_variants: Vec<GeneratedHofVariant>,
    /// Evidence context for the currently-lowered effectful scope. `None` in
    /// pure code. Set by the function-entry plumbing for effectful functions
    /// (var = `_Evidence`) and refreshed at `with` boundaries (var = a fresh
    /// name bound to the inserted-canonical extension). Op-call emission
    /// reads handler closures out of this evidence vector via
    /// `evidence_op_lookup`.
    current_evidence: Option<EvidenceFrame>,
    /// Set of "effect.op" keys whose current handler arm never calls resume.
    /// Used to pass a cheap atom instead of a real continuation closure at the call site,
    /// avoiding the Erlang "a term is constructed but never used" warning.
    no_resume_ops: std::collections::HashSet<String>,
    /// Maps "effect.op" -> handler canonical name for ops that are guaranteed to
    /// resume exactly once with the result value. These ops can be inlined as direct
    /// `let` bindings instead of going through CPS continuation-passing, avoiding
    /// closure allocation. Currently all BEAM-native ops satisfy this property.
    direct_ops: HashMap<String, String>,
    /// Maps "effect.op" -> static handler arm facts for the local
    /// tail-resume optimization. These are scoped to a `with` body and are
    /// optional; missing entries use the normal evidence path.
    static_tail_resume_ops: HashMap<String, StaticTailResumeOp>,
    /// Extra capture params installed while lowering a generated imported
    /// helper variant. These are rebound only around direct handler-arm bodies
    /// so they do not shadow imported helper params or locals.
    static_helper_variant_capture_bindings: Vec<(String, String)>,
    direct_hof_callback_params: HashMap<String, usize>,
    direct_hof_value_bindings: HashMap<String, DirectHofValueBinding>,
    /// Contextual function-value ABIs keyed by the value expression's stable
    /// identity. Unlike the former mutable "next lambda" slot, unrelated
    /// recursive lowering cannot consume or overwrite another value's ABI.
    effect_abi_plan: super::call_effects::EffectAbiPlan,
    /// Compatibility cache for callers that invoke contextual emission
    /// without the normal project-wide precompute checkpoint. Plans remain
    /// module-separated and are consulted only by semantic module.
    fallback_effect_abi_plans: HashMap<String, super::call_effects::EffectAbiPlan>,
    /// Perform-site evidence captured by an open-row callback value, keyed by
    /// that callback expression's identity, with the effects the callback's
    /// type names (those it takes from its caller instead).
    function_value_captured_evidence: HashMap<NodeId, CapturedCallbackEvidence>,
    /// Variable name for the continuation parameter in the current handler function.
    /// Set by `build_handler_fun`, read by `Expr::Resume`.
    current_handler_k: Option<String>,
    /// When lowering a handler arm with `finally`, this holds the finally block AST.
    /// At each `resume` site the cleanup code is lowered inline (as the cleanup of
    /// the region `fin_resume` makes of the resumed computation) so it can capture
    /// variables from the arm body's lexical scope.
    current_handler_finally: Option<crate::ast::Expr>,
    /// When inlining a named handler from another module, local function references
    /// inside that handler body should lower against the source module, not the
    /// current module being emitted.
    current_handler_source_module: Option<String>,
    /// The continuation of the tail of the handler arm being lowered: the
    /// arm's abort continuation (`current_abort_k`) in an arm of a general
    /// `with`; `None` in an arm of a chained one, which resumes in every
    /// tail. A `return` clause is lowered with the continuation of its
    /// `with` here instead.
    current_handler_inherited_k: Option<CExpr>,
    /// The variable holding the abort reference of the `with` whose arms are
    /// being built: an arm that does not resume throws with it, and a
    /// `resume` that is not in tail position catches it.
    current_abort_ref: Option<String>,
    /// The variable holding the abort continuation of the arm being lowered
    /// (`fun(V) -> abort(Ref, Tag, V)`), given to the arm body's tail.
    current_abort_k: Option<String>,
    /// Pre-resolved constructor name -> mangled Erlang atom.
    /// e.g. "NotFound" -> "std_file_NotFound", "Ok" -> "ok".
    /// Built by resolve::build_constructor_atoms before lowering.
    constructor_atoms: super::resolve::ConstructorAtoms,
    /// Pre-resolved name resolution map: NodeId -> ResolvedSymbol.
    /// Built by resolve::resolve_names before lowering.
    resolved: super::resolve::ResolutionMap,
    /// Origins of the nodes of the module being lowered that the generic
    /// fold copied. See `Lowerer::origin`.
    origins: super::generic_fold::NodeOrigins,
    /// Record type facts carried for fresh cross-module inlined nodes.
    /// These mirror typechecker `record_types` entries that would otherwise be
    /// lost when generic folding freshens producer AST into the consumer module.
    carried_record_types: HashMap<crate::ast::NodeId, String>,
    /// Constructor facts carried for fresh cross-module inlined nodes.
    /// These preserve producer-module constructor atoms for inlined private or
    /// opaque constructors whose bare names would otherwise resolve locally.
    carried_constructors: HashMap<crate::ast::NodeId, String>,
    /// Name-level fallback for constructor facts carried through generic fold.
    /// Some later fold rewrites duplicate/freshen AST nodes after the id-keyed
    /// carry; the bare constructor name survives those rewrites.
    carried_constructor_names: HashMap<String, String>,
    /// Bare handler name -> canonical handler name (e.g. "collect_handler" -> "Std.Test.collect_handler").
    /// Built during init_module for resolving handler references in `with` expressions.
    handler_canonical: HashMap<String, String>,
    /// Bare effect name -> canonical effect name (e.g. "Test" -> "Std.Test.Test").
    /// Built during init_module for canonicalizing effect names from the type system.
    effect_canonical: HashMap<String, String>,
    /// Typechecker result for the module currently being lowered.
    /// Provides resolved types, handler info, effect info, etc.
    check_result: &'a crate::typechecker::CheckResult,
    /// Post-classifier optimizer facts for the module being lowered.
    optimization: super::optimize::OptimizationFacts,
    /// Conditional handle bindings: name -> (cond_var, cond_expr, then_canonical, else_canonical).
    /// Used during lower_with to generate conditional handler dispatch.
    handle_cond_vars: HashMap<String, (String, CExpr, String, String)>,
    /// Dynamic handle bindings: name -> (lowered_var, canonical_effect_names, has_return_clause).
    /// For `handle name = some_function_call()` where the handler isn't statically
    /// resolvable, the RHS is lowered to a tuple-of-lambdas and bound to a variable.
    /// At `with` sites, the tuple is destructured to extract per-op handler functions.
    handle_dynamic_vars: HashMap<String, (String, Vec<String>, bool)>,
    /// Undo log for `let`-bound handler names: each entry is a name and its
    /// previous entries in `handler_canonical`, `handle_cond_vars` and
    /// `handle_dynamic_vars`. A block rolls the log back to where it started
    /// when it is lowered, so a handler bound in a block is not visible after it.
    handler_binding_undo: Vec<HandlerBindingUndo>,
    /// Optional function name that should be exported even if it is not `pub`.
    /// Used by the build pipeline to mark the chosen entrypoint explicitly.
    /// Subsumed by Core-level export-all (every function is exported), but kept
    /// wired through the build pipeline's `emit_module*` API.
    #[allow(dead_code)]
    entry_export: Option<String>,
    /// Trait impl dict name -> sorted canonical effect names from the impl's
    /// `needs` clause. Populated during `lower_module` from active and
    /// imported modules, and used as a fallback for imported metadata that
    /// does not yet expose per-method impl effects.
    impl_effects_by_dict: HashMap<String, Vec<String>>,
    /// Trait impl dict + method index -> sorted canonical effect names needed
    /// by that concrete slot. Active modules populate this more precise shape
    /// so pure methods in an effectful impl can remain direct-callable.
    impl_method_effects_by_dict: HashMap<(String, usize), Vec<String>>,
    /// Source-order audit rows for direct-native vs evidence effect-op
    /// lowering decisions in the current module. Populated during expression
    /// lowering when `lower_effect_call` reaches the actual emission branch.
    effect_op_trace: Vec<super::call_effects::EffectOpTraceEntry>,
}

impl<'a> Lowerer<'a> {
    pub(super) fn new(
        ctx: &'a super::CodegenContext,
        constructor_atoms: super::resolve::ConstructorAtoms,
        resolution: LowererResolution,
        check_result: &'a crate::typechecker::CheckResult,
        optimization: super::optimize::OptimizationFacts,
        source_info: Option<SourceInfo>,
        entry_export: Option<String>,
    ) -> Self {
        Lowerer {
            counter: 0,
            anf_counter: 0,
            in_beam_guard: false,
            forced_lambda_cps: None,
            ctx,
            source_info,
            current_module: String::new(),
            current_source_module: String::new(),
            current_function: String::new(),
            module_aliases: HashMap::new(),
            pub_names: std::collections::HashSet::new(),
            record_fields: HashMap::new(),
            fun_info: HashMap::new(),
            effect_defs: HashMap::new(),
            handler_defs: HashMap::new(),
            handler_factory_defs: HashMap::new(),
            local_helper_defs: HashMap::new(),
            helper_inline_stack: Vec::new(),
            generated_helper_variants: Vec::new(),
            dict_method_hoists: HashMap::new(),
            trait_spec_stats: trait_spec_stats::TraitSpecStats::default(),
            generated_hof_variants: Vec::new(),
            current_evidence: None,
            no_resume_ops: std::collections::HashSet::new(),
            direct_ops: HashMap::new(),
            static_tail_resume_ops: HashMap::new(),
            static_helper_variant_capture_bindings: Vec::new(),
            direct_hof_callback_params: HashMap::new(),
            direct_hof_value_bindings: HashMap::new(),
            effect_abi_plan: super::call_effects::EffectAbiPlan::default(),
            fallback_effect_abi_plans: HashMap::new(),
            function_value_captured_evidence: HashMap::new(),
            constructor_atoms,
            resolved: resolution.symbols,
            origins: resolution.origins,
            carried_record_types: resolution.carried_record_types,
            carried_constructors: resolution.carried_constructors,
            carried_constructor_names: resolution.carried_constructor_names,
            current_handler_k: None,
            current_handler_finally: None,
            current_handler_source_module: None,
            current_handler_inherited_k: None,
            current_abort_ref: None,
            current_abort_k: None,
            handler_canonical: HashMap::new(),
            effect_canonical: HashMap::new(),
            check_result,
            optimization,
            handle_cond_vars: HashMap::new(),
            handle_dynamic_vars: HashMap::new(),
            handler_binding_undo: Vec::new(),
            entry_export,
            impl_effects_by_dict: HashMap::new(),
            impl_method_effects_by_dict: HashMap::new(),
            effect_op_trace: Vec::new(),
        }
    }

    pub(super) fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("_Cor{}", n)
    }

    fn semantic_effect_abi_plan(&self) -> Option<&super::call_effects::EffectAbiPlan> {
        let semantic_module = self.current_semantic_module_name();
        if let Some(plan) = self.fallback_effect_abi_plans.get(semantic_module) {
            return Some(plan);
        }
        (semantic_module != self.current_source_module)
            .then(|| self.ctx.modules.get(semantic_module))
            .flatten()
            .filter(|compiled| compiled.effect_abi_plan_ready)
            .map(|compiled| &compiled.effect_abi_plan)
    }

    pub(super) fn planned_call(&self, node_id: NodeId) -> Option<&CallEffectInfo> {
        self.effect_abi_plan.call(node_id).or_else(|| {
            self.semantic_effect_abi_plan()
                .and_then(|plan| plan.call(node_id))
        })
    }

    /// Whether a lambda's innermost body is an effectful call or an applied
    /// operation, as recorded when the plan was made.
    pub(super) fn planned_lambda_body_effectful(&self, lambda_id: NodeId) -> Option<bool> {
        self.effect_abi_plan
            .lambda_body_effectful(lambda_id)
            .or_else(|| {
                self.semantic_effect_abi_plan()
                    .and_then(|plan| plan.lambda_body_effectful(lambda_id))
            })
    }

    /// Whether a dictionary method performs an operation directly. Read
    /// from the plan once it exists; before that the tree is still in the
    /// shape the plan will be made from.
    pub(super) fn dict_method_performs(&self, method: &Expr) -> bool {
        self.effect_abi_plan
            .dict_method_performing(method.id)
            .unwrap_or_else(|| super::effect_position::mentions_operation(method))
    }

    pub(super) fn planned_declaration(&self, node_id: NodeId) -> Option<&CallableAbi> {
        self.effect_abi_plan.declaration(node_id).or_else(|| {
            self.semantic_effect_abi_plan()
                .and_then(|plan| plan.declaration(node_id))
        })
    }

    pub(super) fn capture_function_value_evidence(
        &mut self,
        node_id: NodeId,
        frame: EvidenceFrame,
        named_effects: Vec<String>,
    ) -> Option<CapturedCallbackEvidence> {
        self.function_value_captured_evidence
            .insert(node_id, (frame, named_effects))
    }

    pub(super) fn restore_function_value_captured_evidence(
        &mut self,
        node_id: NodeId,
        previous: Option<CapturedCallbackEvidence>,
    ) {
        if let Some(previous) = previous {
            self.function_value_captured_evidence
                .insert(node_id, previous);
        } else {
            self.function_value_captured_evidence.remove(&node_id);
        }
    }

    /// Build a structured error term and wrap it in `erlang:error(Term)`.
    /// Falls back to the old `{saga_panic, Msg}` tuple when no source info is available.
    pub(super) fn make_error(
        &self,
        kind: ErrorKind,
        message: CExpr,
        span: Option<&crate::token::Span>,
    ) -> CExpr {
        let error_term = if let Some(si) = &self.source_info {
            let line = span.map_or(0, |s| si.line_number(s));
            ErrorInfo {
                kind,
                message,
                module: self.current_source_module.clone(),
                function: self.current_function.clone(),
                file: si.file.clone(),
                line,
            }
            .to_cexpr()
        } else {
            // Stdlib modules don't have source info — use the old format
            CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("saga_error".into())),
                CExpr::Lit(CLit::Atom(kind.as_atom().into())),
                message,
                lower_string_to_binary(&self.current_source_module),
                lower_string_to_binary(&self.current_function),
                lower_string_to_binary(""),
                CExpr::Lit(CLit::Int(0)),
            ])
        };
        cerl_call("erlang", "error", vec![error_term])
    }

    /// Wrap a CExpr with a source location annotation for BEAM stack traces.
    /// No-op if source info is unavailable or span is missing.
    pub(super) fn annotate(&self, expr: CExpr, span: Option<&crate::token::Span>) -> CExpr {
        if let Some(si) = &self.source_info
            && let Some(span) = span
        {
            let line = si.line_number(span);
            if line > 0 {
                return CExpr::Annotated {
                    expr: Box::new(expr),
                    line,
                    file: si.file.clone(),
                };
            }
        }
        expr
    }

    /// Resolve a bare effect name to its canonical form.
    fn canonicalize_effect(&self, bare: &str) -> String {
        self.effect_canonical
            .get(bare)
            .cloned()
            .unwrap_or_else(|| bare.to_string())
    }

    /// Canonicalize a list of effect names from the type system (which uses bare names).
    fn canonicalize_effects(&self, effects: Vec<String>) -> Vec<String> {
        effects
            .into_iter()
            .map(|e| self.canonicalize_effect(&e))
            .collect()
    }

    /// Resolve a bare handler name to its canonical form.
    fn resolve_handler_name(&self, name: &str) -> String {
        self.handler_canonical
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    /// Given a list of effect names (from a `needs` clause), return all
    /// (effect_name, op_name) pairs. This is the single source of truth for
    /// what handler params a function needs.
    pub(super) fn effect_handler_ops(&self, effects: &[String]) -> Vec<(String, String)> {
        let mut ops = Vec::new();
        for eff_name in effects {
            if let Some(info) = self.effect_defs.get(eff_name) {
                // Sort op names for deterministic ordering
                let mut op_names: Vec<&String> = info.ops.keys().collect();
                op_names.sort();
                for op_name in op_names {
                    ops.push((eff_name.clone(), op_name.clone()));
                }
            }
        }
        ops
    }

    /// Generate the handler param variable name for a specific effect op.
    /// e.g. ("Std.Process.Process", "spawn") -> "_Handle_Std_Process_Process_spawn"
    /// Dots are replaced with underscores for valid Core Erlang variable names.
    pub(super) fn handler_param_name(effect: &str, op: &str) -> String {
        let effect = effect
            .chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect::<String>();
        format!("_Handle_{}_{}", effect, op)
    }

    /// Generate a fresh scoped handler binding name for a specific effect op.
    /// Used for local `with` layers so nested handlers for the same op don't
    /// shadow each other and trigger backend "constructed but never used" warnings.
    pub(super) fn fresh_handler_binding_name(&mut self, effect: &str, op: &str) -> String {
        let suffix = self.counter;
        self.counter += 1;
        format!("{}__{}", Self::handler_param_name(effect, op), suffix)
    }

    /// Whether `expr`, as a block statement or a `do` binding, takes the
    /// rest of the block as its continuation (the `let` rule), instead of
    /// being evaluated to a value that is then bound.
    ///
    /// It does when something in it performs (`Lowerer::performs_effect`,
    /// the one definition of that), composed over sub-expressions by
    /// `effect_position::is_effectful`. A `with` does when its handled
    /// computation does. See "The Continuation of a `with`" in
    /// `docs/effect-implementation.md`.
    fn takes_continuation(&self, expr: &Expr) -> bool {
        super::effect_position::is_effectful(expr, &|node| match &node.kind {
            ExprKind::With { expr: inner, .. } => self.takes_continuation(inner),
            _ => self.performs_effect(node),
        })
    }

    /// Canonical predicate for "is this a saturated effectful function call?"
    ///
    /// Reads from the pre-populated `CallEffectMap`. Returns true when the
    /// outer expression is an `App` whose entry classifies as effectful
    /// (`StaticOps` or `RowForwarded`). Bare references and partial
    /// applications are tagged `Pure` by the populator.
    pub(super) fn expr_is_effectful_call(&self, expr: &Expr) -> bool {
        if !matches!(expr.kind, ExprKind::App { .. }) {
            return false;
        }
        if let Some((head, arity)) = Self::app_head_and_source_arity(expr)
            && let ExprKind::Var { name, .. } = &head.kind
            && self.direct_hof_callback_arity(&core_var(name)) == Some(arity)
        {
            return false;
        }
        self.planned(expr).is_cps_call()
    }

    fn app_head_and_source_arity(expr: &Expr) -> Option<(&Expr, usize)> {
        let mut current = expr;
        let mut arity = 0;
        while let ExprKind::App { func, .. } = &current.kind {
            arity += 1;
            current = func;
        }
        (arity > 0).then_some((current, arity))
    }

    /// Variant that uses an explicit `CheckResult` for type-at-span lookups.
    /// When the lowerer runs the pre-pass over a foreign module's elaborated
    /// AST (e.g. handler arm bodies imported from another module), the active
    /// module's `check_result` does not contain that module's spans, so
    /// pattern-effect lookups silently miss. Cross-module walks must thread
    /// the source module's `CheckResult` here.
    fn populate_call_effects_with_check(
        &self,
        program: &ast::Program,
        check_result: &crate::typechecker::CheckResult,
    ) -> super::call_effects::PopulatedCallEffects {
        use super::call_effects::{FunSig, Populator};

        let fun_sigs: HashMap<String, FunSig> = self
            .fun_info
            .iter()
            .map(|(name, info)| {
                (
                    name.clone(),
                    FunSig {
                        abi: info.abi.clone(),
                    },
                )
            })
            .collect();

        let effect_ops: HashMap<String, Vec<String>> = self
            .effect_defs
            .iter()
            .map(|(eff, info)| {
                let mut ops: Vec<String> = info.ops.keys().cloned().collect();
                ops.sort();
                (eff.clone(), ops)
            })
            .collect();

        let trait_method_effects_by_key: HashMap<
            (String, usize),
            crate::typechecker::TraitMethodEffectSig,
        > = check_result
            .traits
            .iter()
            .flat_map(|(trait_name, info)| {
                info.methods.iter().enumerate().map(move |(idx, method)| {
                    ((trait_name.clone(), idx), method.effect_sig.clone())
                })
            })
            .collect();

        Populator::new(super::call_effects::PopulatorInputs {
            module: &self.current_source_module,
            source_info: self.source_info.as_ref(),
            resolved: &self.resolved,
            origins: &self.origins,
            check_result,
            ctx: self.ctx,
            fun_sigs: &fun_sigs,
            effect_ops: &effect_ops,
            effect_canonical: &self.effect_canonical,
            impl_effects_by_dict: &self.impl_effects_by_dict,
            impl_method_effects_by_dict: &self.impl_method_effects_by_dict,
            trait_method_effects_by_key: &trait_method_effects_by_key,
        })
        .populate_with_trace(program)
    }

    /// Whether the trait method at `(trait_name, method_index)` takes no
    /// parameters (e.g. `fun default : a`). Such methods are stored in the dict
    /// as zero-arity thunks and must be applied when accessed.
    pub(super) fn trait_method_is_nullary(&self, trait_name: &str, method_index: usize) -> bool {
        self.trait_info(trait_name)
            .and_then(|info| info.methods.get(method_index))
            .is_some_and(|m| m.param_types.is_empty())
    }

    pub(super) fn trait_method_tuple_index(&self, trait_name: &str, method_index: usize) -> usize {
        self.trait_info(trait_name)
            .map(|info| info.supertraits.len() + method_index)
            .unwrap_or(method_index)
    }

    pub(super) fn trait_info(&self, trait_name: &str) -> Option<&TraitInfo> {
        if let Some(info) = self.check_result.traits.get(trait_name) {
            return Some(info);
        }

        let mut matches = self.check_result.traits.iter().filter_map(|(name, info)| {
            (name.rsplit('.').next() == Some(trait_name)).then_some(info)
        });
        let info = matches.next()?;
        matches.next().is_none().then_some(info)
    }
}

pub(crate) fn precompute_call_effects(
    ctx: &super::CodegenContext,
    module_name: &str,
    program: &ast::Program,
    resolution: super::resolve::ResolutionMap,
    check_result: &crate::typechecker::CheckResult,
) -> super::call_effects::EffectAbiPlan {
    Lowerer::new(
        ctx,
        super::resolve::ConstructorAtoms::new(),
        LowererResolution {
            symbols: resolution,
            origins: ctx
                .modules
                .get(module_name)
                .map(|compiled| compiled.origins.clone())
                .unwrap_or_default(),
            ..Default::default()
        },
        check_result,
        super::optimize::OptimizationFacts::default(),
        None,
        None,
    )
    .precompute_call_effects(module_name, program)
}
