//! Per-call effect metadata tagged ahead of lowering.
//!
//! A pre-pass walks the elaborated program and produces a `NodeId ->
//! CallEffectInfo` map for every `App` node. The lowerer is a read-only
//! consumer at every effectful call site, using the map to drive evidence
//! threading and projection. This is the single writer for per-call effect
//! metadata; adding a new call shape means teaching the populator one new
//! branch, not auditing every dispatcher.
//!
//! Recognized head shapes:
//! - `Var` and `QualifiedName` — resolved via the `ResolutionMap`.
//! - `DictMethodAccess` — effectful trait method calls.
//! - `Lambda` — `(fun x -> ...) y`. Effect row read from the typechecker's
//!   per-node type.
//!
//! Direct effect-op calls (`op!`) are tagged via `collect_effect_call`, not
//! through `App`, and are out of scope for this module.
//!
//! Saturated effectful calls produce `StaticOps` (closed row) or
//! `RowForwarded` (open row). Otherwise: `Pure`. Effectful let-bindings
//! (`let g = factory(); g x`) are tracked via a lexical scope stack inside
//! the populator.
//!
//! This module is intentionally a classifier, not a lowerer. It names the
//! ABI/evidence shape a call site needs; Core Erlang emission remains in
//! `codegen::lower`.

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Decl, Expr, ExprKind, NodeId, Pat, Program, Stmt};
use crate::codegen::CodegenContext;
use crate::codegen::lower::util;
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi};
use crate::typechecker::{CheckResult, TraitMethodEffectSig};

/// Per-call metadata. Keyed by the `NodeId` of an `App` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallEffectInfo {
    Direct,
    Cps(CallableAbi),
}

impl CallEffectInfo {
    /// Pure call. No evidence threading, no return continuation.
    pub fn pure() -> Self {
        Self::Direct
    }

    /// CPS/evidence call. The caller must supply evidence and a return
    /// continuation according to `kind`.
    fn cps(kind: CallEffectKind, user_arity: usize) -> Self {
        if matches!(&kind, CallEffectKind::StaticOps { ops } if ops.is_empty()) {
            return Self::Direct;
        }
        let evidence = match &kind {
            CallEffectKind::StaticOps { ops } => EvidenceAbi::closed(unique_effects(ops)),
            CallEffectKind::RowForwarded { static_ops } => {
                EvidenceAbi::new(unique_effects(static_ops), true)
            }
        };
        let info = Self::Cps(CallableAbi::cps(user_arity, evidence));
        info.debug_check();
        info
    }

    /// Extract the CPS call plan the lowerer needs for evidence construction.
    ///
    /// Returns `None` for direct/externally-pure calls. Open-row calls return
    /// `Some` even when their static effect prefix is empty, because they still
    /// need caller evidence forwarded through the CPS ABI.
    pub fn cps_call_abi(&self) -> Option<&CallableAbi> {
        match self {
            Self::Direct => None,
            Self::Cps(abi) => Some(abi),
        }
    }

    pub fn is_cps_call(&self) -> bool {
        matches!(self, Self::Cps(_))
    }

    /// Human-readable ABI shape for debug/audit traces.
    ///
    /// The wording intentionally mirrors the selective-uniform branch's
    /// `call_shape_debug_label` style, but describes the current direct-first
    /// classifier contract rather than a separate planner.
    pub fn debug_label(&self) -> String {
        match self {
            Self::Direct => "direct".to_string(),
            Self::Cps(abi) => {
                let evidence = abi
                    .evidence
                    .as_ref()
                    .expect("CPS call ABI is missing evidence");
                if evidence.is_open() {
                    format!(
                        "cps-row-forwarded({}->{}, pinned_effects={:?})",
                        abi.user_arity,
                        abi.expanded_arity(),
                        evidence.static_slots()
                    )
                } else {
                    format!(
                        "cps-static({}->{}, effects={:?})",
                        abi.user_arity,
                        abi.expanded_arity(),
                        evidence.static_slots()
                    )
                }
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn test_cps_static(effect: &str, op: &str, user_arity: usize) -> Self {
        Self::cps(
            CallEffectKind::StaticOps {
                ops: vec![OpKey {
                    effect: effect.to_string(),
                    op: op.to_string(),
                }],
            },
            user_arity,
        )
    }

    /// Invariant check for classifier-created entries.
    #[inline]
    fn debug_check(&self) {
        if let Self::Cps(abi) = self {
            assert!(
                abi.evidence.is_some(),
                "CallEffectInfo: CPS calls require an evidence ABI"
            );
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CallEffectKind {
    /// Effects fully known statically at this call site. Caller threads exactly
    /// these ops, in canonical (effect, op) order.
    StaticOps { ops: Vec<OpKey> },
    /// Row-polymorphic call. `static_ops` is the set pinned by a closed prefix
    /// (possibly empty); the rest is forwarded from caller's ambient evidence.
    RowForwarded { static_ops: Vec<OpKey> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OpKey {
    /// Canonical effect name from `ResolutionResult.effects`,
    /// e.g. `"Std.Fail.Fail"`. Never a source-level alias.
    pub effect: String,
    pub op: String,
}

pub type CallEffectMap = HashMap<NodeId, CallEffectInfo>;

/// The implementation and contextual boundary of one function value.
/// Keeping them in one value makes a one-sided adapter plan unrepresentable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionValueBoundary {
    implementation: CallableAbi,
    boundary: CallableAbi,
}

impl FunctionValueBoundary {
    pub fn implementation(&self) -> &CallableAbi {
        &self.implementation
    }

    pub fn boundary(&self) -> &CallableAbi {
        &self.boundary
    }
}

/// The callable views that can coexist for one function-value expression.
/// They must not be collapsed: a row-polymorphic partial application can
/// infer a pure occurrence type while still constructing a CPS closure, and
/// a surrounding callback slot can expose yet another ABI.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionValueAbiPlan {
    inferred: Option<CallableAbi>,
    contextual: Option<FunctionValueBoundary>,
}

impl FunctionValueAbiPlan {
    pub fn inferred(&self) -> Option<&CallableAbi> {
        self.inferred.as_ref()
    }

    pub fn contextual(&self) -> Option<&FunctionValueBoundary> {
        self.contextual.as_ref()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectAbiPlan {
    declarations: HashMap<NodeId, CallableAbi>,
    calls: CallEffectMap,
    function_values: HashMap<NodeId, FunctionValueAbiPlan>,
    frozen: bool,
}

impl EffectAbiPlan {
    fn assert_mutable(&self) {
        assert!(
            !self.frozen,
            "internal ABI planning error: attempted to mutate a frozen plan"
        );
    }

    pub fn freeze(&mut self) {
        self.frozen = true;
    }

    pub fn record_declaration(&mut self, node_id: NodeId, abi: CallableAbi) {
        self.assert_mutable();
        if let Some(previous) = self.declarations.insert(node_id, abi.clone()) {
            assert_eq!(
                previous, abi,
                "internal ABI planning error: conflicting declaration ABI for {node_id:?}"
            );
        }
    }

    pub fn declaration(&self, node_id: NodeId) -> Option<&CallableAbi> {
        self.declarations.get(&node_id)
    }

    pub fn call(&self, node_id: NodeId) -> Option<&CallEffectInfo> {
        self.calls.get(&node_id)
    }

    pub fn into_calls(self) -> CallEffectMap {
        self.calls
    }

    pub fn record_call(&mut self, node_id: NodeId, info: CallEffectInfo) {
        self.assert_mutable();
        if let Some(previous) = self.calls.insert(node_id, info.clone()) {
            assert_eq!(
                previous, info,
                "internal ABI planning error: conflicting call ABI for {node_id:?}"
            );
        }
    }

    pub fn function_value(&self, node_id: NodeId) -> Option<&FunctionValueAbiPlan> {
        self.function_values.get(&node_id)
    }

    pub fn record_inferred_function_value(&mut self, node_id: NodeId, abi: CallableAbi) {
        self.assert_mutable();
        let value = self.function_values.entry(node_id).or_default();
        if let Some(previous) = value.inferred.replace(abi.clone()) {
            assert_eq!(
                previous, abi,
                "internal ABI planning error: conflicting inferred ABI for {node_id:?}"
            );
        }
    }

    pub fn record_function_value_boundary(
        &mut self,
        node_id: NodeId,
        implementation: CallableAbi,
        boundary: CallableAbi,
    ) {
        self.assert_mutable();
        let value = self.function_values.entry(node_id).or_default();
        let contextual = FunctionValueBoundary {
            implementation,
            boundary,
        };
        if let Some(previous) = value.contextual.replace(contextual.clone()) {
            assert_eq!(
                previous, contextual,
                "internal ABI planning error: conflicting contextual ABI for {node_id:?}"
            );
        }
    }

    pub fn function_value_boundary(&self, node_id: NodeId) -> Option<&CallableAbi> {
        Some(
            self.function_values
                .get(&node_id)?
                .contextual
                .as_ref()?
                .boundary(),
        )
    }

    pub fn function_value_implementation(&self, node_id: NodeId) -> Option<&CallableAbi> {
        Some(
            self.function_values
                .get(&node_id)?
                .contextual
                .as_ref()?
                .implementation(),
        )
    }

    /// Merge a separately planned module, rejecting conflicting facts rather
    /// than silently retaining whichever plan happened to be visited first.
    pub fn merge_checked(&mut self, other: &Self) {
        self.assert_mutable();
        for (node_id, abi) in &other.declarations {
            self.record_declaration(*node_id, abi.clone());
        }
        for (node_id, info) in &other.calls {
            self.record_call(*node_id, info.clone());
        }
        for (node_id, value) in &other.function_values {
            if let Some(inferred) = value.inferred() {
                self.record_inferred_function_value(*node_id, inferred.clone());
            }
            if let Some(contextual) = value.contextual() {
                self.record_function_value_boundary(
                    *node_id,
                    contextual.implementation().clone(),
                    contextual.boundary().clone(),
                );
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallEffectTraceEntry {
    pub app_id: NodeId,
    pub head_id: NodeId,
    pub head: String,
    pub supplied_args: usize,
    pub shape: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PopulatedCallEffects {
    pub plan: EffectAbiPlan,
    pub trace: Vec<CallEffectTraceEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectOpTraceEntry {
    pub node_id: NodeId,
    pub effect: String,
    pub op: String,
    pub source_args: usize,
    pub runtime_args: usize,
    pub shape: String,
}

pub fn call_effect_trace_enabled_for(subject: &str) -> bool {
    let Some(filter) = call_effect_trace_filter() else {
        return false;
    };
    debug_filter_matches(&filter, "call-effects", Some(subject))
}

pub fn effect_op_trace_enabled_for(subject: &str) -> bool {
    let Some(filter) = call_effect_trace_filter() else {
        return false;
    };
    debug_filter_matches(&filter, "effect-ops", Some(subject))
}

pub fn format_call_effect_trace(subject: &str, trace: &[CallEffectTraceEntry]) -> String {
    let mut out = format!("call-effects[{subject}]: {} app(s)", trace.len());
    for entry in trace {
        out.push_str(&format!(
            "\n  app#{} head#{} {} / {} -> {}",
            entry.app_id.0, entry.head_id.0, entry.head, entry.supplied_args, entry.shape
        ));
    }
    out
}

pub fn format_effect_op_trace(subject: &str, trace: &[EffectOpTraceEntry]) -> String {
    let mut out = format!("effect-ops[{subject}]: {} op call(s)", trace.len());
    for entry in trace {
        out.push_str(&format!(
            "\n  op#{} {}.{} / {} source arg(s), {} runtime arg(s) -> {}",
            entry.node_id.0,
            entry.effect,
            entry.op,
            entry.source_args,
            entry.runtime_args,
            entry.shape
        ));
    }
    out
}

fn call_effect_trace_filter() -> Option<String> {
    std::env::var_os("SAGA_DEBUG_EFFECT_SHAPES")
        .or_else(|| std::env::var_os("SAGA_DEBUG_SELECTIVE"))
        .map(|value| value.to_string_lossy().to_string())
}

fn debug_filter_matches(filter: &str, target: &str, subject: Option<&str>) -> bool {
    let filter = filter.trim();
    if filter.is_empty() || matches!(filter, "1" | "true" | "all") {
        return true;
    }
    if target.contains(filter) {
        return true;
    }
    let Some(subject) = subject else {
        return false;
    };
    subject.contains(filter) || format!("{target}:{subject}").contains(filter)
}

fn unique_effects(ops: &[OpKey]) -> Vec<String> {
    let mut effects: Vec<String> = ops.iter().map(|k| k.effect.clone()).collect();
    effects.sort();
    effects.dedup();
    effects
}

/// Snapshot of the per-function metadata the populator needs. Built by the
/// Lowerer from its own `FunInfo` table once `init_module` has finished.
#[derive(Debug, Clone, Default)]
pub struct FunSig {
    /// Authoritative runtime convention for this callable.
    pub abi: CallableAbi,
    /// param-index -> absorbed effects (for HOF effect absorption).
    pub param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// Source-level parameter types. Used to detect callback parameters
    /// whose type has an open effect row but no named effects — these need
    /// CPS threading at call sites even though `param_absorbed_effects`
    /// (named-effects only) misses them.
    pub param_types: Vec<crate::typechecker::Type>,
    /// Number of dictionary params prepended by elaboration before source
    /// parameters. Callback metadata is keyed by source parameter index.
    pub dict_param_count: usize,
}

/// Read-only inputs the populator consults during its walk. Bundled into a
/// struct so the constructor doesn't carry a half-dozen reference parameters
/// that all lifetime-tie back to the same lowering invocation.
pub struct PopulatorInputs<'a> {
    pub resolved: &'a ResolutionMap,
    pub check_result: &'a CheckResult,
    pub ctx: &'a CodegenContext,
    pub fun_sigs: &'a HashMap<String, FunSig>,
    /// Effect canonical name -> sorted op names.
    pub effect_ops: &'a HashMap<String, Vec<String>>,
    /// Bare effect name -> canonical effect name (mirrors `Lowerer::effect_canonical`).
    /// Effects from `let_effect_bindings` and pattern-bound vars use bare names;
    /// `effect_ops` is keyed canonically. This map bridges the two.
    pub effect_canonical: &'a HashMap<String, String>,
    /// Static let-binding effects from CodegenContext.
    pub let_effect_bindings: &'a HashMap<String, Vec<String>>,
    /// Trait impl dict name -> sorted canonical effect names from the impl's
    /// `needs` clause. Used as a fallback for imported module metadata that
    /// does not yet expose per-method impl effects.
    pub impl_effects_by_dict: &'a HashMap<String, Vec<String>>,
    /// (trait impl dict name, method index) -> sorted canonical effect names
    /// needed by that concrete dictionary slot beyond the trait method
    /// signature.
    pub impl_method_effects_by_dict: &'a HashMap<(String, usize), Vec<String>>,
    /// (canonical trait name, method index) -> trait-declared effect signature.
    /// This is the contract for polymorphic/where-bound dictionary dispatch.
    pub trait_method_effects_by_key: &'a HashMap<(String, usize), TraitMethodEffectSig>,
}

/// Pre-pass walker. Constructed with the data sources it needs and consumed by
/// `populate(program)`.
pub struct Populator<'a> {
    inputs: PopulatorInputs<'a>,
    plan: EffectAbiPlan,
    trace: Vec<CallEffectTraceEntry>,
    /// Stack of lexical scopes. Each frame maps a bound name to the absorbed
    /// effects that calls of that name should thread.
    scopes: Vec<HashMap<String, Vec<String>>>,
    /// Stack of lexical scopes for variables whose type is an open-row
    /// callable (e.g. a function parameter `f: Unit -> Unit needs {..e}`).
    /// These have no static effects to pin, but the call site must still
    /// route through the CPS path so the caller's ambient evidence is
    /// forwarded into the callee. Parallel to `scopes` — pushed/popped
    /// together so lookups walk the same lexical structure.
    open_row_vars: Vec<HashSet<String>>,
    /// Stack of local function frames mirroring the lowerer's dynamic
    /// `fun_info` mutations for `Stmt::LetFun`. Maps name -> FunSig.
    local_fun_sigs: Vec<HashMap<String, FunSig>>,
    /// Resolved call head NodeId -> whether the callee's effect row is open.
    head_open_row: HashMap<NodeId, bool>,
    /// Effects performed by calls in the currently walked lambda body. This
    /// recovers open callback forwarding when the type-at-node view omits the
    /// absorbed row variable.
    lambda_body_evidence: Vec<EvidenceAbi>,
    /// Completed body-call evidence used only when the lambda itself is an
    /// immediate call head. It must not replace the callable's inferred ABI:
    /// enclosing `with` expressions may discharge some body-call evidence.
    lambda_head_evidence: HashMap<NodeId, EvidenceAbi>,
}

impl<'a> Populator<'a> {
    pub fn new(inputs: PopulatorInputs<'a>) -> Self {
        let head_open_row = Self::collect_head_open_rows(&inputs);
        Populator {
            inputs,
            plan: EffectAbiPlan::default(),
            trace: Vec::new(),
            scopes: Vec::new(),
            open_row_vars: Vec::new(),
            local_fun_sigs: Vec::new(),
            head_open_row,
            lambda_body_evidence: Vec::new(),
            lambda_head_evidence: HashMap::new(),
        }
    }

    fn canonicalize(&self, bare: &str) -> String {
        let family = crate::typechecker::applied_effect_family(bare);
        let canonical = self
            .inputs
            .effect_canonical
            .get(family)
            .cloned()
            .unwrap_or_else(|| family.to_string());
        format!("{}{}", canonical, &bare[family.len()..])
    }

    fn canonicalize_effects(&self, effects: Vec<String>) -> Vec<String> {
        effects.into_iter().map(|e| self.canonicalize(&e)).collect()
    }

    fn collect_head_open_rows(inputs: &PopulatorInputs<'_>) -> HashMap<NodeId, bool> {
        let mut out = HashMap::new();
        for (node_id, resolved) in inputs.resolved.iter() {
            // A symbol is "local" (look it up in the current module's env)
            // when it's a current-module BeamFunction (erlang_mod = None) or
            // when it carries no source_module at all (e.g. block-local funs).
            let local = matches!(
                &resolved.kind,
                ResolvedCodegenKind::BeamFunction {
                    erlang_mod: None,
                    ..
                }
            ) || resolved.source_module.is_none();
            let open = if local {
                inputs
                    .check_result
                    .env
                    .get(&resolved.name)
                    .map(|s| util::has_open_effect_row(&inputs.check_result.sub.apply(&s.ty)))
                    .unwrap_or(false)
            } else {
                resolved
                    .source_module
                    .as_deref()
                    .and_then(|src| inputs.ctx.modules.get(src))
                    .and_then(|m| {
                        m.codegen_info
                            .exports
                            .iter()
                            .find(|(n, _)| n == &resolved.name)
                            .map(|(_, scheme)| util::has_open_effect_row(&scheme.ty))
                    })
                    .unwrap_or(false)
            };
            out.insert(*node_id, open);
        }
        out
    }

    pub fn populate(self, program: &Program) -> CallEffectMap {
        self.populate_with_trace(program).plan.into_calls()
    }

    pub fn populate_with_trace(mut self, program: &Program) -> PopulatedCallEffects {
        for decl in program {
            self.walk_decl(decl);
        }
        PopulatedCallEffects {
            plan: self.plan,
            trace: self.trace,
        }
    }

    /// Push parallel frames onto `scopes` and `open_row_vars`. Use
    /// `push_scope_with` when the caller has already built the effects frame
    /// (e.g. from `fun_param_effectful_vars`).
    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.open_row_vars.push(HashSet::new());
    }

    fn push_scope_with(&mut self, frame: HashMap<String, Vec<String>>, open_row: HashSet<String>) {
        self.scopes.push(frame);
        self.open_row_vars.push(open_row);
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
        self.open_row_vars.pop();
    }

    fn walk_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::FunBinding {
                id,
                name,
                params,
                body,
                ..
            } => {
                if let Some(sig) = self.inputs.fun_sigs.get(name) {
                    self.plan.record_declaration(*id, sig.abi.clone());
                }
                let (frame, open_row) = self.fun_param_effectful_vars(name, params);
                self.push_scope_with(frame, open_row);
                // `fun_param_effectful_vars` seeds callback shape from the
                // function signature, but only a pattern variable can be
                // paired directly with a parameter type. Bindings nested in
                // constructor/tuple/record patterns have their own resolved
                // types in `type_at_span`; record those too so calls through a
                // destructured effectful callback retain the CPS ABI.
                for param in params {
                    self.record_pattern_effectful_vars(param);
                }
                self.walk_expr(body);
                self.pop_scope();
            }
            Decl::Let { value, .. } => {
                self.push_scope();
                self.walk_expr(value);
                self.pop_scope();
            }
            Decl::ImplDef { methods, .. } => {
                for m in methods {
                    self.push_scope();
                    self.walk_expr(&m.node.body);
                    self.pop_scope();
                }
            }
            Decl::HandlerDef { body, .. } => {
                for arm in &body.arms {
                    self.push_scope();
                    for param in &arm.node.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&arm.node.body);
                    if let Some(fb) = &arm.node.finally_block {
                        self.walk_expr(fb);
                    }
                    self.pop_scope();
                }
                if let Some(rc) = &body.return_clause {
                    self.push_scope();
                    for param in &rc.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&rc.body);
                    self.pop_scope();
                }
            }
            Decl::DictConstructor {
                super_dicts,
                methods,
                ..
            } => {
                for super_dict in super_dicts {
                    self.walk_expr(super_dict);
                }
                for m in methods {
                    self.push_scope();
                    self.walk_expr(m);
                    self.pop_scope();
                }
            }
            _ => {}
        }
    }

    fn fun_param_effectful_vars(
        &self,
        name: &str,
        params: &[Pat],
    ) -> (HashMap<String, Vec<String>>, HashSet<String>) {
        let mut effects = HashMap::new();
        let mut open_row = HashSet::new();
        let Some(info) = self.inputs.fun_sigs.get(name) else {
            return (effects, open_row);
        };
        for (idx, effs) in &info.param_absorbed_effects {
            let param_idx = idx + info.dict_param_count;
            if let Some(Pat::Var { name: pname, .. }) = params.get(param_idx) {
                effects.insert(pname.clone(), effs.clone());
            }
        }
        // Callback parameters whose type is an open-row function (`f: Unit ->
        // Unit needs {..e}`) have no named effects to absorb but must still
        // route through the CPS path so the caller's ambient evidence is
        // forwarded into them. `param_absorbed_effects` only tracks named
        // effects, so detect the open-row tail directly off the param types.
        for (idx, pty) in info.param_types.iter().enumerate() {
            let param_idx = idx + info.dict_param_count;
            if let Some(Pat::Var { name: pname, .. }) = params.get(param_idx)
                && util::has_open_effect_row(pty)
            {
                open_row.insert(pname.clone());
            }
        }
        (effects, open_row)
    }

    fn lookup_effectful_var(&self, name: &str) -> Option<Vec<String>> {
        for frame in self.scopes.iter().rev() {
            if let Some(effs) = frame.get(name) {
                return Some(effs.clone());
            }
        }
        None
    }

    fn lookup_open_row_var(&self, name: &str) -> bool {
        self.open_row_vars.iter().rev().any(|f| f.contains(name))
    }

    fn record_effectful_var(&mut self, name: String, effects: Vec<String>) {
        if let Some(frame) = self.scopes.last_mut() {
            frame.insert(name, effects);
        }
    }

    fn record_open_row_var(&mut self, name: String) {
        if let Some(frame) = self.open_row_vars.last_mut() {
            frame.insert(name);
        }
    }

    fn record_pattern_effectful_vars(&mut self, pat: &Pat) {
        match pat {
            Pat::Var { name, .. } => {
                if let Some(effects) = self.pattern_effects(pat)
                    && !effects.is_empty()
                {
                    self.record_effectful_var(name.clone(), effects);
                }
                if self.pattern_is_open_row_callable(pat) {
                    self.record_open_row_var(name.clone());
                }
            }
            Pat::Constructor { args, .. } | Pat::Tuple { elements: args, .. } => {
                for sub in args {
                    self.record_pattern_effectful_vars(sub);
                }
            }
            Pat::ListPat { elements, .. } => {
                for sub in elements {
                    self.record_pattern_effectful_vars(sub);
                }
            }
            Pat::ConsPat { head, tail, .. } => {
                self.record_pattern_effectful_vars(head);
                self.record_pattern_effectful_vars(tail);
            }
            Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
                for (_, sub) in fields {
                    if let Some(sub_pat) = sub {
                        self.record_pattern_effectful_vars(sub_pat);
                    }
                }
            }
            Pat::Or { patterns, .. } => {
                for sub in patterns {
                    self.record_pattern_effectful_vars(sub);
                }
            }
            Pat::StringPrefix { rest, .. } => self.record_pattern_effectful_vars(rest),
            Pat::BitStringPat { segments, .. } => {
                for seg in segments {
                    self.record_pattern_effectful_vars(&seg.value);
                }
            }
            Pat::Wildcard { .. } | Pat::Lit { .. } => {}
        }
    }

    /// True when the pattern binds a value whose function type has an
    /// open-row effect tail. This is tracked independently from named effects:
    /// `Unit -> Unit needs {Skip, ..e}` must classify as `RowForwarded`
    /// with pinned `Skip` ops, not as a closed `StaticOps(Skip)` call.
    fn pattern_is_open_row_callable(&self, pat: &Pat) -> bool {
        let Pat::Var { span, .. } = pat else {
            return false;
        };
        let Some(resolved) = self.inputs.check_result.type_at_span.get(span) else {
            return false;
        };
        if !matches!(resolved, crate::typechecker::Type::Fun(..)) {
            return false;
        }
        util::has_open_effect_row(resolved)
    }

    fn pattern_effects(&self, pat: &Pat) -> Option<Vec<String>> {
        let Pat::Var { span, .. } = pat else {
            return None;
        };
        let resolved = self.inputs.check_result.type_at_span.get(span)?;
        let mut effects: Vec<String> = crate::typechecker::effects_from_type(resolved)
            .into_iter()
            .collect();
        effects.sort();
        let canonical = self.canonicalize_effects(effects);
        if canonical.is_empty() {
            None
        } else {
            Some(canonical)
        }
    }

    fn walk_expr(&mut self, expr: &Expr) {
        if let Some(ty) = self.inputs.check_result.resolved_type_for_node(expr.id)
            && matches!(ty, crate::typechecker::Type::Fun(..))
        {
            let inferred =
                CallableAbi::from_type(&ty, |effects| self.canonicalize_effects(effects));
            self.plan.record_inferred_function_value(expr.id, inferred);
        }
        // Classify after children. Immediately-invoked lambda heads need the
        // completed body plan so an absorbed open callback row contributes to
        // the lambda's runtime ABI even when its type-at-node view is pure.
        self.walk_children(expr);
        if matches!(expr.kind, ExprKind::App { .. }) {
            let info = self.classify_app(expr);
            info.debug_check();
            self.trace.push(self.trace_entry(expr, &info));
            if let Some(evidence) = info.cps_call_abi().and_then(|abi| abi.evidence.clone())
                && let Some(lambda_evidence) = self.lambda_body_evidence.last_mut()
            {
                *lambda_evidence = EvidenceAbi::for_lambda_boundary(lambda_evidence, &evidence);
            }
            self.plan.record_call(expr.id, info);
            self.plan_app_function_value_boundaries(expr);
        }
    }

    fn plan_app_function_value_boundaries(&mut self, expr: &Expr) {
        let (head, _) = peel_app(expr);
        if !matches!(head.kind, ExprKind::Lambda { .. }) {
            return;
        }

        if let Some(call_abi) = self
            .plan
            .call(expr.id)
            .and_then(CallEffectInfo::cps_call_abi)
            .cloned()
        {
            self.plan
                .record_function_value_boundary(head.id, call_abi.clone(), call_abi);
        }
    }

    fn trace_entry(&self, expr: &Expr, info: &CallEffectInfo) -> CallEffectTraceEntry {
        let (head, args) = peel_app(expr);
        CallEffectTraceEntry {
            app_id: expr.id,
            head_id: head.id,
            head: head_debug_label(head),
            supplied_args: args.len(),
            shape: info.debug_label(),
        }
    }

    fn walk_children(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::App { func, arg } => {
                self.walk_expr(func);
                self.walk_expr(arg);
            }
            ExprKind::BinOp { left, right, .. } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }
            ExprKind::UnaryMinus { expr } => self.walk_expr(expr),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.walk_expr(cond);
                self.push_scope();
                self.walk_expr(then_branch);
                self.pop_scope();
                self.push_scope();
                self.walk_expr(else_branch);
                self.pop_scope();
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.walk_expr(scrutinee);
                for arm in arms {
                    self.push_scope();
                    self.record_pattern_effectful_vars(&arm.node.pattern);
                    if let Some(g) = &arm.node.guard {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&arm.node.body);
                    self.pop_scope();
                }
            }
            ExprKind::Block { stmts, .. } => {
                self.push_scope();
                self.local_fun_sigs.push(HashMap::new());
                for stmt in stmts {
                    self.walk_stmt(&stmt.node);
                }
                self.local_fun_sigs.pop();
                self.pop_scope();
            }
            ExprKind::Lambda { params, body, .. } => {
                self.push_scope();
                for param in params {
                    self.record_pattern_effectful_vars(param);
                }
                self.lambda_body_evidence.push(EvidenceAbi::default());
                self.walk_expr(body);
                let body_evidence = self
                    .lambda_body_evidence
                    .pop()
                    .expect("lambda evidence stack underflow");
                if !body_evidence.static_slots().is_empty() || body_evidence.is_open() {
                    self.lambda_head_evidence.insert(expr.id, body_evidence);
                }
                self.pop_scope();
            }
            ExprKind::FieldAccess { expr, .. } => self.walk_expr(expr),
            ExprKind::RecordCreate { fields, .. }
            | ExprKind::AnonRecordCreate { fields }
            | ExprKind::RecordBuild { fields, .. } => {
                for (_, _, e) in fields {
                    self.walk_expr(e);
                }
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.walk_expr(record);
                for (_, _, e) in fields {
                    self.walk_expr(e);
                }
            }
            ExprKind::EffectCall { args, .. } => {
                for a in args {
                    self.walk_expr(a);
                }
            }
            ExprKind::With { expr, handler } => {
                self.push_scope();
                self.walk_expr(expr);
                self.pop_scope();
                if let ast::Handler::Inline { items, .. } = handler.as_ref() {
                    for item in items {
                        match &item.node {
                            ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                                self.push_scope();
                                for param in &arm.params {
                                    self.record_pattern_effectful_vars(param);
                                }
                                self.walk_expr(&arm.body);
                                if let Some(fb) = &arm.finally_block {
                                    self.walk_expr(fb);
                                }
                                self.pop_scope();
                            }
                            ast::HandlerItem::Named(_) => {}
                        }
                    }
                }
            }
            ExprKind::Resume { value } => self.walk_expr(value),
            ExprKind::Tuple { elements } => {
                for e in elements {
                    self.walk_expr(e);
                }
            }
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                for (_, e) in bindings {
                    self.push_scope();
                    self.walk_expr(e);
                    self.pop_scope();
                }
                self.push_scope();
                self.walk_expr(success);
                self.pop_scope();
                for arm in else_arms {
                    self.push_scope();
                    self.record_pattern_effectful_vars(&arm.node.pattern);
                    if let Some(g) = &arm.node.guard {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&arm.node.body);
                    self.pop_scope();
                }
            }
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                for arm in arms {
                    self.push_scope();
                    self.record_pattern_effectful_vars(&arm.node.pattern);
                    if let Some(g) = &arm.node.guard {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&arm.node.body);
                    self.pop_scope();
                }
                if let Some((timeout, body)) = after_clause {
                    self.walk_expr(timeout);
                    self.walk_expr(body);
                }
            }
            ExprKind::BitString { segments } => {
                for seg in segments {
                    self.walk_expr(&seg.value);
                    if let Some(s) = &seg.size {
                        self.walk_expr(s);
                    }
                }
            }
            ExprKind::Ascription { expr, .. } => self.walk_expr(expr),
            ExprKind::HandlerExpr { body } => {
                for arm in &body.arms {
                    self.push_scope();
                    for param in &arm.node.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&arm.node.body);
                    if let Some(fb) = &arm.node.finally_block {
                        self.walk_expr(fb);
                    }
                    self.pop_scope();
                }
                if let Some(rc) = &body.return_clause {
                    self.push_scope();
                    for param in &rc.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&rc.body);
                    self.pop_scope();
                }
            }
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                self.walk_expr(dict)
            }
            ExprKind::ForeignCall { args, .. } => {
                for a in args {
                    self.walk_expr(a);
                }
            }
            // Leaves
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => {}
            // Surface syntax — should be desugared by now, but be permissive.
            ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {}
        }
    }

    fn walk_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { pattern, value, .. } => {
                self.walk_expr(value);
                // After walking the value, propagate effectful-binding info to
                // the binder. `call_effects` is the authoritative owner of
                // this lexical classification; the lowerer only consumes the
                // completed per-App map.
                let mut recorded = false;
                if let Pat::Var { name, .. } = pattern {
                    if let Some(effs) = self.inputs.let_effect_bindings.get(name)
                        && !effs.is_empty()
                    {
                        self.record_effectful_var(name.clone(), effs.clone());
                        recorded = true;
                    } else if let Some(effs) = self.value_effect_signature(value)
                        && !effs.is_empty()
                    {
                        self.record_effectful_var(name.clone(), effs);
                        recorded = true;
                    }
                }
                // Fall back to the binding's resolved type. This catches
                // bindings whose *type* is an effectful function value — e.g. a
                // partial application `let app = choose_string [route]` of type
                // `String -> String needs {..e}` — which `value_effect_signature`
                // misses because the partial application itself performs no
                // effects, so the call map records it as Pure. Reading the
                // binder's type also recovers open-row callables (`needs {..e}`
                // with no named effects), which the value-signature path never
                // tracks; without this, `app "/ok"` lowers as a pure 1-arg
                // apply against a 3-arity CPS function and crashes with a
                // badarity at runtime.
                if !recorded {
                    self.record_pattern_effectful_vars(pattern);
                }
            }
            Stmt::LetFun {
                id,
                name,
                body,
                guard,
                ..
            } => {
                // Mirror the lowerer: register the LetFun's signature into the
                // top local fun frame BEFORE walking its body so recursive
                // calls classify correctly.
                if let Some(sig) = self.let_fun_sig(*id, name) {
                    self.plan.record_declaration(*id, sig.abi.clone());
                    if let Some(frame) = self.local_fun_sigs.last_mut() {
                        frame.insert(name.clone(), sig);
                    }
                }
                if let Some(g) = guard {
                    self.push_scope();
                    self.walk_expr(g);
                    self.pop_scope();
                }
                self.push_scope();
                self.walk_expr(body);
                self.pop_scope();
            }
            Stmt::Expr(e) => self.walk_expr(e),
        }
    }

    /// If `value` is itself an effectful call, return its effect list. Used to
    /// promote `let g = factory()` so subsequent `g x` calls thread evidence.
    fn value_effect_signature(&self, value: &Expr) -> Option<Vec<String>> {
        let effects = self
            .plan
            .call(value.id)?
            .cps_call_abi()?
            .evidence
            .as_ref()?
            .static_slots()
            .to_vec();
        if effects.is_empty() {
            None
        } else {
            Some(effects)
        }
    }

    fn classify_app(&self, expr: &Expr) -> CallEffectInfo {
        let (head, args) = peel_app(expr);
        let arg_count = args.len();
        match &head.kind {
            ExprKind::Var { name } => self.classify_named_call(head.id, name, arg_count),
            ExprKind::QualifiedName { name, .. } => {
                self.classify_named_call(head.id, name, arg_count)
            }
            ExprKind::DictMethodAccess {
                dict,
                trait_name,
                method_index,
            } => self.classify_dict_method_call(dict, trait_name, *method_index, arg_count),
            ExprKind::Lambda { .. } => self.classify_typed_head_call(head.id, arg_count),
            // A field access yielding a function value (e.g. `s.run` where
            // `run: Int -> Int needs {Logger}` is a record field). The callee's
            // effect row lives on the field-access node's resolved type, so it
            // classifies exactly like a lambda head.
            ExprKind::FieldAccess { .. } => self.classify_typed_head_call(head.id, arg_count),
            // Other head shapes have no callee identity that resolves to an
            // effect row, so they classify as Pure. Add a branch here when a
            // new effectful head shape is introduced.
            _ => CallEffectInfo::pure(),
        }
    }

    /// Classify a call whose head is a typed value node (a `Lambda` literal or
    /// a `FieldAccess` yielding a function value). The effect row is derived
    /// from the typechecker's resolved type at that node. Pure heads yield
    /// `Pure`; effectful heads yield `StaticOps` (closed) or `RowForwarded`
    /// (open). Saturation isn't strictly required here — Saga's function values
    /// always match arrow arity at call sites; if `supplied == 0` we
    /// early-return Pure for safety.
    fn classify_typed_head_call(&self, head_id: NodeId, supplied: usize) -> CallEffectInfo {
        if supplied == 0 {
            return CallEffectInfo::pure();
        }
        let Some(shape) = self.lambda_head_shape(head_id) else {
            return CallEffectInfo::pure();
        };
        let Some(kind) = self.call_kind_from_cps_shape(&shape) else {
            return CallEffectInfo::pure();
        };
        CallEffectInfo::cps(kind, supplied)
    }

    /// Classify a call whose head is a `DictMethodAccess` node.
    ///
    /// Effect resolution starts from the trait method's declared effect
    /// signature. For concrete dicts, walk the dict expression to find the
    /// underlying `DictRef { name }`, peeling `App` chains for parameterized
    /// impls (e.g. `__dict_Show_List __dict_Show_String`), then union in the
    /// concrete method slot's impl effects.
    ///
    /// Where-bounded dispatch (dict from a function parameter) ends in a
    /// `Var` rather than `DictRef`, so only the trait method signature is
    /// available. Impl-specific extra effects are intentionally not assumed
    /// for polymorphic dispatch.
    fn classify_dict_method_call(
        &self,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
        supplied: usize,
    ) -> CallEffectInfo {
        if supplied == 0 {
            return CallEffectInfo::pure();
        }
        let method_sig = self
            .inputs
            .trait_method_effects_by_key
            .get(&(trait_name.to_string(), method_index));
        if let Some(sig) = method_sig
            && supplied < sig.user_arity
        {
            return CallEffectInfo::pure();
        }
        let mut effects = method_sig
            .map(|sig| sig.effects.clone())
            .unwrap_or_default();
        let is_open_row = method_sig.is_some_and(|sig| sig.is_open_row);

        // Peel `App` chain inside the dict expression.
        let mut current = dict;
        while let ExprKind::App { func, .. } = &current.kind {
            current = func;
        }
        match &current.kind {
            ExprKind::DictRef { name, .. } => {
                if let Some(impl_effects) = self
                    .inputs
                    .impl_method_effects_by_dict
                    .get(&(name.clone(), method_index))
                    .or_else(|| self.inputs.impl_effects_by_dict.get(name))
                {
                    effects.extend(impl_effects.iter().cloned());
                    effects.sort();
                    effects.dedup();
                }
                let ops = self.collect_op_keys(&effects);
                if ops.is_empty() && !is_open_row {
                    return CallEffectInfo::pure();
                }
                let kind = if is_open_row {
                    CallEffectKind::RowForwarded { static_ops: ops }
                } else {
                    CallEffectKind::StaticOps { ops }
                };
                CallEffectInfo::cps(kind, supplied)
            }
            ExprKind::Var { .. } => {
                // Where-bounded dispatch (dict from a function parameter):
                // the concrete impl is unknown, so only the trait method's
                // declared effects are available at this call site.
                let ops = self.collect_op_keys(&effects);
                if ops.is_empty() && !is_open_row {
                    return CallEffectInfo::pure();
                }
                let kind = if is_open_row {
                    CallEffectKind::RowForwarded { static_ops: ops }
                } else {
                    CallEffectKind::StaticOps { ops }
                };
                CallEffectInfo::cps(kind, supplied)
            }
            _ => CallEffectInfo::pure(),
        }
    }

    fn classify_named_call(&self, head_id: NodeId, name: &str, supplied: usize) -> CallEffectInfo {
        let pure = CallEffectInfo::pure;

        if supplied == 0 {
            return pure();
        }

        // Mirror `resolved_effects`: prefer ResolutionMap.effects, fall back
        // to fun_sigs (which holds CPS-expanded info for local funs).
        let resolved = self.inputs.resolved.get(&head_id);
        let resolved_shape =
            resolved.map(|resolved| self.runtime_shape_from_resolved_head(head_id, resolved));
        if resolved
            .is_some_and(|resolved| matches!(resolved.kind, ResolvedCodegenKind::Intrinsic { .. }))
        {
            return pure();
        }
        let resolved_env_shape =
            resolved.and_then(|resolved| self.runtime_shape_from_resolved_env(resolved, name));
        let resolved_cps_shape = resolved_shape
            .as_ref()
            .and_then(|abi| abi.cps_evidence())
            .or_else(|| {
                resolved_env_shape
                    .as_ref()
                    .and_then(|abi| abi.cps_evidence())
            });
        let canonical_name = resolved.map(|resolved| resolved.canonical_name.clone());
        let mut effects: Vec<String> = match resolved {
            Some(resolved) if !resolved.effects().is_empty() => resolved.effects().to_vec(),
            Some(_) => self
                .lookup_fun_sig(name, canonical_name.as_deref())
                .and_then(|sig| sig.abi.evidence.as_ref())
                .map(|evidence| evidence.static_slots().to_vec())
                .unwrap_or_default(),
            None => {
                // Not a resolved fun. Treat as effectful if it's an in-scope
                // effectful var recorded by this pre-pass's lexical scope
                // walk.
                let is_open_row = self.lookup_open_row_var(name);
                if let Some(effs) = self.lookup_effectful_var(name) {
                    let ops = self.collect_op_keys(&effs);
                    if ops.is_empty() && !is_open_row {
                        // Either the var carried no effects, or the effects
                        // didn't canonicalize against `effect_ops`. Either
                        // way the call is Pure and carries no callable ABI.
                        return pure();
                    }
                    let kind = if is_open_row {
                        CallEffectKind::RowForwarded { static_ops: ops }
                    } else {
                        CallEffectKind::StaticOps { ops }
                    };
                    // Effectful-var calls don't carry a precise user_arity;
                    // supplied > 0 is the gate (already checked above).
                    return CallEffectInfo::cps(kind, supplied);
                }
                if is_open_row {
                    return CallEffectInfo::cps(
                        CallEffectKind::RowForwarded {
                            static_ops: Vec::new(),
                        },
                        supplied,
                    );
                }
                return pure();
            }
        };
        if let Some(shape) = &resolved_cps_shape
            && !shape.static_slots().is_empty()
        {
            effects = shape.static_slots().to_vec();
        }

        // Need expanded arity from fun_sigs to compute user_arity.
        let Some(sig) = self.lookup_fun_sig(name, canonical_name.as_deref()) else {
            let ops = self.collect_op_keys(&effects);
            let is_open_row = resolved_cps_shape
                .as_ref()
                .map(EvidenceAbi::is_open)
                .unwrap_or_else(|| self.head_open_row.get(&head_id).copied().unwrap_or(false));
            // No FunSig snapshot. Effectful only if the effects canonicalized
            // to known ops or the callee has an open row; supplied is the
            // best-effort user arity. Pure calls carry no callable ABI.
            if ops.is_empty() && !is_open_row {
                return pure();
            }
            let kind = if is_open_row {
                CallEffectKind::RowForwarded { static_ops: ops }
            } else {
                CallEffectKind::StaticOps { ops }
            };
            return CallEffectInfo::cps(kind, supplied);
        };

        let ops = self.collect_op_keys(&effects);
        let has_ops = !ops.is_empty();
        // Prefer the per-call open-row signal (looked up by head NodeId) over
        // the FunSig-level flag, since FunSig keys may not capture every alias
        // for an imported function. The two should agree when both are set.
        let is_open_row = self
            .head_open_row
            .get(&head_id)
            .copied()
            .unwrap_or_else(|| {
                sig.abi.evidence.as_ref().is_some_and(EvidenceAbi::is_open)
                    || resolved_cps_shape.is_some_and(|shape| shape.is_open())
            });
        if effects.is_empty() && !is_open_row {
            return pure();
        }
        // Effectful/open-row arity = user + Evidence + ReturnK.
        let user_arity = sig.abi.user_arity;

        // Saturation gate from `call_performs_effect`.
        if user_arity == 0 || supplied < user_arity {
            return pure();
        }
        let kind = if !has_ops || is_open_row {
            CallEffectKind::RowForwarded { static_ops: ops }
        } else {
            CallEffectKind::StaticOps { ops }
        };

        CallEffectInfo::cps(kind, user_arity)
    }

    fn lookup_fun_sig(&self, name: &str, canonical_name: Option<&str>) -> Option<&FunSig> {
        // Lookup order mirrors resolved identity first: local LetFun frames
        // (innermost first), then canonical module identity, then the bare
        // spelling as a final fallback for unresolved/local surfaces.
        for frame in self.local_fun_sigs.iter().rev() {
            if let Some(s) = frame.get(name) {
                return Some(s);
            }
        }
        if let Some(c) = canonical_name
            && let Some(s) = self.inputs.fun_sigs.get(c)
        {
            return Some(s);
        }
        if let Some(s) = self.inputs.fun_sigs.get(name) {
            return Some(s);
        }
        None
    }

    fn lambda_head_shape(&self, lambda_id: NodeId) -> Option<EvidenceAbi> {
        if let Some(evidence) = self.lambda_head_evidence.get(&lambda_id) {
            return Some(evidence.clone());
        }
        if let Some(evidence) = self
            .plan
            .function_value(lambda_id)
            .and_then(FunctionValueAbiPlan::inferred)
            .and_then(|abi| abi.evidence.clone())
        {
            return Some(evidence);
        }
        let ty = self.inputs.check_result.resolved_type_for_node(lambda_id)?;
        self.callable_abi_from_type(&ty).cps_evidence()
    }

    fn let_fun_sig(&self, id: NodeId, name: &str) -> Option<FunSig> {
        if let Some(ty) = self.inputs.check_result.resolved_type_for_node(id) {
            let abi = self.callable_abi_from_type(&ty);
            let param_absorbed_effects = util::param_absorbed_effects_from_type(&ty)
                .into_iter()
                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                .collect();
            return Some(FunSig {
                abi,
                param_absorbed_effects,
                param_types: util::param_types_from_type(&ty),
                dict_param_count: 0,
            });
        }

        self.inputs.fun_sigs.get(name).cloned()
    }

    fn collect_op_keys(&self, effects: &[String]) -> Vec<OpKey> {
        let mut out = Vec::new();
        for eff in effects {
            // Effect names from `let_effect_bindings` and pattern bindings come
            // through bare; `effect_ops` is keyed canonically. Canonicalize
            // before lookup so the two stores agree.
            let canonical = self.canonicalize(eff);
            let family = crate::typechecker::applied_effect_family(&canonical);
            if let Some(op_names) = self.inputs.effect_ops.get(family) {
                for op in op_names {
                    out.push(OpKey {
                        effect: canonical.clone(),
                        op: op.clone(),
                    });
                }
            }
        }
        out.sort();
        out
    }

    fn callable_abi_from_type(&self, ty: &crate::typechecker::Type) -> CallableAbi {
        CallableAbi::from_type(ty, |effects| self.canonicalize_effects(effects))
    }

    fn runtime_shape_from_resolved_head(
        &self,
        head_id: NodeId,
        resolved: &crate::codegen::resolve::ResolvedSymbol,
    ) -> CallableAbi {
        let fallback_ty = self.inputs.check_result.resolved_type_for_node(head_id);
        CallableAbi::from_resolved_symbol(resolved, fallback_ty.as_ref(), |effects| {
            self.canonicalize_effects(effects)
        })
    }

    fn runtime_shape_from_resolved_env(
        &self,
        resolved: &crate::codegen::resolve::ResolvedSymbol,
        fallback_name: &str,
    ) -> Option<CallableAbi> {
        let candidates = [
            resolved.canonical_name.as_str(),
            resolved.name.as_str(),
            fallback_name,
        ];

        fn lookup_type(
            check: &CheckResult,
            candidates: &[&str],
        ) -> Option<crate::typechecker::Type> {
            candidates.iter().find_map(|name| {
                check
                    .env
                    .get(name)
                    .map(|scheme| check.sub.apply(&scheme.ty))
            })
        }

        let ty = lookup_type(self.inputs.check_result, &candidates).or_else(|| {
            resolved
                .source_module
                .as_deref()
                .and_then(|module| self.inputs.check_result.module_check_results().get(module))
                .and_then(|check| lookup_type(check, &candidates))
        })?;

        Some(self.callable_abi_from_type(&ty))
    }

    fn call_kind_from_cps_shape(&self, shape: &EvidenceAbi) -> Option<CallEffectKind> {
        let ops = self.collect_op_keys(shape.static_slots());
        if ops.is_empty() && !shape.is_open() {
            None
        } else if shape.is_open() {
            Some(CallEffectKind::RowForwarded { static_ops: ops })
        } else {
            Some(CallEffectKind::StaticOps { ops })
        }
    }
}

fn peel_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg } => {
                args.push(arg);
                current = func;
            }
            _ => {
                args.reverse();
                return (current, args);
            }
        }
    }
}

fn head_debug_label(head: &Expr) -> String {
    match &head.kind {
        ExprKind::Var { name } => format!("var({name})"),
        ExprKind::QualifiedName { module, name, .. } => format!("qualified({module}.{name})"),
        ExprKind::DictMethodAccess {
            trait_name,
            method_index,
            ..
        } => format!("dict-method({trait_name}#{method_index})"),
        ExprKind::DictSuperAccess {
            trait_name,
            supertrait_index,
            ..
        } => format!("dict-super({trait_name}#{supertrait_index})"),
        ExprKind::Lambda { params, .. } => format!("lambda/{}", params.len()),
        ExprKind::Constructor { name } => format!("ctor({name})"),
        ExprKind::DictRef { name } => format!("dict-ref({name})"),
        ExprKind::ForeignCall { module, func, args } => {
            format!("foreign({module}.{func}/{})", args.len())
        }
        ExprKind::EffectCall {
            qualifier,
            name,
            args,
            ..
        } => format!(
            "effect-call({}{name}!/{})",
            qualifier
                .as_ref()
                .map(|qualifier| format!("{qualifier}."))
                .unwrap_or_default(),
            args.len()
        ),
        ExprKind::Lit { value } => format!("lit({value:?})"),
        ExprKind::Tuple { elements } => format!("tuple/{}", elements.len()),
        ExprKind::RecordCreate { name, fields, .. } => format!("record({name}/{})", fields.len()),
        ExprKind::AnonRecordCreate { fields } => format!("anon-record/{}", fields.len()),
        ExprKind::RecordBuild { fields, .. } => format!("record-build/{}", fields.len()),
        ExprKind::HandlerExpr { .. } => "handler-expr".to_string(),
        ExprKind::App { .. } => "app-head".to_string(),
        ExprKind::BinOp { .. } => "binop".to_string(),
        ExprKind::UnaryMinus { .. } => "unary-minus".to_string(),
        ExprKind::If { .. } => "if".to_string(),
        ExprKind::Case { .. } => "case".to_string(),
        ExprKind::Block { .. } => "block".to_string(),
        ExprKind::FieldAccess { field, .. } => format!("field-access(.{field})"),
        ExprKind::RecordUpdate { .. } => "record-update".to_string(),
        ExprKind::With { .. } => "with".to_string(),
        ExprKind::Resume { .. } => "resume".to_string(),
        ExprKind::Do { .. } => "do".to_string(),
        ExprKind::Receive { .. } => "receive".to_string(),
        ExprKind::BitString { segments } => format!("bitstring/{}", segments.len()),
        ExprKind::Ascription { .. } => "ascription".to_string(),
        ExprKind::Pipe { .. } => "pipe".to_string(),
        ExprKind::BinOpChain { .. } => "binop-chain".to_string(),
        ExprKind::PipeBack { .. } => "pipe-back".to_string(),
        ExprKind::ComposeForward { .. } => "compose-forward".to_string(),
        ExprKind::Cons { .. } => "cons".to_string(),
        ExprKind::ListLit { elements, .. } => format!("list/{}", elements.len()),
        ExprKind::StringInterp { parts, .. } => format!("string-interp/{}", parts.len()),
        ExprKind::ListComprehension { qualifiers, .. } => {
            format!("list-comprehension/{}", qualifiers.len())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn op(effect: &str, op: &str) -> OpKey {
        OpKey {
            effect: effect.to_string(),
            op: op.to_string(),
        }
    }

    #[test]
    fn function_value_plan_keeps_inferred_implementation_and_boundary_distinct() {
        let node = NodeId(42);
        let inferred = CallableAbi::pure(1);
        let implementation = CallableAbi::cps(
            1,
            EvidenceAbi::new(["Main.Repo", "Main.Rollback<Std.String.String>"], true),
        );
        let boundary = CallableAbi::cps(
            1,
            EvidenceAbi::new(["Main.Rollback<Std.String.String>"], false),
        );

        let mut plan = EffectAbiPlan::default();
        plan.record_inferred_function_value(node, inferred.clone());
        plan.record_function_value_boundary(node, implementation.clone(), boundary.clone());

        let value = plan.function_value(node).expect("function-value plan");
        assert_eq!(value.inferred(), Some(&inferred));
        let contextual = value.contextual().expect("contextual boundary");
        assert_eq!(contextual.implementation(), &implementation);
        assert_eq!(contextual.boundary(), &boundary);
        assert_eq!(plan.function_value_boundary(node), Some(&boundary));
    }

    #[test]
    #[should_panic(expected = "conflicting call ABI")]
    fn checked_plan_merge_rejects_conflicting_facts() {
        let node = NodeId(7);
        let mut left = EffectAbiPlan::default();
        left.record_call(node, CallEffectInfo::pure());
        let mut right = EffectAbiPlan::default();
        right.record_call(
            node,
            CallEffectInfo::Cps(CallableAbi::cps(1, EvidenceAbi::closed(["Main.Log"]))),
        );
        left.merge_checked(&right);
    }

    #[test]
    #[should_panic(expected = "mutate a frozen plan")]
    fn frozen_plan_rejects_late_lowering_mutation() {
        let mut plan = EffectAbiPlan::default();
        plan.freeze();
        plan.record_call(NodeId(9), CallEffectInfo::pure());
    }

    #[test]
    fn call_effect_info_debug_labels_direct_and_cps_shapes() {
        assert_eq!(CallEffectInfo::pure().debug_label(), "direct");

        let static_info = CallEffectInfo::cps(
            CallEffectKind::StaticOps {
                ops: vec![
                    op("Std.Fail.Fail", "fail"),
                    op("Std.Console.Console", "print"),
                    op("Std.Console.Console", "read"),
                ],
            },
            2,
        );
        assert_eq!(
            static_info.debug_label(),
            r#"cps-static(2->4, effects=["Std.Console.Console", "Std.Fail.Fail"])"#
        );

        let row_info = CallEffectInfo::cps(
            CallEffectKind::RowForwarded {
                static_ops: vec![op("Std.Fail.Fail", "fail")],
            },
            1,
        );
        assert_eq!(
            row_info.debug_label(),
            r#"cps-row-forwarded(1->3, pinned_effects=["Std.Fail.Fail"])"#
        );
    }

    #[test]
    fn format_call_effect_trace_keeps_walk_order() {
        let trace = vec![
            CallEffectTraceEntry {
                app_id: NodeId(10),
                head_id: NodeId(7),
                head: "var(f)".to_string(),
                supplied_args: 1,
                shape: "direct".to_string(),
            },
            CallEffectTraceEntry {
                app_id: NodeId(12),
                head_id: NodeId(11),
                head: "qualified(Foo.bar)".to_string(),
                supplied_args: 2,
                shape: r#"cps-static(2->4, effects=["Std.Fail.Fail"])"#.to_string(),
            },
        ];

        assert_eq!(
            format_call_effect_trace("Example", &trace),
            concat!(
                "call-effects[Example]: 2 app(s)",
                "\n  app#10 head#7 var(f) / 1 -> direct",
                "\n  app#12 head#11 qualified(Foo.bar) / 2 -> ",
                r#"cps-static(2->4, effects=["Std.Fail.Fail"])"#
            )
        );
    }

    #[test]
    fn format_effect_op_trace_keeps_lowering_order() {
        let trace = vec![
            EffectOpTraceEntry {
                node_id: NodeId(20),
                effect: "Std.IO.Stdio".to_string(),
                op: "print".to_string(),
                source_args: 1,
                runtime_args: 1,
                shape: "evidence-lookup(static-index)".to_string(),
            },
            EffectOpTraceEntry {
                node_id: NodeId(25),
                effect: "Std.Actor.Actor".to_string(),
                op: "self".to_string(),
                source_args: 1,
                runtime_args: 0,
                shape: "direct-native(handler=Std.Actor.beam_actor)".to_string(),
            },
        ];

        assert_eq!(
            format_effect_op_trace("Example", &trace),
            concat!(
                "effect-ops[Example]: 2 op call(s)",
                "\n  op#20 Std.IO.Stdio.print / 1 source arg(s), ",
                "1 runtime arg(s) -> evidence-lookup(static-index)",
                "\n  op#25 Std.Actor.Actor.self / 1 source arg(s), ",
                "0 runtime arg(s) -> direct-native(handler=Std.Actor.beam_actor)"
            )
        );
    }
}
