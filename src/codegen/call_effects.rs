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
//! `RowForwarded` (open row). A call is pure only by a rule that says so
//! (see `Populator::classify_app`); a head no rule covers is an internal
//! compiler error.
//!
//! This module is intentionally a classifier, not a lowerer. It names the
//! ABI/evidence shape a call site needs; Core Erlang emission remains in
//! `codegen::lower`.

use std::collections::HashMap;

use crate::ast::{Decl, Expr, ExprKind, NodeId, Program, Stmt};
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectAbiPlan {
    declarations: HashMap<NodeId, CallableAbi>,
    calls: CallEffectMap,
    /// Facts read off the shape of the tree when the plan was made. Passes
    /// that run after planning move expressions into `let`s, so the lowerer
    /// reads these instead of looking at the shape again.
    ///
    /// Lambda id -> whether its innermost body is an effectful call or an
    /// applied operation. Decides the representation of a lambda that has no
    /// type of its own.
    lambda_bodies_effectful: HashMap<NodeId, bool>,
    /// Dictionary method id -> whether it performs an operation directly,
    /// which gives its slot the impl's own effects.
    dict_methods_performing: HashMap<NodeId, bool>,
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

    pub fn record_lambda_body_effectful(&mut self, lambda_id: NodeId, effectful: bool) {
        self.assert_mutable();
        self.lambda_bodies_effectful.insert(lambda_id, effectful);
    }

    pub fn lambda_body_effectful(&self, lambda_id: NodeId) -> Option<bool> {
        self.lambda_bodies_effectful.get(&lambda_id).copied()
    }

    pub fn record_dict_method_performing(&mut self, method_id: NodeId, performs: bool) {
        self.assert_mutable();
        self.dict_methods_performing.insert(method_id, performs);
    }

    pub fn dict_method_performing(&self, method_id: NodeId) -> Option<bool> {
        self.dict_methods_performing.get(&method_id).copied()
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
        self.lambda_bodies_effectful
            .extend(&other.lambda_bodies_effectful);
        self.dict_methods_performing
            .extend(&other.dict_methods_performing);
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
}

/// Read-only inputs the populator consults during its walk. Bundled into a
/// struct so the constructor doesn't carry a half-dozen reference parameters
/// that all lifetime-tie back to the same lowering invocation.
pub struct PopulatorInputs<'a> {
    /// The module being classified and its source, for reports and errors.
    pub module: &'a str,
    pub source_info: Option<&'a crate::codegen::lower::errors::SourceInfo>,
    pub resolved: &'a ResolutionMap,
    /// Origins of the nodes of the program that the generic fold copied.
    pub origins: &'a crate::codegen::generic_fold::NodeOrigins,
    pub check_result: &'a CheckResult,
    pub ctx: &'a CodegenContext,
    pub fun_sigs: &'a HashMap<String, FunSig>,
    /// Effect canonical name -> sorted op names.
    pub effect_ops: &'a HashMap<String, Vec<String>>,
    /// Bare effect name -> canonical effect name (mirrors `Lowerer::effect_canonical`).
    /// `effect_ops` is keyed canonically.
    pub effect_canonical: &'a HashMap<String, String>,
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
    /// Stack of local function frames mirroring the lowerer's dynamic
    /// `fun_info` mutations for `Stmt::LetFun`. Maps name -> FunSig.
    local_fun_sigs: Vec<HashMap<String, FunSig>>,
    /// Resolved call head NodeId -> whether the callee's effect row is open.
    head_open_row: HashMap<NodeId, bool>,
    /// Name of the declaration being walked, for reports and errors.
    current_decl: String,
}

impl<'a> Populator<'a> {
    pub fn new(inputs: PopulatorInputs<'a>) -> Self {
        let head_open_row = Self::collect_head_open_rows(&inputs);
        Populator {
            inputs,
            plan: EffectAbiPlan::default(),
            trace: Vec::new(),
            local_fun_sigs: Vec::new(),
            head_open_row,
            current_decl: String::new(),
        }
    }

    /// Where `expr` is: `Module.function at file:line` (or a byte offset
    /// when the source text is not at hand).
    fn location(&self, expr: &Expr) -> String {
        let at = match self.inputs.source_info {
            Some(info) => format!("{}:{}", info.file, info.line_number(&expr.span)),
            None => format!("offset {}", expr.span.start),
        };
        format!("{}.{} at {at}", self.inputs.module, self.current_decl)
    }

    /// No rule says whether the call through `head` is pure or uses the CPS
    /// convention. Nothing is assumed: this is a compiler bug.
    fn unknown_head(&self, head: &Expr) -> ! {
        panic!(
            "internal compiler error: cannot classify the call through {} in {}: \
             the head has no type and is not a known function, constructor, \
             dictionary or operation",
            head_debug_label(head),
            self.location(head)
        )
    }

    fn canonicalize(&self, bare: &str) -> String {
        self.inputs
            .effect_canonical
            .get(bare)
            .cloned()
            .unwrap_or_else(|| bare.to_string())
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

    fn walk_decl(&mut self, decl: &Decl) {
        self.current_decl = match decl {
            Decl::FunBinding { name, .. }
            | Decl::Let { name, .. }
            | Decl::HandlerDef { name, .. }
            | Decl::DictConstructor { name, .. } => name.clone(),
            _ => String::new(),
        };
        match decl {
            Decl::FunBinding {
                id,
                name,
                guard,
                body,
                ..
            } => {
                if let Some(sig) = self.inputs.fun_sigs.get(name) {
                    self.plan.record_declaration(*id, sig.abi.clone());
                }
                if let Some(guard) = guard {
                    self.walk_expr(guard);
                }
                self.walk_expr(body);
            }
            Decl::Let { value, .. } => self.walk_expr(value),
            Decl::ImplDef { methods, .. } => {
                for m in methods {
                    self.walk_expr(&m.node.body);
                }
            }
            Decl::HandlerDef { body, .. } => {
                for arm in body.arms.iter().map(|arm| &arm.node) {
                    self.walk_expr(&arm.body);
                    if let Some(fb) = &arm.finally_block {
                        self.walk_expr(fb);
                    }
                }
                if let Some(rc) = &body.return_clause {
                    self.walk_expr(&rc.body);
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
                    self.plan.record_dict_method_performing(
                        m.id,
                        crate::codegen::effect_position::mentions_operation(m),
                    );
                    self.walk_expr(m);
                }
            }
            _ => {}
        }
    }

    fn walk_expr(&mut self, expr: &Expr) {
        // Classify after children: an over-applied named call and a lambda
        // head without a type of its own read their inner calls' entries.
        self.walk_children(expr);
        if matches!(expr.kind, ExprKind::App { .. }) {
            let info = self.classify_app(expr);
            info.debug_check();
            self.trace.push(self.trace_entry(expr, &info));
            self.plan.record_call(expr.id, info);
        }
        if matches!(expr.kind, ExprKind::Lambda { .. }) {
            let effectful = self.untyped_lambda_head_is_effectful(expr);
            self.plan.record_lambda_body_effectful(expr.id, effectful);
        }
    }

    /// A lambda head that has no entry in the type table (a node made after
    /// typechecking). It is a tagged closure when evaluating its body
    /// performs an effect: an effectful call or an applied operation, in
    /// any position that is not a body of its own. `Lowerer::lambda_is_tagged`
    /// reads the answer from the plan to decide how the lambda is lowered.
    fn untyped_lambda_head_is_effectful(&self, head: &Expr) -> bool {
        if !matches!(head.kind, ExprKind::Lambda { .. }) {
            return false;
        }
        let mut body = head;
        while let ExprKind::Lambda { body: inner, .. } = &body.kind {
            body = inner.as_ref();
        }
        crate::codegen::effect_position::is_effectful(body, &|node| {
            (self.plan.call(node.id)).is_some_and(CallEffectInfo::is_cps_call)
                || util::collect_effect_call(node).is_some()
        })
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

    /// Walk the sub-expressions of `expr`. Every `App` node of a chain is
    /// visited (each gets a plan entry); a block opens a frame for its local
    /// functions; everything else is read off the `children` table.
    fn walk_children(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::App { func, arg } => {
                self.walk_expr(func);
                self.walk_expr(arg);
            }
            ExprKind::Block { stmts, .. } => {
                self.local_fun_sigs.push(HashMap::new());
                for stmt in stmts {
                    self.walk_stmt(&stmt.node);
                }
                self.local_fun_sigs.pop();
            }
            _ => {
                for (_, child) in crate::codegen::effect_position::children(expr) {
                    self.walk_expr(child);
                }
            }
        }
    }

    fn walk_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { value, .. } => self.walk_expr(value),
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
                if let Some(sig) = self.let_fun_sig(*id) {
                    self.plan.record_declaration(*id, sig.abi.clone());
                    if let Some(frame) = self.local_fun_sigs.last_mut() {
                        frame.insert(name.clone(), sig);
                    }
                }
                if let Some(g) = guard {
                    self.walk_expr(g);
                }
                self.walk_expr(body);
            }
            Stmt::Expr(e) => self.walk_expr(e),
        }
    }

    /// Tagged closures: the CPS call shape of a call through a function
    /// value. The callee finds its handlers by tag, so the caller's frame is
    /// passed unchanged.
    fn tagged_value_call(supplied: usize) -> CallEffectInfo {
        CallEffectInfo::Cps(CallableAbi::cps(
            supplied,
            EvidenceAbi::new(Vec::<String>::new(), true),
        ))
    }

    /// The type of a node of the program: read from the module the generic
    /// fold copied it from, when it did.
    fn node_type(&self, node_id: NodeId) -> Option<&crate::typechecker::Type> {
        let check = self.inputs.check_result;
        match self.inputs.origins.get(&node_id) {
            Some((Some(module), id)) => {
                let compiled = self.inputs.ctx.modules.get(module.as_ref())?;
                (compiled.expr_types.get(id)).or_else(|| compiled.type_at_node.get(id))
            }
            Some((None, id)) => (check.expr_types.get(id)).or_else(|| check.type_at_node.get(id)),
            None => (check.expr_types.get(&node_id)).or_else(|| check.type_at_node.get(&node_id)),
        }
    }

    /// Tagged closures: classify a call through a function value from the
    /// callee's own type. The call is effectful when any arrow consumed by
    /// the supplied arguments carries effects or an open row.
    fn classify_value_call_from_type(
        &self,
        callee_id: NodeId,
        supplied: usize,
    ) -> Option<CallEffectInfo> {
        let ty = self.node_type(callee_id)?;
        Some(
            if crate::codegen::lower::tagged_consumed_arrows_effectful(ty, supplied) {
                Self::tagged_value_call(supplied)
            } else {
                CallEffectInfo::pure()
            },
        )
    }

    /// Classification of every call shape. Each call is classified by the
    /// first rule that applies to its head; there is no default.
    ///
    /// 1. An applied operation is a perform, lowered by the effect-call
    ///    path: not a CPS *call*.
    /// 2. A constructor or a dictionary constructor builds a value: pure.
    /// 3. A name resolved to an intrinsic: pure.
    /// 4. A name that is a known function (top-level, imported, external or
    ///    block-local): its declared signature.
    /// 5. A dictionary method: the trait method's declared signature, plus
    ///    the impl's own effects when the dictionary is statically known.
    /// 6. Anything with a recorded type (a function value): CPS when an
    ///    arrow the arguments consume carries effects or an open row.
    /// 7. A lambda made after typechecking: CPS when its body performs.
    fn classify_app(&self, expr: &Expr) -> CallEffectInfo {
        let (head, args) = peel_app(expr);
        let supplied = args.len();
        match &head.kind {
            ExprKind::EffectCall { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::DictRef { .. } => CallEffectInfo::pure(),
            ExprKind::Var { name } | ExprKind::QualifiedName { name, .. } => {
                let resolved = self.inputs.resolved.get(&head.id);
                if resolved.is_some_and(|resolved| {
                    matches!(resolved.kind, ResolvedCodegenKind::Intrinsic { .. })
                }) {
                    return CallEffectInfo::pure();
                }
                let canonical = resolved.map(|resolved| resolved.canonical_name.clone());
                let is_local_fun = self
                    .local_fun_sigs
                    .iter()
                    .any(|frame| frame.contains_key(name));
                let known_arity = (resolved.is_some() || is_local_fun)
                    .then(|| self.lookup_fun_sig(name, canonical.as_deref()))
                    .flatten()
                    .map(|sig| sig.abi.user_arity);
                match known_arity {
                    // A named function applied to more arguments than it
                    // takes: the saturated call runs first and its result is
                    // then called as a function value.
                    Some(arity) if arity > 0 && arity < supplied => {
                        let mut inner = expr;
                        for _ in arity..supplied {
                            let ExprKind::App { func, .. } = &inner.kind else {
                                unreachable!("over-applied call is shorter than its arguments");
                            };
                            inner = func;
                        }
                        let inner_is_cps = self
                            .plan
                            .call(inner.id)
                            .is_some_and(CallEffectInfo::is_cps_call);
                        if inner_is_cps {
                            return Self::tagged_value_call(supplied);
                        }
                        match self.classify_value_call_from_type(inner.id, supplied - arity) {
                            Some(rest) if rest.is_cps_call() => Self::tagged_value_call(supplied),
                            Some(_) => CallEffectInfo::pure(),
                            None => self.unknown_head(inner),
                        }
                    }
                    Some(arity) if arity > 0 => self.classify_named_call(head.id, name, supplied),
                    // A constant holding a function, or anything that is not a
                    // known function: a function value. A resolved name with
                    // no type of its own still has its declared signature.
                    _ => self
                        .classify_value_call_from_type(head.id, supplied)
                        .or_else(|| {
                            resolved.map(|_| self.classify_named_call(head.id, name, supplied))
                        })
                        .unwrap_or_else(|| self.unknown_head(head)),
                }
            }
            ExprKind::DictMethodAccess {
                dict,
                trait_name,
                method_index,
            } => {
                let declared =
                    self.classify_dict_method_call(dict, trait_name, *method_index, supplied);
                match declared {
                    Some(declared) if declared.is_cps_call() => declared,
                    _ => self
                        .classify_value_call_from_type(head.id, supplied)
                        .or(declared)
                        .unwrap_or_else(|| self.unknown_head(head)),
                }
            }
            _ => self
                .classify_value_call_from_type(head.id, supplied)
                .unwrap_or_else(|| match &head.kind {
                    ExprKind::Lambda { .. } if self.untyped_lambda_head_is_effectful(head) => {
                        Self::tagged_value_call(supplied)
                    }
                    ExprKind::Lambda { .. } => CallEffectInfo::pure(),
                    _ => self.unknown_head(head),
                }),
        }
    }

    /// Classify a call whose head is a `DictMethodAccess` node, from the
    /// method's declared signature. `None` when no declaration is known.
    ///
    /// The signature is the trait's. For a statically known dictionary
    /// (the dict expression is rooted at a `DictRef`, peeling `App` chains
    /// of parameterized impls such as `__dict_Show_List __dict_Show_String`)
    /// the concrete method slot's impl effects are added, and a trait this
    /// module does not know (a call that arrived by inlining a body of
    /// another module) is read off the dictionary's own constructor.
    ///
    /// For any other dictionary (a `where`-bound parameter, a superclass
    /// projection, a dictionary literal made by elaboration) the concrete
    /// impl is unknown and only the trait's declaration applies.
    fn classify_dict_method_call(
        &self,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
        supplied: usize,
    ) -> Option<CallEffectInfo> {
        let mut root = dict;
        while let ExprKind::App { func, .. } = &root.kind {
            root = func;
        }
        let known_dict = match &root.kind {
            ExprKind::DictRef { name, .. } => Some(name),
            _ => None,
        };
        let sig = (self.inputs.trait_method_effects_by_key)
            .get(&(trait_name.to_string(), method_index))
            .cloned()
            .or_else(|| self.dict_constructor_method_sig(known_dict?, method_index))?;
        if supplied < sig.user_arity {
            return Some(CallEffectInfo::pure());
        }
        let mut effects = sig.effects;
        if let Some(name) = known_dict
            && let Some(impl_effects) = (self.inputs.impl_method_effects_by_dict)
                .get(&(name.clone(), method_index))
                .or_else(|| self.inputs.impl_effects_by_dict.get(name))
        {
            effects.extend(impl_effects.iter().cloned());
            effects.sort();
            effects.dedup();
        }
        let ops = self.collect_op_keys(&effects);
        Some(if sig.is_open_row {
            CallEffectInfo::cps(CallEffectKind::RowForwarded { static_ops: ops }, supplied)
        } else {
            CallEffectInfo::cps(CallEffectKind::StaticOps { ops }, supplied)
        })
    }

    /// The declared signature of method `method_index` of the dictionary
    /// constructor `dict`, wherever it is defined.
    fn dict_constructor_method_sig(
        &self,
        dict: &str,
        method_index: usize,
    ) -> Option<TraitMethodEffectSig> {
        let decls = (self.inputs.ctx.modules.values()).flat_map(|m| &m.elaborated);
        decls.into_iter().find_map(|decl| match decl {
            Decl::DictConstructor {
                name,
                methods,
                method_effects,
                method_open_rows,
                ..
            } if name == dict => match &methods.get(method_index)?.kind {
                ExprKind::Lambda { params, .. } => Some(TraitMethodEffectSig {
                    effects: method_effects.get(method_index)?.clone(),
                    is_open_row: *method_open_rows.get(method_index)?,
                    user_arity: params.len(),
                }),
                _ => None,
            },
            _ => None,
        })
    }

    /// Classify a call to a known function from its declared signature.
    fn classify_named_call(&self, head_id: NodeId, name: &str, supplied: usize) -> CallEffectInfo {
        let pure = CallEffectInfo::pure;

        if supplied == 0 {
            return pure();
        }

        // Mirror `resolved_effects`: prefer ResolutionMap.effects, fall back
        // to fun_sigs (which holds CPS-expanded info for local funs).
        let resolved = self.inputs.resolved.get(&head_id);
        let resolved_shape = resolved.map(CallableAbi::from_resolved_symbol);
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
            // A block-local function, or a resolved one that declares its
            // effects only through its own signature.
            _ => self
                .lookup_fun_sig(name, canonical_name.as_deref())
                .and_then(|sig| sig.abi.evidence.as_ref())
                .map(|evidence| evidence.static_slots().to_vec())
                .unwrap_or_default(),
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

    fn let_fun_sig(&self, id: NodeId) -> Option<FunSig> {
        let abi = self.callable_abi_from_type(self.node_type(id)?);
        Some(FunSig { abi })
    }

    fn collect_op_keys(&self, effects: &[String]) -> Vec<OpKey> {
        let mut out = Vec::new();
        for eff in effects {
            // `effect_ops` is keyed canonically; canonicalize before lookup.
            let canonical = self.canonicalize(eff);
            if let Some(op_names) = self.inputs.effect_ops.get(&canonical) {
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
