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

use std::collections::HashMap;

use crate::ast::{self, Decl, Expr, ExprKind, NodeId, Pat, Program, Stmt};
use crate::codegen::CodegenContext;
use crate::codegen::lower::util;
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use crate::typechecker::CheckResult;

/// Per-call metadata. Keyed by the `NodeId` of an `App` node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallEffectInfo {
    pub kind: CallEffectKind,
    /// Logical user-argument count (excludes evidence and return_k).
    ///
    /// **Invariant**: when `kind == CallEffectKind::Pure`, `user_arity` is
    /// always `0`. The lowerer never reads `user_arity` on `Pure` entries,
    /// and pinning the value to a single canonical zero prevents drift if a
    /// future producer is added. Construct via [`CallEffectInfo::pure()`]
    /// or [`CallEffectInfo::with_ops()`] to get the invariant enforced by
    /// construction; ad-hoc construction must call
    /// [`CallEffectInfo::debug_check()`] (debug builds verify it).
    pub user_arity: usize,
    /// Whether this call accepts a return continuation (i.e. it is effectful).
    pub needs_return_k: bool,
}

impl CallEffectInfo {
    /// Pure call. No evidence threading, no return continuation.
    pub fn pure() -> Self {
        CallEffectInfo {
            kind: CallEffectKind::Pure,
            user_arity: 0,
            needs_return_k: false,
        }
    }

    /// Debug-builds-only invariant check: Pure entries must have user_arity 0
    /// and needs_return_k == false. Call after ad-hoc construction.
    #[inline]
    pub fn debug_check(&self) {
        if cfg!(debug_assertions) && matches!(self.kind, CallEffectKind::Pure) {
            debug_assert_eq!(
                self.user_arity, 0,
                "CallEffectInfo: Pure kind requires user_arity == 0"
            );
            debug_assert!(
                !self.needs_return_k,
                "CallEffectInfo: Pure kind requires needs_return_k == false"
            );
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallEffectKind {
    /// Pure call. No effect threading.
    Pure,
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

/// Snapshot of the per-function metadata the populator needs. Built by the
/// Lowerer from its own `FunInfo` table once `init_module` has finished.
#[derive(Debug, Clone, Default)]
pub struct FunSig {
    /// Expanded arity (base user args + per-op handler params + return_k).
    pub arity: usize,
    /// Sorted, canonical effect names from the `needs` clause.
    pub effects: Vec<String>,
    /// param-index -> absorbed effects (for HOF effect absorption).
    pub param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// True if the callee's effect row has an open tail (`needs {Foo, ..e}`).
    /// Open-row callees produce `RowForwarded` rather than `StaticOps`.
    pub is_open_row: bool,
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
    /// `needs` clause. Sourced from `TraitImplDict.impl_effects` (both the
    /// active module's and imported modules'). Used to classify
    /// `App(DictMethodAccess { dict, .. }, ...)` call sites: walk the dict
    /// expression to find the underlying `DictRef { name }`, then look up
    /// effects here.
    pub impl_effects_by_dict: &'a HashMap<String, Vec<String>>,
}

/// Pre-pass walker. Constructed with the data sources it needs and consumed by
/// `populate(program)`.
pub struct Populator<'a> {
    inputs: PopulatorInputs<'a>,
    map: CallEffectMap,
    /// Stack of lexical scopes. Each frame maps a bound name to the absorbed
    /// effects that calls of that name should thread.
    scopes: Vec<HashMap<String, Vec<String>>>,
    /// Stack of local function frames mirroring the lowerer's dynamic
    /// `fun_info` mutations for `Stmt::LetFun`. Maps name -> FunSig.
    local_fun_sigs: Vec<HashMap<String, FunSig>>,
    /// Resolved call head NodeId -> whether the callee's effect row is open.
    head_open_row: HashMap<NodeId, bool>,
}

impl<'a> Populator<'a> {
    pub fn new(inputs: PopulatorInputs<'a>) -> Self {
        let head_open_row = Self::collect_head_open_rows(&inputs);
        Populator {
            inputs,
            map: HashMap::new(),
            scopes: Vec::new(),
            local_fun_sigs: Vec::new(),
            head_open_row,
        }
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
            let open = match &resolved.kind {
                ResolvedCodegenKind::BeamFunction {
                    erlang_mod: None, ..
                } => inputs
                    .check_result
                    .env
                    .get(&resolved.name)
                    .map(|s| util::has_open_effect_row(&inputs.check_result.sub.apply(&s.ty)))
                    .unwrap_or(false),
                _ => inputs
                    .ctx
                    .modules
                    .get(resolved.source_module.as_deref().unwrap_or_default())
                    .and_then(|m| {
                        m.codegen_info
                            .exports
                            .iter()
                            .find(|(n, _)| n == &resolved.name)
                            .map(|(_, scheme)| util::has_open_effect_row(&scheme.ty))
                    })
                    .unwrap_or(false),
            };
            out.insert(*node_id, open);
        }
        out
    }

    pub fn populate(mut self, program: &Program) -> CallEffectMap {
        for decl in program {
            self.walk_decl(decl);
        }
        self.map
    }

    fn walk_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::FunBinding {
                name, params, body, ..
            } => {
                let frame = self.fun_param_effectful_vars(name, params);
                self.scopes.push(frame);
                self.walk_expr(body);
                self.scopes.pop();
            }
            Decl::Val { value, .. } | Decl::Let { value, .. } => {
                self.scopes.push(HashMap::new());
                self.walk_expr(value);
                self.scopes.pop();
            }
            Decl::ImplDef { methods, .. } => {
                for m in methods {
                    self.scopes.push(HashMap::new());
                    self.walk_expr(&m.node.body);
                    self.scopes.pop();
                }
            }
            Decl::HandlerDef { body, .. } => {
                for arm in &body.arms {
                    self.scopes.push(HashMap::new());
                    for param in &arm.node.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&arm.node.body);
                    if let Some(fb) = &arm.node.finally_block {
                        self.walk_expr(fb);
                    }
                    self.scopes.pop();
                }
                if let Some(rc) = &body.return_clause {
                    self.scopes.push(HashMap::new());
                    for param in &rc.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&rc.body);
                    self.scopes.pop();
                }
            }
            Decl::DictConstructor { methods, .. } => {
                for m in methods {
                    self.scopes.push(HashMap::new());
                    self.walk_expr(m);
                    self.scopes.pop();
                }
            }
            _ => {}
        }
    }

    fn fun_param_effectful_vars(&self, name: &str, params: &[Pat]) -> HashMap<String, Vec<String>> {
        let mut out = HashMap::new();
        let Some(info) = self.inputs.fun_sigs.get(name) else {
            return out;
        };
        for (idx, effs) in &info.param_absorbed_effects {
            if let Some(Pat::Var { name: pname, .. }) = params.get(*idx) {
                out.insert(pname.clone(), effs.clone());
            }
        }
        out
    }

    fn lookup_effectful_var(&self, name: &str) -> Option<Vec<String>> {
        for frame in self.scopes.iter().rev() {
            if let Some(effs) = frame.get(name) {
                return Some(effs.clone());
            }
        }
        None
    }

    fn record_effectful_var(&mut self, name: String, effects: Vec<String>) {
        if let Some(frame) = self.scopes.last_mut() {
            frame.insert(name, effects);
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

    fn pattern_effects(&self, pat: &Pat) -> Option<Vec<String>> {
        let Pat::Var { span, .. } = pat else {
            return None;
        };
        let ty = self.inputs.check_result.type_at_span.get(span)?;
        let mut effects: Vec<String> = crate::typechecker::effects_from_type(ty)
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
        // Tag App nodes (must be done before recursing so head/args don't
        // mutate scope before classification).
        if matches!(expr.kind, ExprKind::App { .. }) {
            let info = self.classify_app(expr);
            info.debug_check();
            self.map.insert(expr.id, info);
        }
        self.walk_children(expr);
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
                self.scopes.push(HashMap::new());
                self.walk_expr(then_branch);
                self.scopes.pop();
                self.scopes.push(HashMap::new());
                self.walk_expr(else_branch);
                self.scopes.pop();
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.walk_expr(scrutinee);
                for arm in arms {
                    self.scopes.push(HashMap::new());
                    self.record_pattern_effectful_vars(&arm.node.pattern);
                    if let Some(g) = &arm.node.guard {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&arm.node.body);
                    self.scopes.pop();
                }
            }
            ExprKind::Block { stmts, .. } => {
                self.scopes.push(HashMap::new());
                self.local_fun_sigs.push(HashMap::new());
                for stmt in stmts {
                    self.walk_stmt(&stmt.node);
                }
                self.local_fun_sigs.pop();
                self.scopes.pop();
            }
            ExprKind::Lambda { body, .. } => {
                self.scopes.push(HashMap::new());
                self.walk_expr(body);
                self.scopes.pop();
            }
            ExprKind::FieldAccess { expr, .. } => self.walk_expr(expr),
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
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
                self.scopes.push(HashMap::new());
                self.walk_expr(expr);
                self.scopes.pop();
                if let ast::Handler::Inline { items, .. } = handler.as_ref() {
                    for item in items {
                        match &item.node {
                            ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                                self.scopes.push(HashMap::new());
                                for param in &arm.params {
                                    self.record_pattern_effectful_vars(param);
                                }
                                self.walk_expr(&arm.body);
                                if let Some(fb) = &arm.finally_block {
                                    self.walk_expr(fb);
                                }
                                self.scopes.pop();
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
                    self.scopes.push(HashMap::new());
                    self.walk_expr(e);
                    self.scopes.pop();
                }
                self.scopes.push(HashMap::new());
                self.walk_expr(success);
                self.scopes.pop();
                for arm in else_arms {
                    self.scopes.push(HashMap::new());
                    self.record_pattern_effectful_vars(&arm.node.pattern);
                    if let Some(g) = &arm.node.guard {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&arm.node.body);
                    self.scopes.pop();
                }
            }
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                for arm in arms {
                    self.scopes.push(HashMap::new());
                    self.record_pattern_effectful_vars(&arm.node.pattern);
                    if let Some(g) = &arm.node.guard {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&arm.node.body);
                    self.scopes.pop();
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
                    self.scopes.push(HashMap::new());
                    for param in &arm.node.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&arm.node.body);
                    if let Some(fb) = &arm.node.finally_block {
                        self.walk_expr(fb);
                    }
                    self.scopes.pop();
                }
                if let Some(rc) = &body.return_clause {
                    self.scopes.push(HashMap::new());
                    for param in &rc.params {
                        self.record_pattern_effectful_vars(param);
                    }
                    self.walk_expr(&rc.body);
                    self.scopes.pop();
                }
            }
            ExprKind::DictMethodAccess { dict, .. } => self.walk_expr(dict),
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
                // the binder, mirroring the lowerer's `current_effectful_vars`
                // mutation in `lower_block`.
                if let Pat::Var { name, .. } = pattern {
                    if let Some(effs) = self.inputs.let_effect_bindings.get(name)
                        && !effs.is_empty()
                    {
                        self.record_effectful_var(name.clone(), effs.clone());
                    } else if let Some(effs) = self.value_effect_signature(value)
                        && !effs.is_empty()
                    {
                        self.record_effectful_var(name.clone(), effs);
                    }
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
                if let Some(sig) = self.let_fun_sig(*id, name)
                    && let Some(frame) = self.local_fun_sigs.last_mut()
                {
                    frame.insert(name.clone(), sig);
                }
                if let Some(g) = guard {
                    self.scopes.push(HashMap::new());
                    self.walk_expr(g);
                    self.scopes.pop();
                }
                self.scopes.push(HashMap::new());
                self.walk_expr(body);
                self.scopes.pop();
            }
            Stmt::Expr(e) => self.walk_expr(e),
        }
    }

    /// If `value` is itself an effectful call, return its effect list. Used to
    /// promote `let g = factory()` so subsequent `g x` calls thread evidence.
    fn value_effect_signature(&self, value: &Expr) -> Option<Vec<String>> {
        match self.map.get(&value.id)?.kind.clone() {
            CallEffectKind::Pure => None,
            CallEffectKind::StaticOps { ops }
            | CallEffectKind::RowForwarded { static_ops: ops } => {
                let mut effects: Vec<String> = ops.into_iter().map(|k| k.effect).collect();
                effects.sort();
                effects.dedup();
                if effects.is_empty() {
                    None
                } else {
                    Some(effects)
                }
            }
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
            ExprKind::DictMethodAccess { dict, .. } => {
                self.classify_dict_method_call(dict, arg_count)
            }
            ExprKind::Lambda { .. } => self.classify_lambda_call(head.id, arg_count),
            // Other head shapes have no callee identity that resolves to an
            // effect row, so they classify as Pure. Add a branch here when a
            // new effectful head shape is introduced.
            _ => CallEffectInfo::pure(),
        }
    }

    /// Classify a call whose head is a `Lambda`. The lambda's effect row is
    /// derived from the typechecker's `type_at_node`. Pure lambdas yield
    /// `Pure`; effectful lambdas yield `StaticOps` (closed) or `RowForwarded`
    /// (open). Saturation isn't strictly required here — Saga's lambdas
    /// always match arrow arity at call sites; if `supplied == 0` we
    /// early-return Pure for safety.
    fn classify_lambda_call(&self, lambda_id: NodeId, supplied: usize) -> CallEffectInfo {
        if supplied == 0 {
            return CallEffectInfo::pure();
        }
        let Some((effects, is_open_row)) = self.lambda_head_effects(lambda_id) else {
            return CallEffectInfo::pure();
        };
        if effects.is_empty() {
            return CallEffectInfo::pure();
        }
        let ops = self.collect_op_keys(&effects);
        if ops.is_empty() {
            return CallEffectInfo::pure();
        }
        let kind = if is_open_row {
            CallEffectKind::RowForwarded { static_ops: ops }
        } else {
            CallEffectKind::StaticOps { ops }
        };
        CallEffectInfo {
            kind,
            user_arity: supplied,
            needs_return_k: true,
        }
    }

    /// Classify a call whose head is a `DictMethodAccess` node.
    ///
    /// Effect resolution: walk the dict expression to find the underlying
    /// `DictRef { name }`, peeling `App` chains for parameterized impls
    /// (e.g. `__dict_Show_List __dict_Show_String`). Look up the impl's
    /// declared effects in `impl_effects_by_dict`. The lookup is uniform
    /// across all methods of the impl since impl-level `needs` applies to
    /// every method body.
    ///
    /// Where-bounded dispatch (dict from a function parameter) ends in a
    /// `Var` rather than `DictRef` and is classified as `RowForwarded`
    /// with no static ops — the actual handler closures live in the dict
    /// tuple's slots and are invoked through the caller's ambient evidence.
    fn classify_dict_method_call(&self, dict: &Expr, supplied: usize) -> CallEffectInfo {
        if supplied == 0 {
            return CallEffectInfo::pure();
        }
        // Peel `App` chain inside the dict expression.
        let mut current = dict;
        while let ExprKind::App { func, .. } = &current.kind {
            current = func;
        }
        match &current.kind {
            ExprKind::DictRef { name, .. } => {
                let Some(effects) = self.inputs.impl_effects_by_dict.get(name) else {
                    return CallEffectInfo::pure();
                };
                if effects.is_empty() {
                    return CallEffectInfo::pure();
                }
                let ops = self.collect_op_keys(effects);
                if ops.is_empty() {
                    return CallEffectInfo::pure();
                }
                CallEffectInfo {
                    kind: CallEffectKind::StaticOps { ops },
                    user_arity: supplied,
                    needs_return_k: true,
                }
            }
            ExprKind::Var { .. } => {
                // Where-bounded dispatch (dict from a function parameter):
                // the impl is unknown at this site, so we cannot tell whether
                // it adds effects. Conservatively classify as pure — matches
                // the trait method's declared signature, which is what the
                // typechecker uses at the call site too. This means
                // where-bounded effectful trait methods are not yet
                // supported; landing them needs a separate channel that
                // tracks the caller's view of the dict-param's impl effects.
                CallEffectInfo::pure()
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
        let canonical_name = resolved.map(|resolved| resolved.canonical_name.clone());
        let effects: Vec<String> = match resolved {
            Some(resolved) if !resolved.effects().is_empty() => resolved.effects().to_vec(),
            Some(_) => self
                .lookup_fun_sig(name, canonical_name.as_deref())
                .map(|s| s.effects.clone())
                .unwrap_or_default(),
            None => {
                // Not a resolved fun. Treat as effectful if it's an in-scope
                // effectful var (mirrors `current_effectful_vars` fallback).
                if let Some(effs) = self.lookup_effectful_var(name) {
                    let ops = self.collect_op_keys(&effs);
                    if ops.is_empty() {
                        // Either the var carried no effects, or the effects
                        // didn't canonicalize against `effect_ops`. Either
                        // way the call is Pure — and Pure must have
                        // needs_return_k == false (see CallEffectInfo doc).
                        return pure();
                    }
                    return CallEffectInfo {
                        kind: CallEffectKind::StaticOps { ops },
                        // Effectful-var calls don't carry a precise user_arity;
                        // supplied > 0 is the gate (already checked above).
                        user_arity: supplied,
                        needs_return_k: true,
                    };
                }
                return pure();
            }
        };

        if effects.is_empty() {
            return pure();
        }

        // Need expanded arity from fun_sigs to compute user_arity.
        let Some(sig) = self.lookup_fun_sig(name, canonical_name.as_deref()) else {
            let ops = self.collect_op_keys(&effects);
            // No FunSig snapshot. Effectful only if the effects canonicalized
            // to known ops; supplied is the best-effort user-arity. Pure must
            // not carry needs_return_k.
            if ops.is_empty() {
                return pure();
            }
            let kind = if self.head_open_row.get(&head_id).copied().unwrap_or(false) {
                CallEffectKind::RowForwarded { static_ops: ops }
            } else {
                CallEffectKind::StaticOps { ops }
            };
            return CallEffectInfo {
                kind,
                user_arity: supplied,
                needs_return_k: true,
            };
        };

        let ops = self.collect_op_keys(&effects);
        let has_ops = !ops.is_empty();
        // Effectful arity = user + Evidence + ReturnK.
        let extras = if has_ops { 2 } else { 0 };
        let user_arity = sig.arity.saturating_sub(extras);

        // Saturation gate from `call_performs_effect`.
        if user_arity == 0 || supplied < user_arity {
            return pure();
        }

        // Prefer the per-call open-row signal (looked up by head NodeId) over
        // the FunSig-level flag, since FunSig keys may not capture every alias
        // for an imported function. The two should agree when both are set.
        let is_open_row = self
            .head_open_row
            .get(&head_id)
            .copied()
            .unwrap_or(sig.is_open_row);
        let kind = if !has_ops {
            CallEffectKind::Pure
        } else if is_open_row {
            CallEffectKind::RowForwarded { static_ops: ops }
        } else {
            CallEffectKind::StaticOps { ops }
        };

        CallEffectInfo {
            kind,
            user_arity: if has_ops { user_arity } else { 0 },
            needs_return_k: has_ops,
        }
    }

    fn lookup_fun_sig(&self, name: &str, canonical_name: Option<&str>) -> Option<&FunSig> {
        // Lookup order mirrors the lowerer: local LetFun frames (innermost
        // first), then the module-level fun_info table by bare name and then
        // by canonical name.
        for frame in self.local_fun_sigs.iter().rev() {
            if let Some(s) = frame.get(name) {
                return Some(s);
            }
        }
        if let Some(s) = self.inputs.fun_sigs.get(name) {
            return Some(s);
        }
        if let Some(c) = canonical_name {
            return self.inputs.fun_sigs.get(c);
        }
        None
    }

    fn lambda_head_effects(&self, lambda_id: NodeId) -> Option<(Vec<String>, bool)> {
        let ty = self.inputs.check_result.resolved_type_for_node(lambda_id)?;
        let (_, effects) = util::arity_and_effects_from_type(&ty);
        let is_open_row = util::has_open_effect_row(&ty);
        let canonical = self.canonicalize_effects(effects);
        if canonical.is_empty() {
            None
        } else {
            Some((canonical, is_open_row))
        }
    }

    fn let_fun_sig(&self, id: NodeId, name: &str) -> Option<FunSig> {
        if let Some(ty) = self.inputs.check_result.resolved_type_for_node(id) {
            let (base_arity, effects) = util::arity_and_effects_from_type(&ty);
            let effects = self.canonicalize_effects(effects);
            let handler_count = self.collect_op_keys(&effects).len();
            let expanded_arity = base_arity + if handler_count > 0 { 2 } else { 0 };
            let param_absorbed_effects = util::param_absorbed_effects_from_type(&ty)
                .into_iter()
                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                .collect();
            return Some(FunSig {
                arity: expanded_arity,
                effects,
                param_absorbed_effects,
                is_open_row: util::has_open_effect_row(&ty),
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
