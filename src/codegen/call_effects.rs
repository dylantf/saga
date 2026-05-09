//! Per-call effect metadata tagged ahead of lowering.
//!
//! This is the Phase 2 deliverable from `docs/planning/plans/evidence-passing-plan.md`.
//! A pre-pass walks the elaborated program and produces a `NodeId -> CallEffectInfo`
//! map for every `App` node. Phase 3's evidence-passing cutover will consume this map
//! to drive evidence threading at each call site; this phase is purely additive
//! and parallel-checked against the existing inline computation in the lowerer.
//!
//! The classification mirrors the inline `Lowerer::call_performs_effect` algorithm:
//! - Resolve the head (`Var` / `QualifiedName`) via the `ResolutionMap`.
//! - Look up the callee's expanded arity and effect row.
//! - Saturated effectful call: `StaticOps` (closed row) or `RowForwarded` (open row).
//! - Otherwise: `Pure`.
//!
//! Effectful let-bindings (`let g = factory(); g x`) are tracked via a lexical scope
//! stack mirroring the lowerer's `current_effectful_vars` mutation.
//!
//! Out-of-scope shapes (deferred to Phase 5):
//! - `DictMethodAccess` (effectful trait methods) — known panic.
//! - Lambda heads `(fun x -> ...) y`.
//! - Direct effect-op calls `op!` — those are tagged via `collect_effect_call`,
//!   not via `App`.

use std::collections::HashMap;

use crate::ast::{self, Decl, Expr, ExprKind, NodeId, Pat, Program, Stmt};
use crate::codegen::resolve::{ResolutionMap, ResolvedName};

/// Per-call metadata. Keyed by the `NodeId` of an `App` node.
#[derive(Debug, Clone)]
pub struct CallEffectInfo {
    pub kind: CallEffectKind,
    /// Logical user-argument count (excludes handler params and return_k).
    pub user_arity: usize,
    /// Whether this call accepts a return continuation (i.e. it is effectful).
    pub needs_return_k: bool,
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
}

/// Pre-pass walker. Constructed with the data sources it needs and consumed by
/// `populate(program)`.
pub struct Populator<'a> {
    resolved: &'a ResolutionMap,
    fun_sigs: &'a HashMap<String, FunSig>,
    /// Per-`Stmt::LetFun` signatures keyed by the LetFun's `id`. Pre-computed
    /// from the typechecker's resolved type for the LetFun node, mirroring the
    /// lowerer's dynamic `fun_info` registration in `lower_block`.
    let_fun_sigs: &'a HashMap<NodeId, FunSig>,
    /// Effect canonical name -> sorted op names.
    effect_ops: &'a HashMap<String, Vec<String>>,
    /// Static let-binding effects from CodegenContext.
    let_effect_bindings: &'a HashMap<String, Vec<String>>,
    map: CallEffectMap,
    /// Stack of lexical scopes. Each frame maps a bound name to the absorbed
    /// effects that calls of that name should thread.
    scopes: Vec<HashMap<String, Vec<String>>>,
    /// Stack of local function frames mirroring the lowerer's dynamic
    /// `fun_info` mutations for `Stmt::LetFun`. Maps name -> FunSig.
    local_fun_sigs: Vec<HashMap<String, FunSig>>,
}

impl<'a> Populator<'a> {
    pub fn new(
        resolved: &'a ResolutionMap,
        fun_sigs: &'a HashMap<String, FunSig>,
        let_fun_sigs: &'a HashMap<NodeId, FunSig>,
        effect_ops: &'a HashMap<String, Vec<String>>,
        let_effect_bindings: &'a HashMap<String, Vec<String>>,
    ) -> Self {
        Populator {
            resolved,
            fun_sigs,
            let_fun_sigs,
            effect_ops,
            let_effect_bindings,
            map: HashMap::new(),
            scopes: Vec::new(),
            local_fun_sigs: Vec::new(),
        }
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
                    self.walk_expr(&arm.node.body);
                    if let Some(fb) = &arm.node.finally_block {
                        self.walk_expr(fb);
                    }
                    self.scopes.pop();
                }
                if let Some(rc) = &body.return_clause {
                    self.scopes.push(HashMap::new());
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

    fn fun_param_effectful_vars(
        &self,
        name: &str,
        params: &[Pat],
    ) -> HashMap<String, Vec<String>> {
        let mut out = HashMap::new();
        let Some(info) = self.fun_sigs.get(name) else {
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

    fn walk_expr(&mut self, expr: &Expr) {
        // Tag App nodes (must be done before recursing so head/args don't
        // mutate scope before classification).
        if matches!(expr.kind, ExprKind::App { .. }) {
            let info = self.classify_app(expr);
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
            ExprKind::RecordCreate { fields, .. }
            | ExprKind::AnonRecordCreate { fields } => {
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
                    self.walk_expr(&arm.node.body);
                    if let Some(fb) = &arm.node.finally_block {
                        self.walk_expr(fb);
                    }
                    self.scopes.pop();
                }
                if let Some(rc) = &body.return_clause {
                    self.scopes.push(HashMap::new());
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
                    if let Some(effs) = self.let_effect_bindings.get(name)
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
                id, name, body, guard, ..
            } => {
                // Mirror the lowerer: register the LetFun's signature into the
                // top local fun frame BEFORE walking its body so recursive
                // calls classify correctly.
                if let Some(sig) = self.let_fun_sigs.get(id)
                    && let Some(frame) = self.local_fun_sigs.last_mut()
                {
                    frame.insert(name.clone(), sig.clone());
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
            CallEffectKind::StaticOps { ops } | CallEffectKind::RowForwarded { static_ops: ops } => {
                let mut effects: Vec<String> = ops.into_iter().map(|k| k.effect).collect();
                effects.sort();
                effects.dedup();
                if effects.is_empty() { None } else { Some(effects) }
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
            // Lambda heads, DictMethodAccess, etc. — out of scope for Phase 2.
            // Mirror today's inline behavior (returns false / Pure) so the
            // parallel-check stays clean.
            _ => CallEffectInfo {
                kind: CallEffectKind::Pure,
                user_arity: arg_count,
                needs_return_k: false,
            },
        }
    }

    fn classify_named_call(
        &self,
        head_id: NodeId,
        name: &str,
        supplied: usize,
    ) -> CallEffectInfo {
        let pure = || CallEffectInfo {
            kind: CallEffectKind::Pure,
            user_arity: supplied,
            needs_return_k: false,
        };

        if supplied == 0 {
            return pure();
        }

        // Mirror `resolved_effects`: prefer ResolutionMap.effects, fall back
        // to fun_sigs (which holds CPS-expanded info for local funs).
        let resolved = self.resolved.get(&head_id);
        let canonical_name = match resolved {
            Some(ResolvedName::LocalFun { canonical_name, .. })
            | Some(ResolvedName::ImportedFun { canonical_name, .. }) => Some(canonical_name.clone()),
            None => None,
        };
        let effects: Vec<String> = match resolved {
            Some(ResolvedName::ImportedFun { effects, .. })
            | Some(ResolvedName::LocalFun { effects, .. })
                if !effects.is_empty() =>
            {
                effects.clone()
            }
            Some(_) => self
                .lookup_fun_sig(name, canonical_name.as_deref())
                .map(|s| s.effects.clone())
                .unwrap_or_default(),
            None => {
                // Not a resolved fun. Treat as effectful if it's an in-scope
                // effectful var (mirrors `current_effectful_vars` fallback).
                if let Some(effs) = self.lookup_effectful_var(name) {
                    let ops = self.collect_op_keys(&effs);
                    return CallEffectInfo {
                        kind: if ops.is_empty() {
                            CallEffectKind::Pure
                        } else {
                            CallEffectKind::StaticOps { ops }
                        },
                        // The inline check returns `true` whenever an
                        // effectful-var is called with at least one arg; it
                        // does not enforce a stricter user_arity since the
                        // var's exact shape isn't recorded. Mirror that.
                        user_arity: supplied,
                        needs_return_k: !effs.is_empty(),
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
            // Inline path: returns true when fun_info missing but effects
            // exist. Mirror that for the bool check; user_arity unknown.
            let ops = self.collect_op_keys(&effects);
            return CallEffectInfo {
                kind: if ops.is_empty() {
                    CallEffectKind::Pure
                } else {
                    CallEffectKind::StaticOps { ops }
                },
                user_arity: supplied,
                needs_return_k: true,
            };
        };

        let ops = self.collect_op_keys(&effects);
        let has_ops = !ops.is_empty();
        let return_k_count = if has_ops { 1 } else { 0 };
        let user_arity = sig.arity.saturating_sub(ops.len() + return_k_count);

        // Saturation gate from `call_performs_effect`.
        if user_arity == 0 || supplied < user_arity {
            return pure();
        }

        CallEffectInfo {
            kind: if has_ops {
                CallEffectKind::StaticOps { ops }
            } else {
                CallEffectKind::Pure
            },
            user_arity,
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
        if let Some(s) = self.fun_sigs.get(name) {
            return Some(s);
        }
        if let Some(c) = canonical_name {
            return self.fun_sigs.get(c);
        }
        None
    }

    fn collect_op_keys(&self, effects: &[String]) -> Vec<OpKey> {
        let mut out = Vec::new();
        for eff in effects {
            if let Some(op_names) = self.effect_ops.get(eff) {
                for op in op_names {
                    out.push(OpKey {
                        effect: eff.clone(),
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

// Silence unused-import warnings under feature combinations.
#[allow(dead_code)]
fn _ast_marker(_: &ast::Program) {}
