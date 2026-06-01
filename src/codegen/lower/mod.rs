//! New lowerer (uniform-effect-translation, stage 12).
//!
//! Consumes `MProgram` (post-ANF, monadic-translated, optionally-optimized)
//! and produces a Core Erlang `CModule`. Designed to be invoked alongside the
//! old lowerer via the toggle in `src/codegen/mod.rs`.
//!
//! ## Sub-step 7a scope
//!
//! Function/decl scaffolding only. The MExpr body lowering is **stubbed**
//! (see [`exprs::lower_body_stub`]) — every emitted CFunDef body is
//! `apply _ReturnK('unit')`. Sub-steps 7b–7g fill in the real translation
//! incrementally.
//!
//! ## Calling convention (uniform)
//!
//! Every emitted CFunDef takes `(user_args..., _Evidence, _ReturnK)` —
//! evidence vector and return continuation are appended even when the source
//! function performs no effects. The slow uniform shape is the load-bearing
//! invariant; selective omission belongs to the optimization stage.
//!
//! ## Module layout
//!
//! - `mod.rs`   — `Lowerer` struct + `lower_module` entry + decl dispatch
//! - `decls.rs` — per-`MDecl` CFunDef construction
//! - `exprs.rs` — MExpr → CExpr (STUB in 7a)
//! - `pats.rs`  — pattern lowering (param-only in 7a; full in 7g)
//! - `util.rs`  — local helpers copied from old lowerer (no imports per
//!   agent-guide allowlist)

#![allow(dead_code)] // 7a scaffolding; consumers land in 7b–7g.

mod app;
mod atom;
mod bootstrap;
mod case;
mod ctx;
mod decls;
mod effects;
mod exprs;
mod exprs_edge;
mod pats;
pub(crate) mod util;

pub(super) use ctx::LowerCtx;

/// Snapshot of every fresh-name counter on the lowerer. Returned by
/// [`Lowerer::snapshot_counters`] and consumed by
/// [`Lowerer::restore_counters`] when lowering nested bodies (lambdas,
/// letfuns) that need their own monotonic naming.
pub(super) struct CounterSnapshot {
    k_counter: u32,
    ev_counter: u32,
    arm_k_counter: u32,
    ret_k_counter: u32,
    helper_counter: u32,
}

use std::collections::HashMap;

use crate::ast::NodeId;
use crate::codegen::CodegenContext;
use crate::codegen::cerl::{CExpr, CModule};
use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{Atom, EffectInfo, MDecl, MExpr, MProgram};
use crate::codegen::resolve::{ConstructorAtoms, ResolutionMap};
use crate::token::Span;

use decls::{dict_constructor_arity, fun_binding_arity, val_arity};

/// New-path lowerer.
///
/// Holds read-only borrows of every input the lowering needs: the source-
/// `NodeId`-keyed resolution map, the constructor → atom table, the cross-
/// module codegen context, the handler-arm classification, and the narrowed
/// effect-info view. None of these are mutated; ownership stays with the
/// caller for the duration of `lower_module`.
///
/// **Type note (open):** the planning spec names this field's type
/// `ModuleCodegenContext`. No such type exists in the codebase today; the
/// existing `CodegenContext` (in `src/codegen/mod.rs`) is the only candidate
/// that fits the role. We use that here and flag the divergence — a follow-up
/// rename to `ModuleCodegenContext` is straightforward if the spec is the
/// canonical name.
pub struct Lowerer<'ctx> {
    resolution: &'ctx ResolutionMap,
    ctors: &'ctx ConstructorAtoms,
    module_ctx: &'ctx CodegenContext,
    handler_info: &'ctx HandlerAnalysis,
    effect_info: &'ctx EffectInfo<'ctx>,
    /// Monotonic counter for fresh K names. Reset at each function entry to
    /// keep emitted Core Erlang stable across decls.
    k_counter: u32,
    /// Monotonic counter for fresh evidence-var names. Reset at each function
    /// entry to keep emitted Core Erlang stable across decls.
    ev_counter: u32,
    /// Monotonic counter for fresh handler-arm continuation names (`_K_arm{n}`).
    /// Distinct from `k_counter` so Bind-K names stay stable as tests already
    /// pin them (`_K0`, `_K1`, ...) independently of any handler arms in scope.
    arm_k_counter: u32,
    /// Monotonic counter for fresh return-clause continuation names (`_K_ret{n}`).
    ret_k_counter: u32,
    /// Monotonic counter for fresh helper var names (`_HArg{n}` style is
    /// positional per arm; this counter is used for transient internals like
    /// return-clause param fallbacks).
    helper_counter: u32,
    /// Monotonic counter for abort/delimiter marker atoms. Unlike the other
    /// counters this is NEVER reset (not in `reset_counters` /
    /// `CounterSnapshot`): marker atoms are runtime values that bubble across
    /// function-call boundaries, so they must be unique across every `with`
    /// site in the module — not merely within one function body. Combined with
    /// `current_erlang_module` this yields a program-global unique marker.
    /// (Resetting it per function caused two functions' first handlers to mint
    /// the same atom, so a callee's prompt would catch a caller's abort.)
    marker_counter: u32,
    /// Declared field order for every known record type. Keyed by record name
    /// (both bare `Foo` and fully-qualified `ModuleName.Foo`) so a lookup
    /// using either form succeeds. Populated at construction from each
    /// module's [`ModuleCodegenInfo::record_fields`].
    ///
    /// `FieldAccess` and `RecordUpdate` need this to translate `record.field`
    /// into a positional `element/2` access — there is no field-name
    /// metadata at runtime, only positions in the underlying tuple.
    pub(super) record_fields: HashMap<String, Vec<String>>,
    /// Whether [`lower_module`] should also emit the bootstrap evidence
    /// builder (`__saga_initial_evidence/0`). Off by default — only the
    /// designated entry-point module needs the bootstrap. See
    /// `bootstrap.rs`.
    pub(super) emit_bootstrap: bool,
    /// Erlang-mangled name of the module currently being lowered (e.g.
    /// `std_base`). Set at the top of [`lower_module`]; used to decide
    /// whether a resolved cross-module reference is actually local (so we
    /// can emit a `FunRef` instead of `erlang:make_fun/3`, which requires
    /// the target to be exported).
    pub(super) current_erlang_module: String,
    /// Source-level names of every handler decl known to the program (local
    /// + imported). Used by [`lower_var_atom`] to detect handler-as-value
    ///   references (`let logger = if dev then console_log else silent_log`)
    ///   that wouldn't otherwise resolve, and emit a placeholder rather than
    ///   a bare-Erlang-var that `erlc` would reject. Populated from module
    ///   metadata at the emit boundary; empty by default.
    pub(super) handler_names: std::collections::HashSet<String>,
    /// Pre-translated handler arms for handler-as-value lowering. When a
    /// handler name appears as a runtime value, the lowerer builds the
    /// op-tuple CExpr from these pre-translated MHandlerArms.
    handler_value_map: &'ctx crate::codegen::monadic::ir::HandlerValueMap,
    /// Current-module top-level `val` declarations. Resolution reports both
    /// vals and zero-parameter function bindings as arity 0; this set keeps
    /// their BEAM shapes distinct (`val/0` vs uniform `fun/2`).
    pub(super) top_level_val_names: std::collections::HashSet<String>,
    /// Current-module zero-parameter function bindings. These are uniform
    /// callables at arity 2 even though their source arity is 0.
    pub(super) zero_arg_fun_names: std::collections::HashSet<String>,
    source_info: Option<SourceInfo>,
}

pub struct SourceInfo {
    file: String,
    line_starts: Vec<usize>,
    node_spans: HashMap<NodeId, Span>,
}

impl SourceInfo {
    pub fn new(file: String, source: &str, node_spans: HashMap<NodeId, Span>) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Self {
            file,
            line_starts,
            node_spans,
        }
    }

    fn line_number(&self, offset: usize) -> usize {
        self.line_starts
            .partition_point(|&start| start <= offset)
            .max(1)
    }

    fn line_for_node(&self, node: NodeId) -> Option<usize> {
        let span = self.node_spans.get(&node)?;
        Some(self.line_number(span.start))
    }
}

impl<'ctx> Lowerer<'ctx> {
    pub fn new(
        resolution: &'ctx ResolutionMap,
        ctors: &'ctx ConstructorAtoms,
        module_ctx: &'ctx CodegenContext,
        handler_info: &'ctx HandlerAnalysis,
        effect_info: &'ctx EffectInfo<'ctx>,
        handler_value_map: &'ctx crate::codegen::monadic::ir::HandlerValueMap,
    ) -> Self {
        let mut record_fields: HashMap<String, Vec<String>> = HashMap::new();
        for (mod_name, m) in &module_ctx.modules {
            for (rec_name, fields) in &m.codegen_info.record_fields {
                let qualified = format!("{}.{}", mod_name, rec_name);
                record_fields.insert(qualified, fields.clone());
                record_fields
                    .entry(rec_name.clone())
                    .or_insert_with(|| fields.clone());
            }
        }
        Self {
            resolution,
            ctors,
            module_ctx,
            handler_info,
            effect_info,
            k_counter: 0,
            ev_counter: 0,
            arm_k_counter: 0,
            ret_k_counter: 0,
            helper_counter: 0,
            marker_counter: 0,
            record_fields,
            emit_bootstrap: false,
            current_erlang_module: String::new(),
            handler_names: std::collections::HashSet::new(),
            handler_value_map,
            top_level_val_names: std::collections::HashSet::new(),
            zero_arg_fun_names: std::collections::HashSet::new(),
            source_info: None,
        }
    }

    pub fn with_source_info(mut self, source_info: SourceInfo) -> Self {
        self.source_info = Some(source_info);
        self
    }

    pub(super) fn annotate_node(&self, expr: CExpr, source: NodeId) -> CExpr {
        let Some(source_info) = &self.source_info else {
            return expr;
        };
        let Some(line) = source_info.line_for_node(source) else {
            return expr;
        };
        CExpr::Annotated {
            expr: Box::new(expr),
            line,
            file: source_info.file.clone(),
        }
    }

    /// Scan the program's passthrough decls for `RecordDef` entries and
    /// insert their declared field order into `record_fields` under both
    /// fully-qualified (`Module.Foo`) and bare (`Foo`) keys. Idempotent:
    /// existing entries (from imported modules) are not overwritten.
    ///
    /// The qualified key uses the **source** (canonical, dotted) module name
    /// from the program's `ModuleDecl` — not the Erlang-mangled module name
    /// passed to `lower_module`. The translator stamps record-name strings
    /// (e.g. on `FieldAccess::record_name`) in the canonical form, so that's
    /// what the lookup must match. Falls back to the supplied `module_name`
    /// when no `ModuleDecl` is present (script / test contexts).
    fn absorb_local_record_defs(&mut self, module_name: &str, program: &MProgram) {
        let source_module = program
            .iter()
            .find_map(|d| match d {
                MDecl::Passthrough(crate::ast::Decl::ModuleDecl { path, .. }) => {
                    Some(path.join("."))
                }
                _ => None,
            })
            .unwrap_or_else(|| module_name.to_string());
        for decl in program {
            if let MDecl::Passthrough(crate::ast::Decl::RecordDef { name, fields, .. }) = decl {
                let field_names: Vec<String> = fields.iter().map(|a| a.node.0.clone()).collect();
                let qualified = format!("{}.{}", source_module, name);
                self.record_fields
                    .entry(qualified)
                    .or_insert_with(|| field_names.clone());
                self.record_fields
                    .entry(name.clone())
                    .or_insert(field_names);
            }
        }
    }

    fn absorb_anon_record_atoms_from_program(&mut self, program: &MProgram) {
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => self.absorb_anon_record_atoms_from_expr(&fb.body),
                MDecl::Val(v) => self.absorb_anon_record_atoms_from_expr(&v.value),
                MDecl::DictConstructor(dc) => {
                    for method in &dc.methods {
                        self.absorb_anon_record_atoms_from_expr(method);
                    }
                }
                _ => {}
            }
        }
    }

    fn absorb_anon_record_atoms_from_atom(&mut self, atom: &Atom) {
        match atom {
            Atom::AnonRecord { fields, .. } => {
                let mut names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&names);
                names.sort();
                self.record_fields
                    .entry(tag)
                    .or_insert_with(|| names.into_iter().map(str::to_string).collect());
                for (_, value) in fields {
                    self.absorb_anon_record_atoms_from_atom(value);
                }
            }
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                for arg in args {
                    self.absorb_anon_record_atoms_from_atom(arg);
                }
            }
            Atom::Record { fields, .. } => {
                for (_, value) in fields {
                    self.absorb_anon_record_atoms_from_atom(value);
                }
            }
            Atom::Lambda { body, .. } => self.absorb_anon_record_atoms_from_expr(body),
            Atom::BackendSpawnThunk { callback, .. } => {
                self.absorb_anon_record_atoms_from_atom(callback)
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => {}
        }
    }

    fn absorb_anon_record_atoms_from_expr(&mut self, expr: &MExpr) {
        match expr {
            MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
                self.absorb_anon_record_atoms_from_atom(atom);
            }
            MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
                for arg in args {
                    self.absorb_anon_record_atoms_from_atom(arg);
                }
            }
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.absorb_anon_record_atoms_from_expr(value);
                self.absorb_anon_record_atoms_from_expr(body);
            }
            MExpr::Ensure { body, cleanup } => {
                self.absorb_anon_record_atoms_from_expr(body);
                self.absorb_anon_record_atoms_from_expr(cleanup);
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.absorb_anon_record_atoms_from_atom(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.absorb_anon_record_atoms_from_expr(guard);
                    }
                    self.absorb_anon_record_atoms_from_expr(&arm.body);
                }
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.absorb_anon_record_atoms_from_atom(cond);
                self.absorb_anon_record_atoms_from_expr(then_branch);
                self.absorb_anon_record_atoms_from_expr(else_branch);
            }
            MExpr::App { head, args, .. } => {
                self.absorb_anon_record_atoms_from_atom(head);
                for arg in args {
                    self.absorb_anon_record_atoms_from_atom(arg);
                }
            }
            MExpr::With { body, .. } => self.absorb_anon_record_atoms_from_expr(body),
            MExpr::FieldAccess { record, .. } | MExpr::DictMethodAccess { dict: record, .. } => {
                self.absorb_anon_record_atoms_from_atom(record);
            }
            MExpr::RecordUpdate { record, fields, .. } => {
                self.absorb_anon_record_atoms_from_atom(record);
                for (_, atom) in fields {
                    self.absorb_anon_record_atoms_from_atom(atom);
                }
            }
            MExpr::BinOp { left, right, .. } => {
                self.absorb_anon_record_atoms_from_atom(left);
                self.absorb_anon_record_atoms_from_atom(right);
            }
            MExpr::UnaryMinus { value, .. } => self.absorb_anon_record_atoms_from_atom(value),
            MExpr::BitString { segments, .. } => {
                for segment in segments {
                    self.absorb_anon_record_atoms_from_atom(&segment.value);
                    if let Some(size) = &segment.size {
                        self.absorb_anon_record_atoms_from_atom(size);
                    }
                }
            }
            MExpr::Receive { arms, after, .. } => {
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.absorb_anon_record_atoms_from_expr(guard);
                    }
                    self.absorb_anon_record_atoms_from_expr(&arm.body);
                }
                if let Some((timeout, body)) = after {
                    self.absorb_anon_record_atoms_from_atom(timeout);
                    self.absorb_anon_record_atoms_from_expr(body);
                }
            }
            MExpr::LetFun { body, rest, .. } => {
                self.absorb_anon_record_atoms_from_expr(body);
                self.absorb_anon_record_atoms_from_expr(rest);
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                for arm in arms {
                    self.absorb_anon_record_atoms_from_expr(&arm.body);
                }
                if let Some(arm) = return_clause {
                    self.absorb_anon_record_atoms_from_expr(&arm.body);
                }
            }
        }
    }

    /// Enable emission of the bootstrap evidence builder
    /// (`__saga_initial_evidence/0`) on the next call to [`lower_module`].
    /// Intended for the entry-point module hosting `main`.
    pub fn with_bootstrap_emission(mut self, on: bool) -> Self {
        self.emit_bootstrap = on;
        self
    }

    /// Mint a fresh handler-arm K name (`_K_arm{n}`). Distinct from Bind-K
    /// to keep emitted Core Erlang stable across changes to handler arms.
    pub(super) fn fresh_k_arm_name(&mut self) -> String {
        let n = self.arm_k_counter;
        self.arm_k_counter += 1;
        format!("_K_arm{}", n)
    }

    /// Mint a fresh return-clause K name (`_K_ret{n}`). Bound to the
    /// synthesized return-lambda; the handled body's tail-K is this var,
    /// so values flow `body → return-clause → outer K` automatically.
    pub(super) fn fresh_k_ret_name(&mut self) -> String {
        let n = self.ret_k_counter;
        self.ret_k_counter += 1;
        format!("_K_ret{}", n)
    }

    /// Mint a program-globally-unique abort/delimiter marker atom. The marker
    /// is a runtime value that bubbles across function-call boundaries, so it
    /// must be unique across every `with` site — not just within one function.
    /// Qualifying with `current_erlang_module` (each module is lowered by its
    /// own `Lowerer`) plus a never-reset counter guarantees that.
    ///
    /// Note this is one atom *per lexical `with` site*, not per runtime handler
    /// activation (Koka mints a fresh marker per activation). Static-per-site is
    /// sound here because: performs dispatch to the nearest handler via
    /// evidence, and a terminal (non-resuming) abort bubbles to the *innermost*
    /// matching delimiter — so an abort is always produced and caught by the
    /// same activation even when one site is live twice on the stack
    /// (recursion). Re-raises are performs, not own-marker aborts, so they never
    /// emit a colliding tuple. Revisit (switch to a runtime-fresh marker bound
    /// at install + guard equality in the prompt) only if first-class/named
    /// handlers gain continuations resumed outside their original dynamic
    /// extent, where two activations of one site must be told apart by identity.
    pub(super) fn fresh_abort_marker(&mut self) -> String {
        let n = self.marker_counter;
        self.marker_counter += 1;
        format!("__saga_abort_{}_{}", self.current_erlang_module, n)
    }

    /// Mint a fresh helper name (`_H{n}`). Used for transient internals
    /// (e.g. return-clause param fallbacks).
    pub(super) fn fresh_helper_name(&mut self) -> String {
        let n = self.helper_counter;
        self.helper_counter += 1;
        format!("_H{}", n)
    }

    /// Mint a fresh Core Erlang variable name for a `With`-extended evidence
    /// vector. Form `_Ev{n}` — parallel to `_K{n}` from [`fresh_k_name`].
    pub(super) fn fresh_evidence_name(&mut self) -> String {
        let n = self.ev_counter;
        self.ev_counter += 1;
        format!("_Ev{}", n)
    }

    /// Mint a fresh Core Erlang variable name for a `Bind` continuation.
    /// Form `_K{n}` — starts with `_` so it is a valid Core Erlang var and
    /// is visually distinguishable from source-derived `_X` mangling.
    pub(super) fn fresh_k_name(&mut self) -> String {
        let n = self.k_counter;
        self.k_counter += 1;
        format!("_K{}", n)
    }

    /// Reset every fresh-name counter at the start of a fresh
    /// function/lambda/letfun body. Continuation-flavored state (return-K,
    /// evidence, arm-K) now lives in [`LowerCtx`] and is constructed afresh
    /// at each entry point rather than reset here.
    pub(super) fn reset_counters(&mut self) {
        self.k_counter = 0;
        self.ev_counter = 0;
        self.arm_k_counter = 0;
        self.ret_k_counter = 0;
        self.helper_counter = 0;
    }

    /// Snapshot the fresh-name counters so they can be restored after
    /// lowering a nested function body (lambda / letfun). Mirrors the
    /// behaviour of the prior `mem::replace` clusters: each nested body
    /// emits stable `_K0`, `_K1`, … names independently of the outer body's
    /// counter state.
    pub(super) fn snapshot_counters(&self) -> CounterSnapshot {
        CounterSnapshot {
            k_counter: self.k_counter,
            ev_counter: self.ev_counter,
            arm_k_counter: self.arm_k_counter,
            ret_k_counter: self.ret_k_counter,
            helper_counter: self.helper_counter,
        }
    }

    /// Restore counters from a [`snapshot_counters`](Self::snapshot_counters)
    /// result.
    pub(super) fn restore_counters(&mut self, s: CounterSnapshot) {
        self.k_counter = s.k_counter;
        self.ev_counter = s.ev_counter;
        self.arm_k_counter = s.arm_k_counter;
        self.ret_k_counter = s.ret_k_counter;
        self.helper_counter = s.helper_counter;
    }

    /// Lower an entire `MProgram` to a Core Erlang `CModule`.
    ///
    /// Iterates declarations in source order:
    ///   - `MFunBinding`, `MVal`, `MDictConstructor` → one `CFunDef` each
    ///   - `Passthrough(ast::Decl)` — most decl kinds emit no runtime code
    ///     (type/effect/trait/import/module headers). The few exceptions
    ///     (`@external` wrappers on `FunSignature`, etc.) are handled by a
    ///     later sub-step; in 7a they're silently skipped, which keeps the
    ///     scaffolding honest about what's stubbed.
    ///
    /// Export list:
    ///   - `MVal` carries its own `public` flag → exported when true.
    ///   - `MFunBinding` and `MDictConstructor` don't carry a `public` flag on
    ///     the IR. We resolve visibility from the current module's
    ///     `ModuleCodegenInfo.exports` (built by the typechecker, lists all
    ///     public bindings by name). When that lookup is unavailable
    ///     (e.g. unit-test contexts using `CodegenContext::default()`),
    ///     we fall back to exporting everything — preserves test ergonomics
    ///     and matches the pre-7g-B behaviour of the new path.
    ///
    /// `@external` wrappers: `Passthrough(FunSignature)` decls with an
    /// `@external("runtime", "<erl_module>", "<erl_func>")` annotation get a
    /// synthesized arity-N+2 wrapper that bridges the uniform calling
    /// convention to the raw BIF. See [`lower_external_wrapper`] in
    /// `decls.rs`.
    pub fn lower_module(&mut self, module_name: &str, program: &MProgram) -> CModule {
        // Track the current module's Erlang name so we can collapse
        // same-module references to a local FunRef in `lower_resolved_value_ref`.
        self.current_erlang_module = module_name.to_string();

        self.top_level_val_names.clear();
        self.zero_arg_fun_names.clear();
        for decl in program {
            match decl {
                MDecl::Val(v) => {
                    self.top_level_val_names.insert(v.name.clone());
                }
                MDecl::FunBinding(fb) if fb.params.is_empty() => {
                    self.zero_arg_fun_names.insert(fb.name.clone());
                }
                _ => {}
            }
        }

        // Collect handler names (local + imported) so `lower_var_atom` can
        // recognize a handler-as-value reference. Includes both bare names
        // and module-qualified canonical names for safety. Local handlers
        // come from this program's `Passthrough(HandlerDef)`; imported
        // ones are listed in each compiled module's
        // `codegen_info.handler_defs`.
        self.handler_names.clear();
        for decl in program {
            if let MDecl::Passthrough(crate::ast::Decl::HandlerDef { name, .. }) = decl {
                self.handler_names.insert(name.clone());
            }
        }
        for compiled in self.module_ctx.modules.values() {
            for hname in &compiled.codegen_info.handler_defs {
                let bare = hname.rsplit('.').next().unwrap_or(hname).to_string();
                self.handler_names.insert(bare);
                self.handler_names.insert(hname.clone());
            }
        }

        // Populate `record_fields` from the currently-compiling module's own
        // `RecordDef` decls. The construction-time pass only sees IMPORTED
        // modules via `module_ctx.modules`; the current module isn't stored
        // there yet, so its records would be missing without this scan.
        // Mirrors the old lowerer's behavior in `lower/init.rs`.
        self.absorb_local_record_defs(module_name, program);
        self.absorb_anon_record_atoms_from_program(program);

        let mut exports = Vec::new();
        let mut funs = Vec::new();

        // Public-name set for FunBinding / DictConstructor visibility.
        // When the module isn't registered in `module_ctx` (test contexts),
        // `pub_names` is `None`: callers default to exporting everything.
        let pub_names: Option<std::collections::HashSet<String>> =
            self.module_ctx.modules.get(module_name).map(|m| {
                m.codegen_info
                    .exports
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect()
            });

        let is_public =
            |name: &str| -> bool { pub_names.as_ref().is_none_or(|s| s.contains(name)) };

        // Group adjacent `MDecl::FunBinding` entries with the same name: each
        // run is one Saga function defined by multiple clauses (`fn 0 x = …`
        // / `fn n x = …`). Translation emits one `MFunBinding` per clause; if
        // we lowered each as its own `CFunDef`, the emitted module would have
        // duplicate `'name'/N = …` definitions and `erlc` would crash. Mirrors
        // the old lowerer's `clause_groups` ([lower/mod.rs:1624-1648]).
        let mut i = 0;
        while i < program.len() {
            let decl = &program[i];
            match decl {
                MDecl::FunBinding(fb) => {
                    // Collect any adjacent same-name clauses into one group.
                    let mut group: Vec<&crate::codegen::monadic::ir::MFunBinding> = vec![fb];
                    let mut j = i + 1;
                    while j < program.len() {
                        if let MDecl::FunBinding(next) = &program[j]
                            && next.name == fb.name
                        {
                            group.push(next);
                            j += 1;
                            continue;
                        }
                        break;
                    }
                    if is_public(&fb.name) {
                        exports.push((fb.name.clone(), fun_binding_arity(&fb.params)));
                    }
                    if group.len() == 1 {
                        funs.push(self.lower_fun_binding(fb));
                    } else {
                        funs.push(self.lower_fun_binding_clauses(&group));
                    }
                    i = j;
                    continue;
                }
                MDecl::Val(v) => {
                    if v.public {
                        exports.push((v.name.clone(), val_arity()));
                    }
                    funs.push(self.lower_val(v));
                    i += 1;
                    continue;
                }
                MDecl::DictConstructor(dc) => {
                    if is_public(&dc.name) {
                        exports.push((dc.name.clone(), dict_constructor_arity(dc)));
                    }
                    funs.push(self.lower_dict_constructor(dc));
                    i += 1;
                    continue;
                }
                MDecl::Passthrough(decl) => {
                    if let Some((wrapper, arity, public)) = decls::lower_external_wrapper(decl) {
                        if public {
                            exports.push((wrapper.name.clone(), arity));
                        }
                        funs.push(wrapper);
                    } else if let Some((wrapper, arity, public)) =
                        decls::lower_builtin_wrapper(decl)
                    {
                        if public {
                            exports.push((wrapper.name.clone(), arity));
                        }
                        funs.push(wrapper);
                    }
                    i += 1;
                    continue;
                }
            }
        }

        if self.emit_bootstrap {
            funs.push(bootstrap::build_initial_evidence_fundef());
            // Entry-point wrapper: the BEAM runner (`exec_erl`) invokes
            // `Module:main/1` with the atom `'unit'`, but the new path
            // exports the user's `main` under the uniform calling
            // convention as `main/3` (1 user param + `_Evidence` +
            // `_ReturnK`). Synthesize a `main/1` shim that materialises the
            // initial evidence vector and threads it (plus an identity
            // continuation) into `main/3`.
            funs.push(bootstrap::build_main_entry_wrapper());
            exports.push(("main".to_string(), 1));
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }
}

#[cfg(test)]
mod tests;
