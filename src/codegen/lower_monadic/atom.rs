//! `Atom → CExpr` lowering for the monadic-IR → Core Erlang pipeline.

use crate::ast::NodeId;
use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::monadic::ir::{Atom, MVar};
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};

use super::Lowerer;
use super::ctx::LowerCtx;
use super::util::{core_var, lower_lit_atom, lower_string_to_binary, mangle_ctor_atom};

impl<'ctx> Lowerer<'ctx> {
    // ---------------------------------------------------------------
    // Atom lowering (sub-step 7b)
    // ---------------------------------------------------------------

    /// Lower an `Atom` to its value-producing `CExpr`. By the ANF/monadic
    /// invariants, an `Atom` is non-effectful and produces a value directly —
    /// no continuation involved. Recursive `Atom` positions (constructor
    /// args, tuple elements, record fields) are lowered in place; there is
    /// no "lift to let" path because those positions are themselves atomic.
    ///
    /// The `ctx` is plumbed through only because `Atom::Lambda` contains an
    /// `MExpr` body whose lowering is continuation-sensitive — in particular,
    /// a `Resume` inside a lambda defined inside a handler arm body must
    /// resolve to the *enclosing arm's* K, not the lambda's own _ReturnK.
    /// All other atom variants ignore the ctx.
    pub(super) fn lower_atom(&mut self, atom: &Atom, ctx: &LowerCtx) -> CExpr {
        match atom {
            Atom::Var { name, source } => self.lower_var_atom(name, *source),
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Ctor { name, args, .. } => self.lower_ctor_atom(name, args, ctx),
            Atom::Tuple { elements, .. } => {
                CExpr::Tuple(elements.iter().map(|e| self.lower_atom(e, ctx)).collect())
            }
            Atom::AnonRecord { fields, .. } => self.lower_anon_record_atom(fields, ctx),
            Atom::Record { name, fields, .. } => self.lower_record_atom(name, fields, ctx),
            Atom::Lambda { params, body, .. } => self.lower_lambda_atom(params, body, ctx),
            Atom::DictRef { name, source } => self.lower_dict_ref_atom(name, *source),
            Atom::QualifiedRef {
                module,
                name,
                source,
            } => self.lower_qualified_ref_atom(module, name, *source),
            Atom::Symbol { symbol, .. } => lower_string_to_binary(symbol),
        }
    }

    /// Lower an `Atom::Var` reference.
    ///
    /// A bare (unqualified) `Var` in the source AST can refer to either:
    ///   1. A local binding (function param, let binding, lambda param,
    ///      case binding, etc.) — lowered to `core_var(name)`.
    ///   2. A top-level function or imported symbol — must be lowered as
    ///      a function value (`FunRef` / `make_fun`), not a bare Erlang
    ///      variable, or `erlc` rejects with "unbound variable".
    ///
    /// The resolution map is authoritative: if `MVar.source` (the original
    /// AST NodeId of the reference) has a `ResolvedSymbol` entry, this is
    /// case 2 — dispatch through [`lower_resolved_value_ref`] exactly like
    /// the old lowerer's `ExprKind::Var` branch ([lower/mod.rs:3334-3351]).
    /// Otherwise fall back to a bare var.
    fn lower_var_atom(&mut self, mvar: &MVar, source: NodeId) -> CExpr {
        if let Some(resolved) = self.resolution.get(&source).cloned() {
            return self.lower_resolved_value_ref(resolved);
        }
        if let Some(fun) = self.unique_imported_fun_value(&mvar.name) {
            return fun;
        }
        // Handler-as-value references (`let logger = if dev then console_log
        // else silent_log`) need a real op-tuple value. The new path doesn't
        // yet synthesize one for arbitrary handler names — emit a placeholder
        // `'unit'` atom so `erlc` accepts the module. Any subsequent `with
        // logger body` site then takes the empty-effects Dynamic branch
        // (warning + body-only), making this a clean runtime failure rather
        // than a compile-time block. TODO: synthesize the proper op-tuple
        // (see `lower_handler_def_to_tuple` in the old lowerer for the
        // shape).
        if self.handler_names.contains(&mvar.name) {
            return CExpr::Lit(CLit::Atom("unit".to_string()));
        }
        CExpr::Var(core_var(&mvar.name))
    }

    fn unique_imported_fun_value(&self, name: &str) -> Option<CExpr> {
        let mut found: Option<CExpr> = None;
        for (module_name, compiled) in &self.module_ctx.modules {
            let erlang_mod = module_name.to_lowercase().replace('.', "_");
            for (export_name, scheme) in &compiled.codegen_info.exports {
                if export_name != name {
                    continue;
                }
                if found.is_some() {
                    return None;
                }
                let (source_arity, mut effects) = arity_and_effects_from_type(&scheme.ty);
                if let Some((_, annotated)) = compiled
                    .codegen_info
                    .fun_effects
                    .iter()
                    .find(|(n, _)| n == name)
                {
                    for effect in annotated {
                        if !effects.contains(effect) {
                            effects.push(effect.clone());
                        }
                    }
                }
                let dict_params = scheme.constraints.len();
                let uniform = if effects.is_empty() {
                    uniform_value_arity(source_arity + dict_params, &effects, name)
                } else {
                    source_arity + dict_params + 2
                };
                found = Some(fun_value_of(erlang_mod.clone(), name.to_string(), uniform));
            }
        }
        found
    }

    /// Lower an `Atom::Ctor` — a recursively-atomic constructor application.
    ///
    /// Saga's runtime encoding:
    ///   - `Nil` → `[]`
    ///   - `Cons(h, t)` → `[h | t]`
    ///   - `True` / `False` → bare `'true'` / `'false'` atoms (Erlang native)
    ///   - other nullary BEAM-interop atoms (exit reasons) → bare atoms
    ///     (skipped here — 7b sticks to the common path; sub-step 7g revisits)
    ///   - everything else → `{tag_atom, arg_0, arg_1, ...}` tagged tuple
    fn lower_ctor_atom(&mut self, name: &str, args: &[Atom], ctx: &LowerCtx) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            "Normal" | "Shutdown" | "Killed" | "Noproc" if args.is_empty() => {
                return CExpr::Lit(CLit::Atom(exit_reason_bare_atom(bare).to_string()));
            }
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            let head = self.lower_atom(&args[0], ctx);
            let tail = self.lower_atom(&args[1], ctx);
            return CExpr::Cons(Box::new(head), Box::new(tail));
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems: Vec<CExpr> = Vec::with_capacity(args.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for arg in args {
            elems.push(self.lower_atom(arg, ctx));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::AnonRecord` — a structural record with no nominal type.
    ///
    /// Encoding (matches the old lowerer):
    ///   `{tag_atom, field_v_0, field_v_1, ...}` where `tag_atom =
    ///   anon_record_tag(field_names)` and fields are ordered by sorted
    ///   name. Sorting yields a stable representation regardless of source
    ///   field order, which is what makes two anon records with the same
    ///   fields structurally equal at the BEAM level.
    fn lower_anon_record_atom(&mut self, fields: &[(String, Atom)], ctx: &LowerCtx) -> CExpr {
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let mut elems: Vec<CExpr> = Vec::with_capacity(fields.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for (_, value) in sorted {
            elems.push(self.lower_atom(value, ctx));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::Record` — a named record value.
    ///
    /// Encoding (matches the old lowerer):
    ///   `{record_tag, field_v_0, field_v_1, ...}` where the tag is the
    ///   mangled constructor atom (same table used for ADT ctors), and the
    ///   fields are ordered by the record's declared field order.
    ///
    /// **7b limitation.** The old lowerer reads declared field order from
    /// `resolved_record_fields(node_id, name)`, which threads the
    /// `ResolutionMap` + `CheckResult.records`. The new path doesn't yet
    /// have a `CheckResult` borrow on the `Lowerer` (the spec narrows to
    /// `EffectInfo` only). For 7b we honor the source-supplied field
    /// order — the translator preserved the source order — which works
    /// when records are constructed with declaration-order fields. A later
    /// sub-step (likely 7d's record-update work) is the right place to
    /// add a declared-order lookup. Flagged in the step report.
    fn lower_record_atom(
        &mut self,
        name: &str,
        fields: &[(String, Atom)],
        ctx: &LowerCtx,
    ) -> CExpr {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems: Vec<CExpr> = Vec::with_capacity(fields.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for (_, value) in fields {
            elems.push(self.lower_atom(value, ctx));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::DictRef` — a reference to a trait dictionary value.
    ///
    /// Tries the `ResolutionMap` first (the resolver tags inter-module dict
    /// references with a `BeamFunction`/`ExternalFunction` codegen kind);
    /// otherwise falls back to a local `CExpr::Var`. The fallback covers
    /// dict-parameter variables passed in as function arguments (e.g. the
    /// `sub_a` parameter on a conditional impl like
    /// `Show for List a where {a: Show}`).
    fn lower_dict_ref_atom(&mut self, name: &str, source: NodeId) -> CExpr {
        if let Some(resolved) = self.resolution.get(&source).cloned() {
            // Dict constructors are uniform-shape callables like everything
            // else; `lower_resolved_value_ref` adds the `+2` for
            // `_Evidence`/`_ReturnK` via `uniform_value_arity`.
            return self.lower_resolved_value_ref(resolved);
        }
        CExpr::Var(core_var(name))
    }

    /// Lower an `Atom::QualifiedRef` — a `Module.name` reference used as a
    /// value (not under a call).
    ///
    /// The resolver tags qualified references with the target Erlang module
    /// / function / arity. We dispatch through `lower_resolved_value_ref`
    /// the same way the dict case does. When the resolution map has no
    /// entry, fall back to a bare `core_var(name)`; this preserves the
    /// behavior of the old lowerer's last-resort branch.
    fn lower_qualified_ref_atom(&mut self, _module: &str, name: &str, source: NodeId) -> CExpr {
        if let Some(resolved) = self.resolution.get(&source).cloned() {
            return self.lower_resolved_value_ref(resolved);
        }
        CExpr::Var(core_var(name))
    }

    /// Translate a `ResolvedSymbol` into its value-position `CExpr`.
    ///
    /// Copied from the old lowerer (`lower/mod.rs::lower_resolved_value_ref`)
    /// and stripped to the value-only path the new lowerer needs:
    ///   - `InlineVal` — old-path-only perf optimization; the new path
    ///     gets equivalent perf from effect-optimization (bind-collapse +
    ///     Bind→Let). Hard panic if encountered (see arm body).
    ///   - `Intrinsic` becomes a `FunRef` at its declared arity. Intrinsics
    ///     are direct BIFs / compiler primitives with no Saga wrapper, so the
    ///     uniform-shape +2 expansion does NOT apply to them.
    ///   - `BeamFunction` / `ExternalFunction` references point at a Saga
    ///     function (or its `@external` wrapper) compiled under the uniform
    ///     calling convention: `(user_args..., _Evidence, _ReturnK)`. The
    ///     resolved `arity` is the **source** arity (user-visible parameter
    ///     count) — we add `+2` for evidence + return-K so callers using the
    ///     resulting fun value invoke it with the right number of arguments.
    ///     Arity-0 entries (vals, niladic constants) stay arity-0: those are
    ///     not wrapped in the uniform shape; calling them just yields the
    ///     constant value.
    pub(super) fn lower_resolved_value_ref(&mut self, resolved: ResolvedSymbol) -> CExpr {
        match resolved.kind {
            ResolvedCodegenKind::InlineVal => {
                panic!(
                    "InlineVal resolution not used in new path — vals are uniformly emitted as \
                     arity-0 constants; this resolution kind should not appear post-translation. \
                     If it does, the translator or backend-resolve is producing stale resolution \
                     info. (canonical_name={})",
                    resolved.canonical_name
                )
            }
            ResolvedCodegenKind::Intrinsic { arity, .. } => {
                // `@builtin` decls are wrapped at their defining module under
                // the uniform calling convention by
                // `lower_builtin_wrapper` (in `decls.rs`). Reference the
                // wrapper at its uniform arity: `make_fun(erlang_mod, name,
                // arity + 2)`. The intrinsic name itself doubles as the
                // wrapper's function name.
                //
                // For intrinsics without a wrapper yet, this still emits a
                // cross-module `make_fun` reference — which will fail at
                // link time. That mirrors the existing behavior (the old
                // `FunRef(name, arity)` failed the same way) and surfaces
                // missing wrappers loudly.
                if let Some(src_mod) = &resolved.source_module {
                    let erlang_mod: String = src_mod.to_lowercase().replace('.', "_");
                    // Intrinsics have no effect annotation; treat them as
                    // pure for the uniform-arity calculation.
                    let uniform = uniform_value_arity(arity, &[], &resolved.name);
                    fun_value_of(erlang_mod, resolved.name, uniform)
                } else {
                    CExpr::FunRef(resolved.name, arity)
                }
            }
            ResolvedCodegenKind::ExternalFunction {
                erlang_mod,
                name,
                arity,
                effects,
                ..
            } => {
                let uniform = uniform_value_arity(arity, &effects, &name);
                // Same-module refs use FunRef — `erlang:make_fun/3` requires
                // the target to be exported, but local @external wrappers
                // for private decls aren't exported. The old lowerer's
                // [`lower_local_fun_ref`] makes the same choice.
                if erlang_mod == self.current_erlang_module {
                    local_value_ref(name, uniform)
                } else {
                    fun_value_of(erlang_mod, name, uniform)
                }
            }
            ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(erlang_mod),
                name,
                arity,
                effects,
                ..
            } => {
                let uniform = uniform_value_arity(arity, &effects, &name);
                if erlang_mod == self.current_erlang_module {
                    local_value_ref(name, uniform)
                } else {
                    fun_value_of(erlang_mod, name, uniform)
                }
            }
            ResolvedCodegenKind::BeamFunction {
                name,
                arity,
                effects,
                ..
            } => {
                let uniform = uniform_value_arity(arity, &effects, &name);
                if let Some(src_mod) = &resolved.source_module {
                    let erlang_mod = src_mod.to_lowercase().replace('.', "_");
                    if erlang_mod != self.current_erlang_module {
                        return fun_value_of(erlang_mod, name.clone(), uniform);
                    }
                }
                local_value_ref(name.clone(), uniform)
            }
        }
    }
}

fn exit_reason_bare_atom(name: &str) -> &'static str {
    match name {
        "Normal" => "normal",
        "Shutdown" => "shutdown",
        "Killed" => "killed",
        "Noproc" => "noproc",
        _ => unreachable!("not a nullary ExitReason constructor: {}", name),
    }
}

/// Map a resolved BEAM/external function reference's arity to the
/// uniform-shape arity at which it is callable.
///
/// The resolver's `arity` field already includes dict-passing params (and,
/// for effectful functions registered by the old-path's
/// `build_imported_fun_scoped`, the `_Evidence` + `_ReturnK` slots — i.e.
/// `+2` is already baked in). For pure functions, the resolver's arity is
/// the source + dict count only; we add `+2` here to reach the uniform
/// shape every Saga-defined callable is emitted under.
///
/// Arity-0 with no effects denotes a top-level val (a constant), which is
/// the only kind of Saga-emitted callable that stays at arity 0. Dict
/// constructors with no where-clause params also resolve with `arity == 0`
/// but emit at arity 2 (uniform `(_Evidence, _ReturnK)`); we detect them
/// by the `__dict_` name prefix used everywhere in elaboration and force
/// the `+2` regardless.
pub(super) fn uniform_value_arity(arity: usize, effects: &[String], name: &str) -> usize {
    let is_dict_ctor = name.starts_with("__dict_");
    if !effects.is_empty() {
        // Old-path resolution already added `+2` for effectful imports.
        arity
    } else if arity == 0 && !is_dict_ctor {
        // Val constant — stays arity-0.
        0
    } else {
        // Pure function — resolution carries source + dict count only;
        // add `+2` for uniform `(_Evidence, _ReturnK)`.
        arity + 2
    }
}

fn arity_and_effects_from_type(ty: &crate::typechecker::Type) -> (usize, Vec<String>) {
    use crate::typechecker::Type;

    let mut arity = 0;
    let mut effects = Vec::new();
    let mut cur = ty;
    while let Type::Fun(_, ret, row) = cur {
        arity += 1;
        for effect in &row.effects {
            if !effects.contains(&effect.name) {
                effects.push(effect.name.clone());
            }
        }
        cur = ret;
    }
    effects.sort();
    (arity, effects)
}

/// Emit a value-position reference to a same-module callable.
///
/// Arity-0 entries are top-level `val` constants — referencing them must
/// invoke the local function to materialize the value, not produce a
/// fun reference (which is a callable, not a tuple/record/etc.).
/// Arity > 0 stays a `FunRef`, the caller `apply`s it when needed.
fn local_value_ref(name: String, uniform: usize) -> CExpr {
    if uniform == 0 {
        CExpr::Apply(Box::new(CExpr::FunRef(name, 0)), vec![])
    } else {
        CExpr::FunRef(name, uniform)
    }
}

/// Emit a function value (as an Erlang term) for a known module/function/arity.
///
/// Arity-0 functions reduce to a direct call returning the value; higher
/// arities become an `erlang:make_fun/3` to construct a fun term. Matches
/// the old lowerer's convention.
fn fun_value_of(erlang_mod: String, name: String, arity: usize) -> CExpr {
    if arity == 0 {
        CExpr::Call(erlang_mod, name, vec![])
    } else {
        CExpr::Call(
            "erlang".to_string(),
            "make_fun".to_string(),
            vec![
                CExpr::Lit(CLit::Atom(erlang_mod)),
                CExpr::Lit(CLit::Atom(name)),
                CExpr::Lit(CLit::Int(arity as i64)),
            ],
        )
    }
}
