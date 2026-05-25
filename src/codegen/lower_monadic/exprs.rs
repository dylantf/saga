//! Monadic-IR → Core Erlang expression lowering.
//!
//! Sub-step 7b: `Atom → CExpr` lowering for every variant of the `Atom`
//! enum from `monadic-ir-spec.md`. Structural `MExpr` variants are still
//! stubbed; they arrive in sub-step 7c.

use crate::ast::{NodeId, Pat};
use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::monadic::ir::{Atom, MExpr, MVar};
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};

use super::Lowerer;
use super::pats::lower_param_names;
use super::util::{core_var, lower_lit_atom, lower_string_to_binary, mangle_ctor_atom};

// Name of the function-entry return-continuation variable. Every emitted
// CFunDef binds this as its trailing parameter (after `_Evidence`); the body
// applies it to the function's final value. Kept in sync with `decls.rs`.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";
/// Function-entry evidence-vector parameter name. Kept in sync with
/// `decls.rs`'s [`EVIDENCE_VAR`].
pub(super) const EVIDENCE_VAR: &str = "_Evidence";

impl<'ctx> Lowerer<'ctx> {
    /// Lower an MExpr in function-body (tail) position.
    ///
    /// STUB (7a): every body lowers to `apply _ReturnK('unit')`.
    /// Sub-step 7c replaces this with real MExpr lowering.
    pub(super) fn lower_body_stub(&mut self, _body: &MExpr) -> CExpr {
        CExpr::Apply(
            Box::new(CExpr::Var(RETURN_K_VAR.to_string())),
            vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
        )
    }

    /// Lower the body of an `MDecl::Val` in 7a.
    ///
    /// Vals are arity-0 — there is no `_ReturnK` in scope — so the stub
    /// returns the constant value directly. STUB (7a): every val body is
    /// `'unit'`. Sub-step 7c replaces this with real MExpr-to-value
    /// lowering (literal atoms / tuples / etc. emitted in place).
    pub(super) fn lower_val_body_stub(&mut self, _value: &MExpr) -> CExpr {
        CExpr::Lit(CLit::Atom("unit".to_string()))
    }

    // ---------------------------------------------------------------
    // Atom lowering (sub-step 7b)
    // ---------------------------------------------------------------

    /// Lower an `Atom` to its value-producing `CExpr`. By the ANF/monadic
    /// invariants, an `Atom` is non-effectful and produces a value directly —
    /// no continuation involved. Recursive `Atom` positions (constructor
    /// args, tuple elements, record fields) are lowered in place; there is
    /// no "lift to let" path because those positions are themselves atomic.
    pub(super) fn lower_atom(&mut self, atom: &Atom) -> CExpr {
        match atom {
            Atom::Var { name, .. } => self.lower_var_atom(name),
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Ctor { name, args, .. } => self.lower_ctor_atom(name, args),
            Atom::Tuple { elements, .. } => {
                CExpr::Tuple(elements.iter().map(|e| self.lower_atom(e)).collect())
            }
            Atom::AnonRecord { fields, .. } => self.lower_anon_record_atom(fields),
            Atom::Record { name, fields, .. } => self.lower_record_atom(name, fields),
            Atom::Lambda { params, body, .. } => self.lower_lambda_atom(params, body),
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
    /// `MVar.id` is ignored at the reference site: the translator mints a
    /// fresh `id` per `Var` *use*, so it cannot identify a binding scope.
    /// Source-named variables lower to `core_var(name)` — the same shape
    /// 7a's `lower_param_names` produces for function params. Sub-step 7c
    /// is responsible for keeping translator-introduced binders (`Bind` /
    /// `Let`) from colliding with these.
    fn lower_var_atom(&mut self, mvar: &MVar) -> CExpr {
        CExpr::Var(core_var(&mvar.name))
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
    fn lower_ctor_atom(&mut self, name: &str, args: &[Atom]) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            let head = self.lower_atom(&args[0]);
            let tail = self.lower_atom(&args[1]);
            return CExpr::Cons(Box::new(head), Box::new(tail));
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems: Vec<CExpr> = Vec::with_capacity(args.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for arg in args {
            elems.push(self.lower_atom(arg));
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
    fn lower_anon_record_atom(&mut self, fields: &[(String, Atom)]) -> CExpr {
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let mut elems: Vec<CExpr> = Vec::with_capacity(fields.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for (_, value) in sorted {
            elems.push(self.lower_atom(value));
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
    fn lower_record_atom(&mut self, name: &str, fields: &[(String, Atom)]) -> CExpr {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems: Vec<CExpr> = Vec::with_capacity(fields.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for (_, value) in fields {
            elems.push(self.lower_atom(value));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::Lambda` — closure value at construction.
    ///
    /// Uniform calling convention: every lambda receives `_Evidence` and
    /// `_ReturnK` after its user params, regardless of whether the body
    /// performs effects. The body is STUBBED in 7b (delegates to
    /// `lower_body_stub`); sub-step 7c replaces the body with real MExpr
    /// lowering.
    ///
    /// STUB (7b): lambda body lowers via stub from 7a. 7c replaces.
    fn lower_lambda_atom(&mut self, params: &[Pat], body: &MExpr) -> CExpr {
        let mut param_vars = lower_param_names(params);
        param_vars.push(EVIDENCE_VAR.to_string());
        param_vars.push(RETURN_K_VAR.to_string());
        let body_ce = self.lower_body_stub(body);
        CExpr::Fun(param_vars, Box::new(body_ce))
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
    ///   - `Intrinsic` becomes a `FunRef`.
    ///   - BEAM / External functions become `call mod:fun([])` for arity 0
    ///     and `erlang:make_fun/3` for higher arities — matching the old
    ///     lowerer's value-as-funref convention.
    fn lower_resolved_value_ref(&mut self, resolved: ResolvedSymbol) -> CExpr {
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
            ResolvedCodegenKind::Intrinsic { arity, .. } => CExpr::FunRef(resolved.name, arity),
            ResolvedCodegenKind::ExternalFunction {
                erlang_mod,
                name,
                arity,
                ..
            } => fun_value_of(erlang_mod, name, arity),
            ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(erlang_mod),
                name,
                arity,
                ..
            } => fun_value_of(erlang_mod, name, arity),
            ResolvedCodegenKind::BeamFunction { name, arity, .. } => CExpr::FunRef(name, arity),
        }
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
