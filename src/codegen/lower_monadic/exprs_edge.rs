//! Sub-step 7g — remaining `MExpr` variants.
//!
//! Split out of `exprs.rs` to keep the per-file size discipline (≤800 LOC).
//! Each method here is dispatched from `exprs.rs::lower_expr`; the
//! K-threading conventions follow the rules established for the other
//! variants (every non-`Bind`/`Let` final value flows through
//! `apply <ctx.return_k>(...)`).
//!
//! Covers: `FieldAccess`, `RecordUpdate`, `DictMethodAccess`, `ForeignCall`,
//! `BinOp`, `UnaryMinus`, `BitString`, `Receive`. Also hosts the
//! `binop_atoms` operator-dispatch helper.

use crate::ast::BinOp as AstBinOp;
use crate::codegen::cerl::{CArm, CBinSeg, CExpr, CLit};
use crate::codegen::monadic::ir::{Atom, MArm, MBitSegment, MExpr};

use super::{LowerCtx, Lowerer};
use super::util::{resolve_bit_segment_flags, resolve_bit_segment_meta, resolve_bit_segment_size};

impl<'ctx> Lowerer<'ctx> {
    /// Lower `FieldAccess { record, field, record_name, .. }`.
    ///
    /// Records are runtime-represented as `{tag, f0, f1, ...}`. A field at
    /// declared position `i` lives at Erlang tuple index `i + 2` (1-based
    /// indexing, +1 for the leading tag). The declared field order comes
    /// from the per-module `ModuleCodegenInfo::record_fields` cache built
    /// at lowerer construction.
    ///
    /// **Open question, flagged.** When `record_name` is `None` (the
    /// translator couldn't resolve which record type this access belongs
    /// to), we cannot recover field order. The old lowerer has a richer
    /// `current_record_type_name` fallback via `front_resolution` per
    /// NodeId — the new path doesn't thread that yet. Panicking here
    /// surfaces the gap precisely; tighten when 7g part B / step 8 has a
    /// real test that hits it.
    pub(super) fn lower_field_access(
        &mut self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        ctx: &LowerCtx,
    ) -> CExpr {
        // Anonymous records (`{ a: …, b: … }`) use a synthetic tag of the
        // form `__anon_<sorted_field_names_joined_by_underscore>` — the tag
        // itself encodes the field order, sorted alphabetically (see
        // `ast::anon_record_tag`). Derive the order from the tag when no
        // explicit `record_fields` entry exists, instead of panicking.
        let anon_order: Option<Vec<String>> = record_name.and_then(|n| {
            n.strip_prefix("__anon_").map(|rest| {
                rest.split('_').map(|s| s.to_string()).collect::<Vec<_>>()
            })
        });
        let order_owned: Option<Vec<String>> = record_name
            .and_then(|n| self.record_fields.get(n).cloned())
            .or(anon_order);
        let order = order_owned.unwrap_or_else(|| {
            panic!(
                "lower_field_access: cannot resolve record field order (record_name={:?}); \
                 RecordInfo threading from CheckResult is the follow-up — see exprs_edge.rs flag",
                record_name
            )
        });
        let idx = order.iter().position(|f| f == field).unwrap_or_else(|| {
            panic!(
                "lower_field_access: field '{}' not in declared order for record {:?} (order={:?})",
                field, record_name, order
            )
        }) as i64
            + 2;
        let rec = self.lower_atom(record);
        let access = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(idx)), rec],
        );
        self.apply_current_k(access, ctx)
    }

    /// Lower `RecordUpdate { record, fields, record_name, .. }`.
    ///
    /// Build a fresh tuple `{tag, f0', f1', ...}` where each `fi'` is the
    /// updated value (if present in `fields`) or `element(i+2, base)` (if
    /// untouched). The tag is preserved via `element(1, base)`. The base
    /// record is bound to a let-var first so we don't re-evaluate it per
    /// untouched-field access — even though it's atomic by ANF, the var is
    /// cheaper than repeating an `Atom::Tuple` materialization.
    pub(super) fn lower_record_update(
        &mut self,
        record: &Atom,
        fields: &[(String, Atom)],
        record_name: Option<&str>,
        ctx: &LowerCtx,
    ) -> CExpr {
        // See `lower_field_access`: anon record tags encode their sorted
        // field order in the tag itself (`__anon_<f0>_<f1>_…`). Use that
        // when no `record_fields` entry exists.
        let anon_order: Option<Vec<String>> = record_name.and_then(|n| {
            n.strip_prefix("__anon_").map(|rest| {
                rest.split('_').map(|s| s.to_string()).collect::<Vec<_>>()
            })
        });
        let order = record_name
            .and_then(|n| self.record_fields.get(n))
            .cloned()
            .or(anon_order)
            .unwrap_or_else(|| {
                panic!(
                    "lower_record_update: cannot resolve record field order (record_name={:?}); \
                     RecordInfo threading from CheckResult is the follow-up — see exprs_edge.rs flag",
                    record_name
                )
            });
        let rec_var = self.fresh_helper_name();
        let rec_ce = self.lower_atom(record);

        let field_map: std::collections::HashMap<&str, &Atom> =
            fields.iter().map(|(n, a)| (n.as_str(), a)).collect();

        let tag_ce = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(rec_var.clone())],
        );

        let mut elems: Vec<CExpr> = Vec::with_capacity(order.len() + 1);
        elems.push(tag_ce);
        for (pos, field_name) in order.iter().enumerate() {
            elems.push(match field_map.get(field_name.as_str()) {
                Some(new_atom) => self.lower_atom(new_atom),
                None => CExpr::Call(
                    "erlang".to_string(),
                    "element".to_string(),
                    vec![
                        CExpr::Lit(CLit::Int((pos + 2) as i64)),
                        CExpr::Var(rec_var.clone()),
                    ],
                ),
            });
        }
        let tuple = CExpr::Tuple(elems);
        let inner = CExpr::Let(rec_var, Box::new(rec_ce), Box::new(tuple));
        self.apply_current_k(inner, ctx)
    }

    /// Lower `DictMethodAccess { dict, method_index, .. }`.
    ///
    /// Dicts are runtime-represented as `{name_tag, m0, m1, ...}`. The
    /// `method_index` carried by the IR is the 0-based slot in the source
    /// `DictMethodAccess` AST node — element index in the tuple is
    /// `method_index + 1` (1-based offset over the leading tag), matching
    /// the old lowerer's `*method_index as i64 + 1` convention.
    ///
    /// Note: the task brief says "Emit `erlang:element(method_index, dict)`",
    /// but the old lowerer uses `method_index + 1`. The IR field is the AST
    /// field passed through verbatim by the translator, so we match the old
    /// behavior to avoid changing dict-call semantics here.
    pub(super) fn lower_dict_method_access(
        &mut self,
        dict: &Atom,
        method_index: usize,
        ctx: &LowerCtx,
    ) -> CExpr {
        let d = self.lower_atom(dict);
        let elem = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(method_index as i64 + 1)), d],
        );
        self.apply_current_k(elem, ctx)
    }

    /// Lower `ForeignCall { module, func, args, .. }`.
    ///
    /// Emits `call '<module>':'<func>'(<args...>)`. There is no `_Evidence`
    /// / `_ReturnK` threading — foreign calls are raw BIFs. The result flows
    /// through the ambient continuation in `ctx.return_k` so the caller's
    /// continuation receives the BIF's return value.
    pub(super) fn lower_foreign_call(
        &mut self,
        module: &str,
        func: &str,
        args: &[Atom],
        ctx: &LowerCtx,
    ) -> CExpr {
        let call_args: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a)).collect();
        let call = CExpr::Call(module.to_string(), func.to_string(), call_args);
        self.apply_current_k(call, ctx)
    }

    /// Lower `BinOp { op, left, right, .. }`.
    ///
    /// Both operands are atoms by ANF, so we lower them inline and emit the
    /// native Core Erlang shape via [`binop_atoms`]. Result flows through
    /// the ambient continuation in `ctx.return_k`.
    ///
    /// `And`/`Or`: ANF guarantees both operands are non-effectful, so eager
    /// evaluation matches Saga's source semantics. We lower these to the
    /// `erlang:'and'`/`erlang:'or'` BIFs rather than short-circuit `case`
    /// rewrites; the old lowerer's short-circuit shape is unnecessary here.
    pub(super) fn lower_binop(
        &mut self,
        op: &AstBinOp,
        left: &Atom,
        right: &Atom,
        ctx: &LowerCtx,
    ) -> CExpr {
        let l = self.lower_atom(left);
        let r = self.lower_atom(right);
        self.apply_current_k(binop_atoms(op, l, r), ctx)
    }

    /// Lower `UnaryMinus { value, .. }` to `0 - value` via the integer
    /// negation BIF. Atomic by ANF.
    pub(super) fn lower_unary_minus(&mut self, value: &Atom, ctx: &LowerCtx) -> CExpr {
        let v = self.lower_atom(value);
        let neg = CExpr::Call(
            "erlang".to_string(),
            "-".to_string(),
            vec![CExpr::Lit(CLit::Int(0)), v],
        );
        self.apply_current_k(neg, ctx)
    }

    /// Lower `BitString { segments, .. }` (construction; pattern lowering
    /// lives in `pats.rs`).
    ///
    /// Each segment's value and optional size are atoms; we lower them
    /// inline and wrap in `CBinSeg::Segment` (or `BinaryAll` for an
    /// unsized binary splice, or `Byte` runs for literal-string sugar).
    /// Spec encoding copied verbatim from `src/codegen/lower/exprs.rs::lower_bitstring_expr`.
    pub(super) fn lower_bitstring(&mut self, segments: &[MBitSegment], ctx: &LowerCtx) -> CExpr {
        let mut segs: Vec<CBinSeg<CExpr>> = Vec::new();
        for seg in segments {
            // String literal sugar — expand to byte segments.
            if let Atom::Lit {
                value: crate::ast::Lit::String(s, kind),
                ..
            } = &seg.value
            {
                let resolved = if kind.is_multiline() {
                    super::util::process_string_escapes(s)
                } else {
                    s.clone()
                };
                for b in resolved.as_bytes() {
                    segs.push(CBinSeg::Byte(*b));
                }
                continue;
            }

            let is_binary = seg.specs.contains(&crate::ast::BitSegSpec::Binary);
            let value = self.lower_atom(&seg.value);

            if is_binary && seg.size.is_none() {
                segs.push(CBinSeg::BinaryAll(value));
                continue;
            }

            let (type_name, default_size, unit) = resolve_bit_segment_meta(&seg.specs);
            let flags = resolve_bit_segment_flags(&seg.specs);
            let size = seg.size.as_ref().map(|s| self.lower_atom(s));
            let size_expr = resolve_bit_segment_size(size, &type_name, default_size);

            segs.push(CBinSeg::Segment {
                value,
                size: size_expr,
                unit,
                type_name,
                flags,
            });
        }
        self.apply_current_k(CExpr::Binary(segs), ctx)
    }

    /// Lower `Receive { arms, after, .. }`.
    ///
    /// Arms share the enclosing continuation (same convention as `Case`
    /// arms). The timeout in `after` is atomic by ANF; the after-body
    /// lowers under the same ambient K as the arms. When there is no
    /// `after`, default to `infinity` / `'true'` — matching the old
    /// lowerer's shape.
    ///
    /// **Deferred (flagged for follow-up):** the old lowerer recognises
    /// `Down`/`Exit` system-message constructor patterns and rewrites them
    /// into raw Erlang `{'DOWN', ...}` / `{'EXIT', ...}` tuple patterns
    /// plus a reason-conversion let-wrap (see
    /// `src/codegen/lower/mod.rs::ExprKind::Receive` arm). That logic
    /// lives in `lower/beam_interop.rs` which is frozen per the agent
    /// guide. Lowering it requires either copying `beam_interop.rs` into
    /// `lower_monadic/` or promoting it to shared infrastructure — out of
    /// scope for 7g part A. Until then, `Down`/`Exit` patterns in receive
    /// arms emit as plain constructor tuples, which will not match real
    /// system messages at runtime.
    pub(super) fn lower_receive(
        &mut self,
        arms: &[MArm],
        after: Option<&(Atom, Box<MExpr>)>,
        ctx: &LowerCtx,
    ) -> CExpr {
        let carms: Vec<CArm> = arms.iter().map(|arm| self.lower_arm(arm, ctx)).collect();
        let (timeout, timeout_body) = match after {
            Some((t, body)) => (self.lower_atom(t), self.lower_expr(body, ctx)),
            None => (
                CExpr::Lit(CLit::Atom("infinity".to_string())),
                CExpr::Lit(CLit::Atom("true".to_string())),
            ),
        };
        CExpr::Receive(carms, Box::new(timeout), Box::new(timeout_body))
    }
}

/// Map a Saga `BinOp` plus two already-lowered atom CExprs into a single
/// Core Erlang CExpr. Mirrors `src/codegen/lower/util.rs::binop_call`'s
/// dispatch, but takes pre-lowered values instead of var names — atoms in
/// ANF go straight to the BIF without needing an intermediate let.
///
/// Saga's source-level short-circuit operators (`And`, `Or`) get the
/// eager `erlang:'and'`/`erlang:'or'` BIFs here. ANF guarantees both
/// operands are non-yielding, so eager evaluation is observably
/// equivalent to the old lowerer's `case`-based short-circuit shape.
pub(super) fn binop_atoms(op: &AstBinOp, l: CExpr, r: CExpr) -> CExpr {
    use AstBinOp::*;
    let call = |name: &str| {
        CExpr::Call(
            "erlang".to_string(),
            name.to_string(),
            vec![l.clone(), r.clone()],
        )
    };
    match op {
        Add => call("+"),
        Sub => call("-"),
        Mul => call("*"),
        FloatDiv => call("/"),
        IntDiv => call("div"),
        Mod => call("rem"),
        FloatMod => CExpr::Call("math".to_string(), "fmod".to_string(), vec![l, r]),
        Eq => call("=:="),
        NotEq => call("=/="),
        Lt => call("<"),
        Gt => call(">"),
        LtEq => call("=<"),
        GtEq => call(">="),
        Concat => CExpr::Binary(vec![CBinSeg::BinaryAll(l), CBinSeg::BinaryAll(r)]),
        And => call("and"),
        Or => call("or"),
    }
}
