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

use crate::ast::{BinOp as AstBinOp, NodeId, Pat};
use crate::codegen::cerl::{CArm, CBinSeg, CExpr, CLit, CPat};
use crate::codegen::monadic::ir::{Atom, MArm, MBitSegment, MExpr};

use super::util::{
    core_var, lower_string_to_binary, mangle_ctor_atom, resolve_bit_segment_flags,
    resolve_bit_segment_meta, resolve_bit_segment_size,
};
use super::{LowerCtx, Lowerer};

impl<'ctx> Lowerer<'ctx> {
    /// Resolve a record's field order from structural metadata. Anonymous
    /// records carry their canonical sorted order in `anon_fields`; named
    /// records are looked up in the `record_fields` cache by `record_name`.
    /// Never decodes the runtime tag string.
    fn record_field_order(
        &self,
        record_name: Option<&str>,
        anon_fields: Option<&[String]>,
    ) -> Vec<String> {
        if let Some(order) = anon_fields {
            return order.to_vec();
        }
        record_name
            .and_then(|n| self.record_fields.get(n).cloned())
            .unwrap_or_else(|| {
                panic!(
                    "record_field_order: cannot resolve field order (record_name={:?}); \
                     named records must appear in record_fields and anonymous records \
                     must carry anon_fields from elaboration",
                    record_name
                )
            })
    }

    /// Lower `FieldAccess { record, field, record_name, anon_fields, .. }`.
    ///
    /// Records are runtime-represented as `{tag, f0, f1, ...}`. A field at
    /// declared position `i` lives at Erlang tuple index `i + 2` (1-based
    /// indexing, +1 for the leading tag).
    ///
    /// Field order comes from structural metadata, never by decoding the
    /// runtime tag: for anonymous records the translator carries the canonical
    /// sorted order in `anon_fields`; for named records we look it up in the
    /// per-module `ModuleCodegenInfo::record_fields` cache keyed by
    /// `record_name`.
    pub(super) fn lower_field_access(
        &mut self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        anon_fields: Option<&[String]>,
        ctx: &LowerCtx,
    ) -> CExpr {
        let order = self.record_field_order(record_name, anon_fields);
        let idx = order.iter().position(|f| f == field).unwrap_or_else(|| {
            panic!(
                "lower_field_access: field '{}' not in declared order for record {:?} (order={:?})",
                field, record_name, order
            )
        }) as i64
            + 2;
        let rec = self.lower_atom(record, ctx);
        let access = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(idx)), rec],
        );
        self.apply_current_k(access, ctx)
    }

    /// Lower `RecordUpdate { record, fields, record_name, anon_fields, .. }`.
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
        anon_fields: Option<&[String]>,
        ctx: &LowerCtx,
    ) -> CExpr {
        let order = self.record_field_order(record_name, anon_fields);
        let rec_var = self.fresh_helper_name();
        let rec_ce = self.lower_atom(record, ctx);

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
                Some(new_atom) => self.lower_atom(new_atom, ctx),
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
        let d = self.lower_atom(dict, ctx);
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
        let call_args: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a, ctx)).collect();
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
        source: NodeId,
        ctx: &LowerCtx,
    ) -> CExpr {
        let l = self.lower_atom(left, ctx);
        let r = self.lower_atom(right, ctx);
        let call = self.annotate_node(binop_atoms(op, l, r), source);
        self.apply_current_k(call, ctx)
    }

    /// Lower `UnaryMinus { value, .. }` to `0 - value` via the integer
    /// negation BIF. Atomic by ANF.
    pub(super) fn lower_unary_minus(&mut self, value: &Atom, ctx: &LowerCtx) -> CExpr {
        let v = self.lower_atom(value, ctx);
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
            let value = self.lower_atom(&seg.value, ctx);

            if is_binary && seg.size.is_none() {
                segs.push(CBinSeg::BinaryAll(value));
                continue;
            }

            let (type_name, default_size, unit) = resolve_bit_segment_meta(&seg.specs);
            let flags = resolve_bit_segment_flags(&seg.specs);
            let size = seg.size.as_ref().map(|s| self.lower_atom(s, ctx));
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
    /// BEAM system-message constructors are represented differently in
    /// mailboxes than ordinary Saga ADTs. `Down(pid, reason)` matches
    /// `{'DOWN', _Ref, 'process', Pid, RawReason}` and `Exit(pid, reason)`
    /// matches `{'EXIT', Pid, RawReason}`. When the reason pattern is a
    /// variable, the raw Erlang reason is converted back to Saga
    /// `ExitReason` before the arm body runs.
    pub(super) fn lower_receive(
        &mut self,
        arms: &[MArm],
        after: Option<&(Atom, Box<MExpr>)>,
        ctx: &LowerCtx,
    ) -> CExpr {
        let carms: Vec<CArm> = arms
            .iter()
            .map(|arm| self.lower_receive_arm(arm, ctx))
            .collect();
        let (timeout, timeout_body) = match after {
            Some((t, body)) => (self.lower_atom(t, ctx), self.lower_expr(body, ctx)),
            None => (
                CExpr::Lit(CLit::Atom("infinity".to_string())),
                CExpr::Lit(CLit::Atom("true".to_string())),
            ),
        };
        CExpr::Receive(carms, Box::new(timeout), Box::new(timeout_body))
    }

    fn lower_receive_arm(&mut self, arm: &MArm, ctx: &LowerCtx) -> CArm {
        let arm_ctx = ctx.with_pat_locals(&arm.pattern);
        let (pat, reason_wrapper) = self.lower_receive_pat(&arm.pattern);
        let guard = arm.guard.as_ref().map(|g| self.lower_guard(g, &arm_ctx));
        let raw_body = self.lower_expr(&arm.body, &arm_ctx);
        let body = match reason_wrapper {
            Some((user_var, raw_var)) => {
                let conversion = self.exit_reason_from_erlang(&raw_var);
                CExpr::Let(user_var, Box::new(conversion), Box::new(raw_body))
            }
            None => raw_body,
        };
        CArm { pat, guard, body }
    }

    fn lower_receive_pat(&mut self, pat: &Pat) -> (CPat, Option<(String, String)>) {
        match pat {
            Pat::Constructor { name, args, .. } if is_system_msg(name) && args.len() == 2 => {
                let pid_pat = self.lower_pat(&args[0]);
                let (reason_pat, wrapper) = match &args[1] {
                    Pat::Var { name, .. } => {
                        let raw = self.fresh_helper_name();
                        (CPat::Var(raw.clone()), Some((core_var(name), raw)))
                    }
                    other => (self.lower_pat(other), None),
                };
                (system_msg_pattern(name, pid_pat, reason_pat), wrapper)
            }
            _ => (self.lower_pat(pat), None),
        }
    }

    fn exit_reason_from_erlang(&mut self, raw_var: &str) -> CExpr {
        let normal = mangle_ctor_atom("Normal", self.ctors);
        let shutdown = mangle_ctor_atom("Shutdown", self.ctors);
        let killed = mangle_ctor_atom("Killed", self.ctors);
        let noproc = mangle_ctor_atom("Noproc", self.ctors);
        let error = mangle_ctor_atom("Error", self.ctors);
        let other = mangle_ctor_atom("Other", self.ctors);

        let error_msg_var = self.fresh_helper_name();
        let error_msg_var2 = self.fresh_helper_name();
        let other_var = self.fresh_helper_name();
        let fmt_var = self.fresh_helper_name();
        let stringify = CExpr::Call(
            "unicode".to_string(),
            "characters_to_binary".to_string(),
            vec![CExpr::Call(
                "io_lib".to_string(),
                "format".to_string(),
                vec![
                    lower_string_to_binary("~p"),
                    CExpr::Cons(
                        Box::new(CExpr::Var(other_var.clone())),
                        Box::new(CExpr::Nil),
                    ),
                ],
            )],
        );

        CExpr::Case(
            Box::new(CExpr::Var(raw_var.to_string())),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("normal".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(normal)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("shutdown".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(shutdown)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("killed".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(killed)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("noproc".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(noproc)),
                },
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Tuple(vec![
                            CPat::Lit(CLit::Atom("saga_error".to_string())),
                            CPat::Wildcard,
                            CPat::Var(error_msg_var.clone()),
                            CPat::Wildcard,
                            CPat::Wildcard,
                            CPat::Wildcard,
                            CPat::Wildcard,
                        ]),
                        CPat::Wildcard,
                    ]),
                    guard: None,
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom(error.clone())),
                        CExpr::Var(error_msg_var),
                    ]),
                },
                CArm {
                    pat: CPat::Tuple(vec![CPat::Var(error_msg_var2.clone()), CPat::Wildcard]),
                    guard: Some(CExpr::Call(
                        "erlang".to_string(),
                        "is_binary".to_string(),
                        vec![CExpr::Var(error_msg_var2.clone())],
                    )),
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom(error)),
                        CExpr::Var(error_msg_var2),
                    ]),
                },
                CArm {
                    pat: CPat::Var(other_var.clone()),
                    guard: None,
                    body: CExpr::Let(
                        fmt_var.clone(),
                        Box::new(stringify),
                        Box::new(CExpr::Tuple(vec![
                            CExpr::Lit(CLit::Atom(other)),
                            CExpr::Var(fmt_var),
                        ])),
                    ),
                },
            ],
        )
    }
}

fn is_system_msg(ctor_name: &str) -> bool {
    let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
    matches!(bare, "Down" | "Exit")
}

fn system_msg_pattern(ctor_name: &str, pid_pat: CPat, reason_pat: CPat) -> CPat {
    let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
    match bare {
        "Down" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("DOWN".to_string())),
            CPat::Wildcard,
            CPat::Lit(CLit::Atom("process".to_string())),
            pid_pat,
            reason_pat,
        ]),
        "Exit" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("EXIT".to_string())),
            pid_pat,
            reason_pat,
        ]),
        _ => unreachable!("not a system message: {}", ctor_name),
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
