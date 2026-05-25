//! Pattern lowering for the new lowerer.
//!
//! Sub-step 7g (part B): full `Pat → CPat` coverage. The shape mirrors
//! `src/codegen/lower/pats.rs` — same record/anon-record/string-prefix /
//! bitstring conventions — but copied (not imported) per the agent-guide's
//! "no imports from frozen files" rule.
//!
//! `Pat::Or`, `Pat::ListPat`, `Pat::ConsPat` are desugared upstream
//! (`src/desugar.rs`) and therefore unreachable here. We panic with the
//! same `"surface syntax should be desugared before codegen"` message the
//! old lowerer uses.

use std::collections::HashMap;

use crate::ast::{BitSegment, Expr, ExprKind, Lit, Pat};
use crate::codegen::cerl::{CBinSeg, CExpr, CLit, CPat};

use super::Lowerer;
use super::util::{
    core_var, lower_lit, mangle_ctor_atom, process_string_escapes,
    resolve_bit_segment_flags, resolve_bit_segment_meta, resolve_bit_segment_size,
};

/// Map a function's parameter patterns to Core Erlang variable names.
///
/// `Pat::Var { name }` keeps its name (mangled via `core_var`); every other
/// pattern (including destructuring forms) gets a positional `_Arg{i}`
/// placeholder. Function-entry destructuring is left to a follow-up
/// (matches the old lowerer's behaviour, which also flattens to fresh
/// `_Arg{i}` and relies on the body to bind via case-on-arg if needed).
pub(super) fn lower_param_names(params: &[Pat]) -> Vec<String> {
    params
        .iter()
        .enumerate()
        .map(|(i, pat)| match pat {
            Pat::Var { name, .. } => core_var(name),
            _ => format!("_Arg{}", i),
        })
        .collect()
}

impl<'ctx> Lowerer<'ctx> {
    /// Lower an AST `Pat` to a Core Erlang `CPat`.
    ///
    /// 7g-B covers the full source-syntax range: variables, wildcards,
    /// literals (including string-as-binary), tuples, constructors (with
    /// the same special cases as `lower_ctor_atom`: `Nil`/`True`/`False`,
    /// `Cons`), records (positional from declared field order, alias
    /// pattern when `as_name` is set), anon-records (sorted by field
    /// name), string-prefix sugar (`"abc" <> rest` → binary pattern with
    /// per-byte literal segments + binary-all tail), and bit-string
    /// patterns.
    ///
    /// `Pat::Or`, `Pat::ListPat`, `Pat::ConsPat` are unreachable post-
    /// desugar and panic with a clear message.
    pub(super) fn lower_pat(&self, pat: &Pat) -> CPat {
        match pat {
            Pat::Wildcard { .. } => CPat::Wildcard,
            Pat::Var { name, .. } => CPat::Var(core_var(name)),
            Pat::Lit { value, .. } => match value {
                Lit::String(s, kind) => {
                    let resolved = if kind.is_multiline() {
                        process_string_escapes(s)
                    } else {
                        s.clone()
                    };
                    CPat::Binary(
                        resolved
                            .as_bytes()
                            .iter()
                            .map(|&b| CBinSeg::Byte(b))
                            .collect(),
                    )
                }
                _ => CPat::Lit(lower_lit(value)),
            },
            Pat::Tuple { elements, .. } => {
                CPat::Tuple(elements.iter().map(|p| self.lower_pat(p)).collect())
            }
            Pat::Constructor { name, args, .. } => {
                let bare = name.rsplit('.').next().unwrap_or(name);
                match bare {
                    "Nil" if args.is_empty() => CPat::Nil,
                    "True" if args.is_empty() => CPat::Lit(CLit::Atom("true".to_string())),
                    "False" if args.is_empty() => CPat::Lit(CLit::Atom("false".to_string())),
                    _ => {
                        if name == "Cons" && args.len() == 2 {
                            return CPat::Cons(
                                Box::new(self.lower_pat(&args[0])),
                                Box::new(self.lower_pat(&args[1])),
                            );
                        }
                        let tag = mangle_ctor_atom(name, self.ctors);
                        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
                        elems.extend(args.iter().map(|p| self.lower_pat(p)));
                        CPat::Tuple(elems)
                    }
                }
            }
            Pat::Record {
                name,
                fields,
                as_name,
                ..
            } => {
                // Records are tagged tuples in declared field order. The order
                // comes from the lowerer's `record_fields` cache, populated at
                // construction from each module's `ModuleCodegenInfo`.
                let tag = mangle_ctor_atom(name, self.ctors);
                let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
                if let Some(order) = self.record_fields.get(name.as_str()) {
                    let field_map: HashMap<&str, Option<&Pat>> =
                        fields.iter().map(|(n, p)| (n.as_str(), p.as_ref())).collect();
                    for field_name in order {
                        match field_map.get(field_name.as_str()) {
                            Some(Some(p)) => elems.push(self.lower_pat(p)),
                            // Punning: `{ name }` binds field to var named after the field.
                            Some(None) => elems.push(CPat::Var(core_var(field_name))),
                            None => elems.push(CPat::Wildcard),
                        }
                    }
                } else {
                    // No declared-order entry — fall back to source order.
                    // This matches the old lowerer's permissive fallback.
                    for (field_name, alias) in fields {
                        match alias {
                            Some(p) => elems.push(self.lower_pat(p)),
                            None => elems.push(CPat::Var(core_var(field_name))),
                        }
                    }
                }
                let tuple_pat = CPat::Tuple(elems);
                match as_name {
                    Some(var) => CPat::Alias(core_var(var), Box::new(tuple_pat)),
                    None => tuple_pat,
                }
            }
            Pat::AnonRecord { fields, .. } => {
                // Anonymous records are tagged tuples with a deterministic tag
                // derived from sorted field names; field order in the runtime
                // tuple is the sorted field-name order.
                let field_names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&field_names);
                let mut sorted_names: Vec<&str> = field_names.clone();
                sorted_names.sort();
                let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
                let field_map: HashMap<&str, Option<&Pat>> =
                    fields.iter().map(|(n, p)| (n.as_str(), p.as_ref())).collect();
                for field_name in &sorted_names {
                    match field_map.get(field_name) {
                        Some(Some(p)) => elems.push(self.lower_pat(p)),
                        Some(None) => elems.push(CPat::Var(core_var(field_name))),
                        None => elems.push(CPat::Wildcard),
                    }
                }
                CPat::Tuple(elems)
            }
            Pat::StringPrefix { prefix, rest, .. } => {
                // `"abc" <> rest` → `<<$a, $b, $c, Rest/binary>>`.
                let mut segs: Vec<CBinSeg<CPat>> =
                    prefix.as_bytes().iter().map(|&b| CBinSeg::Byte(b)).collect();
                let tail = self.lower_pat(rest);
                segs.push(CBinSeg::BinaryAll(tail));
                CPat::Binary(segs)
            }
            Pat::BitStringPat { segments, .. } => {
                let mut segs = Vec::with_capacity(segments.len());
                for seg in segments {
                    // String-literal sugar — same flattening as construction.
                    if let Pat::Lit {
                        value: Lit::String(s, kind),
                        ..
                    } = &seg.value
                    {
                        let resolved = if kind.is_multiline() {
                            process_string_escapes(s)
                        } else {
                            s.clone()
                        };
                        for b in resolved.as_bytes() {
                            segs.push(CBinSeg::Byte(*b));
                        }
                        continue;
                    }
                    segs.push(self.lower_bit_segment_pat(seg));
                }
                CPat::Binary(segs)
            }
            Pat::ListPat { .. } | Pat::ConsPat { .. } | Pat::Or { .. } => {
                unreachable!("surface syntax should be desugared before codegen")
            }
        }
    }

    /// Lower a single bit-segment pattern. Shape parallels
    /// `exprs_edge::lower_bitstring`'s expression-side handling, but the
    /// inner value is itself a `CPat`. Size expressions in pattern position
    /// are integer literals or variable references; the helper
    /// `lower_pat_size_expr` enforces that.
    fn lower_bit_segment_pat(&self, seg: &BitSegment<Pat>) -> CBinSeg<CPat> {
        let is_binary = seg.specs.contains(&crate::ast::BitSegSpec::Binary);
        let pat = self.lower_pat(&seg.value);

        if is_binary && seg.size.is_none() {
            return CBinSeg::BinaryAll(pat);
        }

        let (type_name, default_size, unit) = resolve_bit_segment_meta(&seg.specs);
        let flags = resolve_bit_segment_flags(&seg.specs);
        let size = seg.size.as_deref().map(lower_pat_size_expr);
        let size_expr = resolve_bit_segment_size(size, &type_name, default_size);

        CBinSeg::Segment {
            value: pat,
            size: size_expr,
            unit,
            type_name,
            flags,
        }
    }
}

/// Lower a pattern-position bit-segment size expression to a CExpr.
///
/// Pattern sizes are limited to integer literals or in-scope variable
/// references (e.g. `<<len:8, data:len/binary>>`). Anything else is a
/// codegen-stage invariant violation — copied from
/// `src/codegen/lower/mod.rs::lower_size_expr`.
fn lower_pat_size_expr(expr: &Expr) -> CExpr {
    match &expr.kind {
        ExprKind::Lit {
            value: Lit::Int(_, n),
            ..
        } => CExpr::Lit(CLit::Int(*n)),
        ExprKind::Var { name, .. } => CExpr::Var(core_var(name)),
        _ => unreachable!("bitstring segment size must be an integer literal or variable"),
    }
}
