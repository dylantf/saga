//! Exhaustiveness and redundancy checking using Maranget's usefulness algorithm.
//!
//! Reference: Luc Maranget, "Warnings for pattern matching" (2007).
//!
//! The core idea: a pattern vector `q` is *useful* with respect to a pattern
//! matrix `P` iff there exists a value matched by `q` that is not matched by
//! any row of `P`.
//!
//! - Exhaustiveness: `useful(all_arms, [_, _, ...])` should be false.
//! - Redundancy: for arm i, `useful(arms[0..i], arm_i)` should be true.

use std::collections::HashMap;

use crate::ast::{Lit, Pat};

use super::{RecordInfo, Substitution, Type};

/// A simplified pattern for the matrix algorithm.
/// We strip spans and normalize booleans to constructors.
#[derive(Debug, Clone)]
pub(crate) enum SPat {
    /// Matches anything
    Wildcard,
    /// Constructor with name, arity, and sub-patterns
    Constructor(String, Vec<SPat>),
    /// Literal (Int, Float, String) -- treated as infinite domain
    Literal(Lit),
    /// Tuple with sub-patterns (single anonymous constructor)
    Tuple(Vec<SPat>),
}

/// Context passed to the usefulness algorithm: how to look up constructors for a type.
pub(crate) struct ExhaustivenessCtx<'a> {
    /// type_name -> vec of (ctor_name, arity)
    pub adt_variants: &'a HashMap<String, Vec<(String, usize)>>,
}

/// Context for simplifying patterns -- provides record type info so that
/// named and anonymous record patterns can be converted into positional
/// constructors with correct arity and sub-pattern types.
pub(crate) struct SimplifyCtx<'a> {
    pub records: &'a HashMap<String, RecordInfo>,
    pub sub: &'a Substitution,
}

/// A row in the pattern matrix (one case arm's worth of patterns).
type PatRow = Vec<SPat>;
/// The pattern matrix: rows of pattern vectors.
type PatMatrix = Vec<PatRow>;

/// Convert an AST pattern to a simplified pattern.
///
/// `ty` is the (optional) resolved type of the value being matched. It is used
/// to determine the full field set for anonymous record patterns.
pub(crate) fn simplify_pat(pat: &Pat, ty: Option<&Type>, ctx: &SimplifyCtx) -> SPat {
    match pat {
        Pat::Wildcard { .. } | Pat::Var { .. } => SPat::Wildcard,
        Pat::Lit {
            value: Lit::Bool(b),
            ..
        } => {
            let name = if *b { "True" } else { "False" };
            SPat::Constructor(name.into(), vec![])
        }
        Pat::Lit {
            value: Lit::Unit, ..
        } => SPat::Wildcard,
        Pat::Lit { value, .. } => SPat::Literal(value.clone()),
        Pat::Constructor { name, args, .. } => {
            // Use bare constructor name (last segment) so qualified patterns
            // like `Std.File.FileError` match adt_variants which use bare names.
            let bare = name.rsplit('.').next().unwrap_or(name);
            SPat::Constructor(
                bare.to_string(),
                args.iter().map(|p| simplify_pat(p, None, ctx)).collect(),
            )
        }
        Pat::Tuple { elements, .. } => {
            // Extract element types from Tuple type if available
            let elem_types: Option<Vec<Type>> = ty.and_then(|t| match t {
                Type::Con(name, args) if name == super::canonicalize_type_name("Tuple") => Some(args.clone()),
                _ => None,
            });
            SPat::Tuple(
                elements
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        let elem_ty = elem_types.as_ref().and_then(|ts| ts.get(i));
                        simplify_pat(p, elem_ty, ctx)
                    })
                    .collect(),
            )
        }
        Pat::Record { name, fields, .. } => simplify_record_pat(name, fields, ctx),
        Pat::AnonRecord { fields, .. } => simplify_anon_record_pat(fields, ty, ctx),
        Pat::StringPrefix { .. } | Pat::BitStringPat { .. } => {
            // String prefix and bitstring patterns are non-covering (infinite domain)
            // Treat as wildcard so exhaustiveness requires a catch-all arm
            SPat::Wildcard
        }
        Pat::ListPat { .. } | Pat::ConsPat { .. } | Pat::Or { .. } => {
            unreachable!("surface syntax should be desugared before exhaustiveness checking")
        }
    }
}

/// Simplify a named record pattern into a positional constructor.
/// Looks up the record definition to get the canonical field order and types.
fn simplify_record_pat(name: &str, fields: &[(String, Option<Pat>)], ctx: &SimplifyCtx) -> SPat {
    let Some(info) = ctx.records.get(name) else {
        return SPat::Wildcard;
    };
    let field_map: HashMap<&str, Option<&Pat>> = fields
        .iter()
        .map(|(fname, opt_pat)| (fname.as_str(), opt_pat.as_ref()))
        .collect();
    let sub_pats: Vec<SPat> = info
        .fields
        .iter()
        .map(|(fname, field_ty)| {
            match field_map.get(fname.as_str()) {
                Some(Some(pat)) => {
                    let resolved = ctx.sub.apply(field_ty);
                    simplify_pat(pat, Some(&resolved), ctx)
                }
                _ => SPat::Wildcard, // unmentioned or bare binding
            }
        })
        .collect();
    SPat::Constructor(name.to_string(), sub_pats)
}

/// Simplify an anonymous record pattern. Requires the type to know the full
/// field set; without it, falls back to Wildcard.
fn simplify_anon_record_pat(
    fields: &[(String, Option<Pat>)],
    ty: Option<&Type>,
    ctx: &SimplifyCtx,
) -> SPat {
    // The type must be Type::Record(all_fields) so we know every field.
    let Some(Type::Record(all_fields)) = ty else {
        return SPat::Wildcard;
    };
    let field_map: HashMap<&str, Option<&Pat>> = fields
        .iter()
        .map(|(fname, opt_pat)| (fname.as_str(), opt_pat.as_ref()))
        .collect();
    // Use a synthetic constructor name for anonymous records.
    // All anonymous record patterns of the same type will share this name
    // because Type::Record fields are sorted.
    let ctor_name = format!(
        "__anon_record_{}",
        all_fields
            .iter()
            .map(|(f, _)| f.as_str())
            .collect::<Vec<_>>()
            .join("_")
    );
    let sub_pats: Vec<SPat> = all_fields
        .iter()
        .map(|(fname, field_ty)| match field_map.get(fname.as_str()) {
            Some(Some(pat)) => {
                let resolved = ctx.sub.apply(field_ty);
                simplify_pat(pat, Some(&resolved), ctx)
            }
            _ => SPat::Wildcard,
        })
        .collect();
    SPat::Constructor(ctor_name, sub_pats)
}

/// Specialize the matrix for a given constructor.
///
/// For each row whose first column is:
/// - `Constructor(c, sub_pats)` where c == ctor_name: replace first column with sub_pats
/// - `Wildcard`: replace first column with `arity` wildcards
/// - anything else: drop the row
fn specialize(matrix: &PatMatrix, ctor_name: &str, arity: usize) -> PatMatrix {
    let mut result = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        match &row[0] {
            SPat::Constructor(name, sub_pats) if name == ctor_name => {
                let mut new_row: Vec<SPat> = sub_pats.clone();
                new_row.extend_from_slice(&row[1..]);
                result.push(new_row);
            }
            SPat::Wildcard => {
                let mut new_row: Vec<SPat> = vec![SPat::Wildcard; arity];
                new_row.extend_from_slice(&row[1..]);
                result.push(new_row);
            }
            SPat::Tuple(sub_pats) => {
                // Tuples in the first column: specialize if we're specializing for tuples
                // This case handles when ctor_name is "__tuple" (our internal sentinel)
                if ctor_name == "__tuple" {
                    let mut new_row: Vec<SPat> = sub_pats.clone();
                    new_row.extend_from_slice(&row[1..]);
                    result.push(new_row);
                }
                // otherwise skip
            }
            _ => {
                // Constructor mismatch or literal -- skip
            }
        }
    }
    result
}

/// Build the default matrix: keep rows whose first column is a wildcard,
/// dropping the first column.
fn default_matrix(matrix: &PatMatrix) -> PatMatrix {
    let mut result = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        if matches!(&row[0], SPat::Wildcard) {
            result.push(row[1..].to_vec());
        }
    }
    result
}

/// Collect the set of constructors that appear in the first column of the matrix.
fn head_constructors(matrix: &PatMatrix) -> Vec<(String, usize)> {
    let mut seen = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        match &row[0] {
            SPat::Constructor(name, args) => {
                if seen_names.insert(name.clone()) {
                    seen.push((name.clone(), args.len()));
                }
            }
            SPat::Tuple(elems) => {
                if seen_names.insert("__tuple".into()) {
                    seen.push(("__tuple".into(), elems.len()));
                }
            }
            _ => {}
        }
    }
    seen
}

/// Determine whether a pattern vector is useful w.r.t. the matrix.
///
/// Returns true if there exists a value matched by `q` but not by any row in `matrix`.
pub(crate) fn useful(ctx: &ExhaustivenessCtx, matrix: &PatMatrix, q: &PatRow) -> bool {
    // Base case: zero columns
    if q.is_empty() {
        // Useful iff no rows in matrix (no prior pattern covers the empty value)
        return matrix.is_empty();
    }

    match &q[0] {
        SPat::Constructor(ctor_name, sub_pats) => {
            let arity = sub_pats.len();
            let spec = specialize(matrix, ctor_name, arity);
            let mut new_q: Vec<SPat> = sub_pats.clone();
            new_q.extend_from_slice(&q[1..]);
            useful(ctx, &spec, &new_q)
        }

        SPat::Tuple(sub_pats) => {
            let arity = sub_pats.len();
            let spec = specialize(matrix, "__tuple", arity);
            let mut new_q: Vec<SPat> = sub_pats.clone();
            new_q.extend_from_slice(&q[1..]);
            useful(ctx, &spec, &new_q)
        }

        SPat::Literal(_) => {
            // Literals belong to an infinite domain (Int, Float, String).
            // A literal pattern is useful if the default matrix doesn't cover everything.
            // We check: is the query (with first col dropped) useful against the default matrix?
            // This is correct because we can always pick a fresh literal not in the matrix.
            let def = default_matrix(matrix);
            let rest = q[1..].to_vec();
            useful(ctx, &def, &rest)
        }

        SPat::Wildcard => {
            // Look at what constructors appear in the first column of the matrix
            let head_ctors = head_constructors(matrix);

            // Determine if the signature is complete (all constructors of the type appear)
            let is_complete = is_complete_signature(ctx, &head_ctors);

            if is_complete {
                // Try specializing for each constructor: q is useful if it's useful
                // for at least one constructor
                for (ctor_name, arity) in &head_ctors {
                    let spec = specialize(matrix, ctor_name, *arity);
                    let mut new_q: Vec<SPat> = vec![SPat::Wildcard; *arity];
                    new_q.extend_from_slice(&q[1..]);
                    if useful(ctx, &spec, &new_q) {
                        return true;
                    }
                }
                false
            } else {
                // Incomplete signature: use default matrix
                let def = default_matrix(matrix);
                let rest = q[1..].to_vec();
                useful(ctx, &def, &rest)
            }
        }
    }
}

/// Check if the constructors appearing in the first column form a complete
/// signature for their type (i.e., all constructors are present).
fn is_complete_signature(ctx: &ExhaustivenessCtx, head_ctors: &[(String, usize)]) -> bool {
    if head_ctors.is_empty() {
        return false;
    }

    // Special case: tuples and anonymous records always form a complete
    // signature (single constructor)
    if head_ctors.len() == 1
        && (head_ctors[0].0 == "__tuple" || head_ctors[0].0.starts_with("__anon_record_"))
    {
        return true;
    }

    // Look up the type by finding which ADT contains the first constructor
    let first_ctor = &head_ctors[0].0;
    for variants in ctx.adt_variants.values() {
        if variants.iter().any(|(name, _)| name == first_ctor) {
            // Found the type -- check if all its constructors appear
            return variants
                .iter()
                .all(|(name, _)| head_ctors.iter().any(|(hc, _)| hc == name));
        }
    }

    // Not a known ADT (could be a literal type) -- incomplete
    false
}

/// Find all uncovered patterns (all witnesses).
/// This tries each missing constructor at the top level to produce a complete list.
pub(crate) fn find_all_witnesses(
    ctx: &ExhaustivenessCtx,
    matrix: &PatMatrix,
    n: usize,
) -> Vec<Vec<SPat>> {
    if n == 0 {
        return if matrix.is_empty() {
            vec![vec![]]
        } else {
            vec![]
        };
    }

    let head_ctors = head_constructors(matrix);
    let is_complete = is_complete_signature(ctx, &head_ctors);

    let mut all_witnesses = Vec::new();

    if is_complete {
        // All constructors present -- recurse into each to find nested gaps
        for (ctor_name, arity) in &head_ctors {
            let spec = specialize(matrix, ctor_name, *arity);
            for witness in find_all_witnesses(ctx, &spec, arity + n - 1) {
                let (sub_pats, rest) = witness.split_at(*arity);
                let mut result = vec![SPat::Constructor(ctor_name.clone(), sub_pats.to_vec())];
                result.extend_from_slice(rest);
                all_witnesses.push(result);
            }
        }
    } else {
        // Find all missing constructors and generate a witness for each
        let type_variants = find_type_variants(ctx, &head_ctors);
        if let Some(variants) = type_variants {
            for (ctor_name, arity) in &variants {
                if head_ctors.iter().any(|(hc, _)| hc == ctor_name) {
                    // This constructor is present -- check for nested gaps
                    let spec = specialize(matrix, ctor_name, *arity);
                    for witness in find_all_witnesses(ctx, &spec, arity + n - 1) {
                        let (sub_pats, rest) = witness.split_at(*arity);
                        let mut result =
                            vec![SPat::Constructor(ctor_name.clone(), sub_pats.to_vec())];
                        result.extend_from_slice(rest);
                        all_witnesses.push(result);
                    }
                } else {
                    // Missing constructor -- produce a witness with wildcards
                    let def = default_matrix(matrix);
                    for witness in find_all_witnesses(ctx, &def, n - 1) {
                        let mut result = vec![SPat::Constructor(
                            ctor_name.clone(),
                            vec![SPat::Wildcard; *arity],
                        )];
                        result.extend_from_slice(&witness);
                        all_witnesses.push(result);
                    }
                }
            }
        } else {
            // No known type -- fall back to wildcard witness
            let def = default_matrix(matrix);
            for witness in find_all_witnesses(ctx, &def, n - 1) {
                let mut result = vec![SPat::Wildcard];
                result.extend_from_slice(&witness);
                all_witnesses.push(result);
            }
        }
    }

    all_witnesses
}

/// Find the full variant list for the type that the head constructors belong to.
fn find_type_variants(
    ctx: &ExhaustivenessCtx,
    head_ctors: &[(String, usize)],
) -> Option<Vec<(String, usize)>> {
    if head_ctors.is_empty() {
        return None;
    }
    let first_ctor = &head_ctors[0].0;
    for variants in ctx.adt_variants.values() {
        if variants.iter().any(|(name, _)| name == first_ctor) {
            return Some(variants.clone());
        }
    }
    None
}

/// Format a witness pattern for error messages.
pub(crate) fn format_witness(witness: &[SPat]) -> String {
    witness
        .iter()
        .map(format_spat)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_spat(pat: &SPat) -> String {
    match pat {
        SPat::Wildcard => "_".into(),
        SPat::Constructor(name, args) if args.is_empty() => name.clone(),
        SPat::Constructor(name, args) => {
            let args_str: Vec<String> = args.iter().map(format_spat).collect();
            format!("{}({})", name, args_str.join(", "))
        }
        SPat::Literal(lit) => match lit {
            Lit::Int(s, _) => s.clone(),
            Lit::Float(s, _) => s.clone(),
            Lit::String(s, _) => format!("\"{}\"", s),
            Lit::Bool(b) => b.to_string(),
            Lit::Unit => "()".into(),
        },
        SPat::Tuple(elems) => {
            let inner: Vec<String> = elems.iter().map(format_spat).collect();
            format!("({})", inner.join(", "))
        }
    }
}
