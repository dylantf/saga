use std::collections::HashSet;

use crate::ast::{self, Expr, Lit, Pat};
use crate::token::Span;

use super::{Checker, Diagnostic, Scheme, Type};

impl Checker {
    // --- Pattern binding ---

    /// Bind a pattern to a type, adding variables to the environment.
    pub(crate) fn bind_pattern(&mut self, pat: &Pat, ty: &Type) -> Result<(), Diagnostic> {
        match pat {
            Pat::Wildcard { .. } => Ok(()),
            Pat::Var { id, name, span, .. } => {
                self.env.insert_with_def(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: ty.clone(),
                    },
                    *id,
                );
                self.record_type_at_span(*span, ty);
                self.lsp.node_spans.insert(*id, *span);
                self.lsp.definitions.push((*id, name.clone(), *span));
                Ok(())
            }
            Pat::Lit { value, span, .. } => {
                let lit_ty = match value {
                    Lit::Int(_) => Type::int(),
                    Lit::Float(_) => Type::float(),
                    Lit::String(_) => Type::string(),
                    Lit::Bool(_) => Type::bool(),
                    Lit::Unit => Type::unit(),
                };
                self.unify_at(ty, &lit_ty, *span)
            }
            Pat::Constructor {
                id, name, args, span, ..
            } => {
                let ctor_scheme = self.constructors.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(
                        *span,
                        format!("undefined constructor in pattern: {}", name),
                    )
                })?;
                // Record reference to constructor definition for find-references/rename
                if let Some(def_id) = self.lsp.constructor_def_ids.get(name).copied() {
                    self.record_reference(*id, *span, def_id);
                }
                let (ctor_ty, _) = self.instantiate(&ctor_scheme);
                let mut current = ctor_ty;
                for arg_pat in args {
                    match current {
                        Type::Arrow(param_ty, ret_ty) => {
                            self.bind_pattern(arg_pat, &param_ty)?;
                            current = *ret_ty;
                        }
                        _ => {
                            return Err(Diagnostic::error_at(
                                *span,
                                format!("constructor {} applied to too many arguments", name),
                            ));
                        }
                    }
                }
                self.unify_at(ty, &current, *span)
            }
            Pat::Record {
                name,
                fields,
                as_name,
                span,
                ..
            } => {
                let info = self.records.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(
                        *span,
                        format!("undefined record type in pattern: {}", name),
                    )
                })?;
                // Record the type name reference for find-references/rename
                let name_end = span.start + name.len();
                self.lsp.type_references.push((
                    crate::token::Span { start: span.start, end: name_end },
                    name.to_string(),
                ));
                let (inst_fields, result_ty) = self.instantiate_record(name, &info);
                self.unify_at(ty, &result_ty, *span)?;

                for (fname, alias_pat) in fields {
                    let (_, field_ty) =
                        inst_fields
                            .iter()
                            .find(|(n, _)| n == fname)
                            .ok_or_else(|| {
                                Diagnostic::error_at(
                                    *span,
                                    format!("unknown field '{}' on record {}", fname, name),
                                )
                            })?;
                    let resolved_field_ty = self.sub.apply(field_ty);
                    match alias_pat {
                        Some(pat) => self.bind_pattern(pat, &resolved_field_ty)?,
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: resolved_field_ty.clone(),
                                },
                            );
                            self.record_type_at_span(*span, &resolved_field_ty);
                        }
                    }
                }
                if let Some(as_var) = as_name {
                    let resolved = self.sub.apply(&result_ty);
                    self.env.insert(
                        as_var.clone(),
                        Scheme {
                            forall: vec![],
                            constraints: vec![],
                            ty: resolved.clone(),
                        },
                    );
                    self.record_type_at_span(*span, &resolved);
                }
                Ok(())
            }

            Pat::Tuple { elements, span, .. } => {
                let elem_tys: Vec<Type> = elements.iter().map(|_| self.fresh_var()).collect();
                let tuple_ty = Type::Con("Tuple".into(), elem_tys.clone());
                self.unify_at(ty, &tuple_ty, *span)?;
                for (pat, elem_ty) in elements.iter().zip(elem_tys.iter()) {
                    self.bind_pattern(pat, elem_ty)?;
                }
                Ok(())
            }

            Pat::StringPrefix { rest, span, .. } => {
                self.unify_at(ty, &Type::string(), *span)?;
                self.bind_pattern(rest, &Type::string())
            }

            Pat::AnonRecord { fields, span, .. } => {
                let mut field_tys: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(fname, _)| (fname.clone(), self.fresh_var()))
                    .collect();
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
                let record_ty = Type::Record(field_tys.clone());
                self.unify_at(ty, &record_ty, *span)?;

                for (fname, alias_pat) in fields {
                    let (_, field_ty) = field_tys.iter().find(|(n, _)| n == fname).unwrap();
                    let resolved_field_ty = self.sub.apply(field_ty);
                    match alias_pat {
                        Some(pat) => self.bind_pattern(pat, &resolved_field_ty)?,
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: resolved_field_ty.clone(),
                                },
                            );
                            self.record_type_at_span(*span, &resolved_field_ty);
                        }
                    }
                }
                Ok(())
            }
        }
    }

    // --- Exhaustiveness checking ---

    /// Check whether case arms exhaustively cover a type using Maranget's
    /// usefulness algorithm. Also detects unreachable/redundant arms.
    pub(crate) fn check_exhaustiveness(
        &self,
        arms: &[ast::CaseArm],
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), Diagnostic> {
        use super::exhaustiveness::{self as exh, ExhaustivenessCtx, SPat};

        let resolved = self.sub.apply(scrutinee_ty);

        // Skip exhaustiveness for unresolved type variables and arrow types
        match &resolved {
            Type::Con(_, _) => {}
            _ => return Ok(()),
        };

        let type_name = match &resolved {
            Type::Con(name, _) => name.clone(),
            _ => unreachable!(),
        };

        // For primitive types with infinite value sets, keep the simple check:
        // require a wildcard/variable fallback if any literal patterns are used.
        if !self.adt_variants.contains_key(&type_name)
            && matches!(type_name.as_str(), "Int" | "Float" | "String")
        {
            let has_lit = arms
                .iter()
                .any(|arm| matches!(&arm.pattern, Pat::Lit { .. }));
            if has_lit {
                let has_catchall = arms.iter().any(|arm| {
                    arm.guard.is_none()
                        && matches!(&arm.pattern, Pat::Wildcard { .. } | Pat::Var { .. })
                });
                if !has_catchall {
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "non-exhaustive pattern match on {}: add a wildcard `_` or variable pattern",
                            type_name
                        ),
                    ));
                }
            }
            return Ok(());
        }

        // For non-ADT, non-primitive types (e.g. Unit, records), skip.
        // Tuples are allowed through -- they're single-constructor types
        // handled natively by the Maranget algorithm.
        if !self.adt_variants.contains_key(&type_name) && type_name != "Tuple" {
            return Ok(());
        }

        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };

        // Build pattern matrix from arms (skip guarded arms for coverage,
        // but include them for redundancy checking)
        let mut matrix: Vec<Vec<SPat>> = Vec::new();

        for arm in arms {
            let spat = exh::simplify_pat(&arm.pattern);
            let row = vec![spat.clone()];

            // Redundancy check: is this arm useful w.r.t. prior unguarded arms?
            if arm.guard.is_none() && !exh::useful(&ctx, &matrix, &row) {
                let pat_str = exh::format_witness(&[spat]);
                return Err(Diagnostic::error_at(
                    arm.pattern.span(),
                    format!("unreachable pattern: {} already covered", pat_str),
                ));
            }

            // Only unguarded arms contribute to coverage
            if arm.guard.is_none() {
                matrix.push(row);
            }
        }

        // Exhaustiveness check: is a wildcard useful against the full matrix?
        let wildcard_row = vec![SPat::Wildcard];
        if exh::useful(&ctx, &matrix, &wildcard_row) {
            // Collect all uncovered witnesses for a complete error message
            let witnesses = exh::find_all_witnesses(&ctx, &matrix, 1);
            if !witnesses.is_empty() {
                let formatted: Vec<String> =
                    witnesses.iter().map(|w| exh::format_witness(w)).collect();
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "non-exhaustive pattern match: missing {}",
                        formatted.join(", ")
                    ),
                ));
            }
            return Err(Diagnostic::error_at(span, "non-exhaustive pattern match"));
        }

        Ok(())
    }

    /// Check do...else exhaustiveness: for each binding `pat <- expr`, find the
    /// constructors of the expr type NOT matched by `pat` (the "bail" constructors),
    /// and verify the else arms cover them all.
    pub(crate) fn check_do_exhaustiveness(
        &self,
        bindings: &[(Pat, Expr)],
        binding_types: &[Type],
        else_arms: &[ast::CaseArm],
        span: Span,
    ) -> Result<(), Diagnostic> {
        use super::exhaustiveness::{self as exh, ExhaustivenessCtx, SPat};

        // Collect all bail constructors needed across all bindings
        let mut needed: HashSet<String> = HashSet::new();

        for ((pat, _), ty) in bindings.iter().zip(binding_types.iter()) {
            let resolved = self.sub.apply(ty);
            let type_name = match &resolved {
                Type::Con(name, _) => name,
                _ => continue,
            };
            let all_variants = match self.adt_variants.get(type_name) {
                Some(v) => v,
                None => continue,
            };

            // If the binding pattern is a wildcard/var, it matches everything -- no bail
            match pat {
                Pat::Wildcard { .. } | Pat::Var { .. } => continue,
                _ => {}
            }

            // Find which constructor the binding pattern matches
            let matched = match pat {
                Pat::Constructor { name, .. } => Some(name.as_str()),
                Pat::Lit {
                    value: Lit::Bool(b),
                    ..
                } => Some(if *b { "True" } else { "False" }),
                _ => None,
            };

            for (v, _arity) in all_variants {
                if matched != Some(v.as_str()) {
                    needed.insert(v.clone());
                }
            }
        }

        if needed.is_empty() {
            return Ok(());
        }

        // Use Maranget to check else arm coverage
        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };

        // Build a matrix from else arms (each is a single-column pattern)
        let matrix: Vec<Vec<SPat>> = else_arms
            .iter()
            .filter(|arm| arm.guard.is_none())
            .map(|arm| vec![exh::simplify_pat(&arm.pattern)])
            .collect();

        // Check that each needed bail constructor is covered
        let mut missing_ctors = Vec::new();
        for ctor_name in &needed {
            let arity = self
                .adt_variants
                .values()
                .flat_map(|v| v.iter())
                .find(|(n, _)| n == ctor_name)
                .map(|(_, a)| *a)
                .unwrap_or(0);
            let row = vec![SPat::Constructor(
                ctor_name.clone(),
                vec![SPat::Wildcard; arity],
            )];
            if exh::useful(&ctx, &matrix, &row) {
                missing_ctors.push(ctor_name.as_str());
            }
        }

        if missing_ctors.is_empty() {
            Ok(())
        } else {
            missing_ctors.sort();
            Err(Diagnostic::error_at(
                span,
                format!(
                    "non-exhaustive do...else: missing {}",
                    missing_ctors.join(", ")
                ),
            ))
        }
    }
}
