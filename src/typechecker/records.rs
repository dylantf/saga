use crate::ast::Expr;
use crate::token::Span;

use super::{Checker, Diagnostic, Type};

impl Checker {
    // --- Record inference ---

    pub(crate) fn infer_record_create(
        &mut self,
        name: &str,
        fields: &[(String, Span, Expr)],
        span: Span,
    ) -> Result<Type, Diagnostic> {
        let info = self.records.get(name).cloned().ok_or_else(|| {
            Diagnostic::error_at(span, format!("undefined record type: {}", name))
        })?;
        // Record the type name reference for find-references/rename
        let name_end = span.start + name.len();
        self.lsp.type_references.push((
            crate::token::Span {
                start: span.start,
                end: name_end,
            },
            name.to_string(),
        ));
        let (inst_fields, result_ty) = self.instantiate_record(name, &info);

        for (fname, fspan, fexpr) in fields {
            let expected = inst_fields.iter().find(|(n, _)| n == fname);
            match expected {
                None => {
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        *fspan,
                        format!("unknown field '{}' on record {}", fname, name),
                    ));
                    // Still infer the expression to check for errors within it
                    let _ = self.infer_expr(fexpr);
                }
                Some((_, expected_ty)) => match self.infer_expr(fexpr) {
                    Ok(actual) => {
                        if let Err(e) = self.unify_at(expected_ty, &actual, fexpr.span) {
                            self.collected_diagnostics.push(e);
                        }
                    }
                    Err(e) => {
                        self.collected_diagnostics.push(e);
                    }
                },
            }
        }

        // Check for missing fields
        let provided: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
        let missing: Vec<&str> = inst_fields
            .iter()
            .filter(|(n, _)| !provided.contains(&n.as_str()))
            .map(|(n, _)| n.as_str())
            .collect();
        if !missing.is_empty() {
            self.collected_diagnostics.push(Diagnostic::error_at(
                span,
                format!(
                    "missing field{} on record {}: {}",
                    if missing.len() > 1 { "s" } else { "" },
                    name,
                    missing.join(", "),
                ),
            ));
        }

        Ok(result_ty)
    }

    pub(crate) fn infer_anon_record_create(
        &mut self,
        fields: &[(String, Span, Expr)],
    ) -> Result<Type, Diagnostic> {
        let mut typed_fields: Vec<(String, Type)> = Vec::new();
        for (fname, _fspan, fexpr) in fields {
            let ty = self.infer_expr(fexpr)?;
            typed_fields.push((fname.clone(), ty));
        }
        typed_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(Type::Record(typed_fields))
    }

    pub(crate) fn infer_record_update(
        &mut self,
        record: &Expr,
        fields: &[(String, Span, Expr)],
        span: Span,
    ) -> Result<Type, Diagnostic> {
        let rec_ty = self.infer_expr(record)?;
        let mut resolved = self.sub.apply(&rec_ty);

        if matches!(&resolved, Type::Var(_))
            && let Some((fname, _, _)) = fields.first()
        {
            let candidates: Vec<_> = self
                .records
                .iter()
                .filter(|(_, info)| info.fields.iter().any(|(n, _)| n == fname))
                .map(|(rname, _)| rname.clone())
                .collect();
            if candidates.len() == 1 {
                self.unify(&resolved, &Type::Con(candidates[0].clone(), vec![]))?;
                resolved = self.sub.apply(&rec_ty);
            }
        }

        match &resolved {
            Type::Con(name, _) => {
                let info = self.records.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(span, format!("type {} is not a record", name))
                })?;
                let (inst_fields, result_ty) = self.instantiate_record(name, &info);
                // Unify the record expression type with the instantiated result type
                // so that type params flow from the input record to the field types.
                self.unify_at(&resolved, &result_ty, span)?;
                for (fname, fspan, fexpr) in fields {
                    let expected =
                        inst_fields
                            .iter()
                            .find(|(n, _)| n == fname)
                            .ok_or_else(|| {
                                Diagnostic::error_at(
                                    *fspan,
                                    format!("unknown field '{}' on record {}", fname, name),
                                )
                            })?;
                    let actual = self.infer_expr(fexpr)?;
                    self.unify_at(&expected.1, &actual, fexpr.span)?;
                }
                Ok(self.sub.apply(&result_ty))
            }
            Type::Record(rec_fields) => {
                for (fname, fspan, fexpr) in fields {
                    let (_, expected_ty) =
                        rec_fields.iter().find(|(n, _)| n == fname).ok_or_else(|| {
                            Diagnostic::error_at(
                                *fspan,
                                format!("unknown field '{}' on anonymous record", fname),
                            )
                        })?;
                    let actual = self.infer_expr(fexpr)?;
                    self.unify_at(expected_ty, &actual, fexpr.span)?;
                }
                Ok(self.sub.apply(&resolved))
            }
            _ => Err(Diagnostic::error_at(
                span,
                format!("cannot update non-record type {}", resolved),
            )),
        }
    }

    pub(crate) fn infer_field_access(
        &mut self,
        record_expr: &Expr,
        field: &str,
        span: Span,
    ) -> Result<Type, Diagnostic> {
        let expr_ty = self.infer_expr(record_expr)?;

        // Empty field name means incomplete field access (e.g. `record.`).
        // The parser recovered, so we still have the receiver's type recorded.
        // Return a fresh type var so inference can continue.
        if field.is_empty() {
            return Ok(self.fresh_var());
        }

        let resolved = self.sub.apply(&expr_ty);

        match &resolved {
            Type::Con(name, _) => {
                let info = self.records.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(span, format!("type {} is not a record", name))
                })?;
                let (inst_fields, result_ty) = self.instantiate_record(name, &info);
                // Unify so that the record's concrete type args flow into field types
                self.unify_at(&resolved, &result_ty, span)?;
                let (_, field_ty) =
                    inst_fields
                        .iter()
                        .find(|(n, _)| n == field)
                        .ok_or_else(|| {
                            Diagnostic::error_at(
                                span,
                                format!("no field '{}' on record {}", field, name),
                            )
                        })?;
                Ok(self.sub.apply(field_ty))
            }
            Type::Var(id) => {
                let id = *id;
                // Collect candidates: for each record that has this field,
                // instantiate its type params to fresh vars and return both the
                // record result type and the field type.
                let candidates: Vec<_> = self
                    .records
                    .iter()
                    .filter(|(_, info)| info.fields.iter().any(|(n, _)| n == field))
                    .map(|(rname, _)| rname.clone())
                    .collect();
                match candidates.len() {
                    0 => Err(Diagnostic::error_at(
                        span,
                        format!("no record has field '{}'", field),
                    )),
                    1 => {
                        let rname = &candidates[0];
                        let info = self.records.get(rname).cloned().unwrap();
                        let (inst_fields, result_ty) = self.instantiate_record(rname, &info);
                        self.unify(&resolved, &result_ty)?;
                        let (_, field_ty) = inst_fields.iter().find(|(n, _)| n == field).unwrap();
                        Ok(self.sub.apply(field_ty))
                    }
                    _ => {
                        // Multiple records have this field. Narrow by intersecting
                        // with candidates already observed for this variable.
                        let narrowed: Vec<String> = match self.field_candidates.get(&id) {
                            Some((existing, _)) => candidates
                                .into_iter()
                                .filter(|n| existing.contains(n))
                                .collect(),
                            None => candidates,
                        };
                        match narrowed.len() {
                            0 => Err(Diagnostic::error_at(
                                span,
                                format!(
                                    "no single record type has all accessed fields (including '{}')",
                                    field
                                ),
                            )),
                            1 => {
                                let rname = &narrowed[0];
                                let info = self.records.get(rname).cloned().unwrap();
                                let (inst_fields, result_ty) =
                                    self.instantiate_record(rname, &info);
                                self.unify(&resolved, &result_ty)?;
                                self.field_candidates.remove(&id);
                                let (_, field_ty) =
                                    inst_fields.iter().find(|(n, _)| n == field).unwrap();
                                Ok(self.sub.apply(field_ty))
                            }
                            _ => {
                                // For ambiguity checking, instantiate each candidate
                                // and compare the resolved field types structurally.
                                let mut inst_results: Vec<(String, Type)> = Vec::new();
                                for rname in &narrowed {
                                    let info = self.records.get(rname).cloned().unwrap();
                                    let (inst_fields, _) = self.instantiate_record(rname, &info);
                                    let (_, field_ty) =
                                        inst_fields.iter().find(|(n, _)| n == field).unwrap();
                                    inst_results.push((rname.clone(), self.sub.apply(field_ty)));
                                }
                                let first_ty = &inst_results[0].1;
                                let all_agree = inst_results.iter().all(|(_, ty)| ty == first_ty);
                                if all_agree {
                                    self.field_candidates.insert(id, (narrowed, span));
                                    Ok(first_ty.clone())
                                } else {
                                    Err(Diagnostic::error_at(
                                        span,
                                        format!(
                                            "ambiguous field '{}': found in [{}] with different types; add a type annotation",
                                            field,
                                            narrowed.join(", ")
                                        ),
                                    ))
                                }
                            }
                        }
                    }
                }
            }
            Type::Record(fields) => {
                let (_, field_ty) = fields.iter().find(|(n, _)| n == field).ok_or_else(|| {
                    Diagnostic::error_at(span, format!("no field '{}' on anonymous record", field))
                })?;
                Ok(self.sub.apply(field_ty))
            }
            _ => Err(Diagnostic::error_at(
                span,
                format!("cannot access field '{}' on type {}", field, resolved),
            )),
        }
    }
}
