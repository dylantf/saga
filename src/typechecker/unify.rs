use std::collections::{HashMap, HashSet};

use crate::token::Span;

use super::{Checker, Diagnostic, EffectRow, Scheme, Severity, Type};

/// Replace type variable IDs with readable names for display.
pub(super) fn rename_vars(ty: &Type, names: &HashMap<u32, String>) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(name) = names.get(id) {
                Type::Con(name.clone(), vec![])
            } else {
                ty.clone()
            }
        }
        Type::Arrow(a, b) => Type::Arrow(
            Box::new(rename_vars(a, names)),
            Box::new(rename_vars(b, names)),
        ),
        Type::EffArrow(a, b, row) => Type::EffArrow(
            Box::new(rename_vars(a, names)),
            Box::new(rename_vars(b, names)),
            EffectRow {
                effects: row.effects.iter()
                    .map(|(name, args)| {
                        (
                            name.clone(),
                            args.iter().map(|t| rename_vars(t, names)).collect(),
                        )
                    })
                    .collect(),
                // Rename row tail variable to readable name if in the mapping
                tail: row.tail,
            },
        ),
        Type::Con(name, args) => Type::Con(
            name.clone(),
            args.iter().map(|a| rename_vars(a, names)).collect(),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(fname, ty)| (fname.clone(), rename_vars(ty, names)))
                .collect(),
        ),
        Type::Error => Type::Error,
        Type::Never => Type::Never,
    }
}

/// Collect all free type variable IDs in a type (in order of first occurrence).
pub(crate) fn collect_free_vars(ty: &Type, out: &mut Vec<u32>) {
    match ty {
        Type::Var(id) => {
            if !out.contains(id) {
                out.push(*id);
            }
        }
        Type::Arrow(a, b) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
        }
        Type::EffArrow(a, b, row) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
            for (_, args) in &row.effects {
                for t in args {
                    collect_free_vars(t, out);
                }
            }
            if let Some(tail_id) = row.tail
                && !out.contains(&tail_id)
            {
                out.push(tail_id);
            }
        }
        Type::Con(_, args) => {
            for arg in args {
                collect_free_vars(arg, out);
            }
        }
        Type::Record(fields) => {
            for (_, ty) in fields {
                collect_free_vars(ty, out);
            }
        }
        Type::Error | Type::Never => {}
    }
}

impl Checker {
    // --- Unification ---

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        let a = self.sub.apply(a);
        let b = self.sub.apply(b);

        match (&a, &b) {
            _ if a == b => Ok(()),

            // Error type unifies with anything (suppresses cascading errors)
            (Type::Error, _) | (_, Type::Error) => Ok(()),

            // Var bindings before Never so that variables get bound to Never
            (Type::Var(id), _) => self.sub.bind(*id, &b),
            (_, Type::Var(id)) => self.sub.bind(*id, &a),

            // Never (bottom) unifies with anything
            (Type::Never, _) | (_, Type::Never) => Ok(()),

            (Type::Arrow(a1, a2), Type::Arrow(b1, b2)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)
            }
            // Arrow is effect-agnostic: unifies with any EffArrow (effects are
            // handled elsewhere via effect tracking, not unification).
            (Type::Arrow(a1, a2), Type::EffArrow(b1, b2, _))
            | (Type::EffArrow(a1, a2, _), Type::Arrow(b1, b2)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)
            }
            (Type::EffArrow(a1, a2, row1), Type::EffArrow(b1, b2, row2)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)?;
                self.unify_effect_rows(row1, row2)
            }

            (Type::Con(n1, args1), Type::Con(n2, args2))
                if n1 == n2 && args1.len() == args2.len() =>
            {
                for (a, b) in args1.iter().zip(args2.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }

            (Type::Record(f1), Type::Record(f2)) => {
                let names1: Vec<&str> = f1.iter().map(|(n, _)| n.as_str()).collect();
                let names2: Vec<&str> = f2.iter().map(|(n, _)| n.as_str()).collect();
                if names1 != names2 {
                    let a_display = self.prettify_type(&a);
                    let b_display = self.prettify_type(&b);
                    return Err(Diagnostic::error(format!(
                        "type mismatch: expected {}, got {}",
                        a_display, b_display
                    )));
                }
                for ((_, t1), (_, t2)) in f1.iter().zip(f2.iter()) {
                    self.unify(t1, t2)?;
                }
                Ok(())
            }

            _ => {
                let a_display = self.prettify_type(&a);
                let b_display = self.prettify_type(&b);
                Err(Diagnostic::error(format!(
                    "type mismatch: expected {}, got {}",
                    a_display, b_display
                )))
            }
        }
    }

    /// Unify two effect rows. Matches effects by name, unifies type args,
    /// then binds leftover effects to row variables (if open).
    fn unify_effect_rows(&mut self, row1: &EffectRow, row2: &EffectRow) -> Result<(), Diagnostic> {
        // Apply row substitutions to resolve any already-bound row variables
        let r1 = self.sub.apply_effect_row(row1);
        let r2 = self.sub.apply_effect_row(row2);

        // Match effects by name and unify their type args pairwise
        for (name, args1) in &r1.effects {
            if let Some((_, args2)) = r2.effects.iter().find(|(n, _)| n == name) {
                for (t1, t2) in args1.iter().zip(args2.iter()) {
                    self.unify(t1, t2)?;
                }
            }
        }

        // Collect unmatched effects from each side
        let extras1: Vec<_> = r1.effects.iter()
            .filter(|(n, _)| !r2.effects.iter().any(|(n2, _)| n2 == n))
            .cloned()
            .collect();
        let extras2: Vec<_> = r2.effects.iter()
            .filter(|(n, _)| !r1.effects.iter().any(|(n1, _)| n1 == n))
            .cloned()
            .collect();

        match (r1.tail, r2.tail) {
            // Both closed: unmatched effects are an error
            (None, None) => {
                if extras1.is_empty() && extras2.is_empty() {
                    Ok(())
                } else {
                    let all_extras: Vec<_> = extras1.iter().chain(extras2.iter())
                        .map(|(n, _)| n.as_str())
                        .collect();
                    Err(Diagnostic::error(format!(
                        "effect mismatch: {{{}}} not covered by closed effect row",
                        all_extras.join(", ")
                    )))
                }
            }
            // row1 is open: bind its tail to the extras from row2
            (Some(tail1), None) => {
                self.sub.bind_row(tail1, EffectRow { effects: extras2, tail: None })
            }
            // row2 is open: bind its tail to the extras from row1
            (None, Some(tail2)) => {
                self.sub.bind_row(tail2, EffectRow { effects: extras1, tail: None })
            }
            // Both open: create a fresh row variable for the shared tail
            (Some(tail1), Some(tail2)) => {
                if tail1 == tail2 {
                    // Same row variable: just check extras are empty
                    return Ok(());
                }
                let fresh = self.next_var;
                self.next_var += 1;
                self.sub.bind_row(tail1, EffectRow { effects: extras2, tail: Some(fresh) })?;
                self.sub.bind_row(tail2, EffectRow { effects: extras1, tail: Some(fresh) })
            }
        }
    }

    /// Format a type for error messages: apply substitutions, then replace
    /// any remaining unresolved type variables with readable names (a, b, c, ...).
    pub(crate) fn prettify_type(&self, ty: &Type) -> Type {
        let resolved = self.sub.apply(ty);
        let mut vars = Vec::new();
        collect_free_vars(&resolved, &mut vars);
        if vars.is_empty() {
            return resolved;
        }
        let names: HashMap<u32, String> = vars
            .iter()
            .enumerate()
            .map(|(i, &id)| {
                let name = ((b'a' + i as u8) as char).to_string();
                (id, name)
            })
            .collect();
        rename_vars(&resolved, &names)
    }

    /// Unify with span context: if unification fails, attach the span to the error.
    pub(crate) fn unify_at(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), Diagnostic> {
        self.unify(a, b).map_err(|e| e.with_span(span))
    }

    // --- Instantiation & Generalization ---

    /// Replace forall'd variables with fresh type variables.
    /// Returns the instantiated type and any trait constraints (remapped to fresh vars).
    pub(crate) fn instantiate(&mut self, scheme: &Scheme) -> (Type, Vec<(String, Type)>) {
        let mapping: HashMap<u32, Type> = scheme
            .forall
            .iter()
            .map(|&id| (id, self.fresh_var()))
            .collect();
        let ty = self.replace_vars(&scheme.ty, &mapping);
        let constraints = scheme
            .constraints
            .iter()
            .map(|(trait_name, var_id)| {
                let fresh = mapping.get(var_id).cloned().unwrap_or(Type::Var(*var_id));
                (trait_name.clone(), fresh)
            })
            .collect();
        (ty, constraints)
    }

    pub(crate) fn replace_vars(&self, ty: &Type, mapping: &HashMap<u32, Type>) -> Type {
        match ty {
            Type::Var(id) => mapping.get(id).cloned().unwrap_or_else(|| ty.clone()),
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.replace_vars(a, mapping)),
                Box::new(self.replace_vars(b, mapping)),
            ),
            Type::EffArrow(a, b, row) => {
                let new_tail = row.tail.map(|id| {
                    if let Some(Type::Var(new_id)) = mapping.get(&id) {
                        *new_id
                    } else {
                        id
                    }
                });
                Type::EffArrow(
                    Box::new(self.replace_vars(a, mapping)),
                    Box::new(self.replace_vars(b, mapping)),
                    EffectRow {
                        effects: row.effects.iter()
                            .map(|(name, args)| {
                                (
                                    name.clone(),
                                    args.iter().map(|t| self.replace_vars(t, mapping)).collect(),
                                )
                            })
                            .collect(),
                        tail: new_tail,
                    },
                )
            }
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter().map(|a| self.replace_vars(a, mapping)).collect(),
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(fname, ty)| (fname.clone(), self.replace_vars(ty, mapping)))
                    .collect(),
            ),
            Type::Error => Type::Error,
            Type::Never => Type::Never,
        }
    }

    /// Generalize a type over variables not free in the environment.
    pub(crate) fn generalize(&self, ty: &Type) -> Scheme {
        let resolved = self.sub.apply(ty);
        let env_vars = self.env.free_vars(&self.sub);
        // Collect effect type param vars that must not be generalized --
        // these are shared across ops of the same effect within a function scope.
        let effect_vars: HashSet<u32> = self
            .effect_state
            .type_param_cache
            .values()
            .flat_map(|mapping| {
                mapping.values().filter_map(|ty| {
                    let resolved = self.sub.apply(ty);
                    if let Type::Var(id) = resolved {
                        Some(id)
                    } else {
                        None
                    }
                })
            })
            .collect();
        let mut forall = Vec::new();
        collect_free_vars(&resolved, &mut forall);
        forall.retain(|v| !env_vars.contains(v) && !effect_vars.contains(v));
        Scheme {
            forall,
            constraints: vec![],
            ty: resolved,
        }
    }

    /// Convert a surface TypeExpr to our internal Type representation.
    pub(crate) fn convert_type_expr(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
    ) -> Type {
        match texpr {
            crate::ast::TypeExpr::Named { name, span } if name == "Never" => {
                self.lsp.type_references.push((*span, name.clone()));
                Type::Never
            }
            crate::ast::TypeExpr::Named { name, span } => {
                // Record type reference for find-references (skip type variables/params)
                if name.starts_with(|c: char| c.is_uppercase()) {
                    self.lsp.type_references.push((*span, name.clone()));
                }
                Type::Con(name.clone(), vec![])
            }
            crate::ast::TypeExpr::Var { name, .. } => {
                if let Some((_, id)) = params.iter().find(|(n, _)| n == name) {
                    Type::Var(*id)
                } else {
                    // New type variable -- create fresh and remember for reuse
                    let id = self.next_var;
                    self.next_var += 1;
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            }
            crate::ast::TypeExpr::App { func, arg, .. } => {
                let func_ty = self.convert_type_expr(func, params);
                let arg_ty = self.convert_type_expr(arg, params);
                // Type application: push arg into Con's args list
                match func_ty {
                    Type::Con(name, mut args) => {
                        args.push(arg_ty);
                        if let Some(&expected) = self.type_arity.get(&name)
                            && args.len() > expected
                        {
                            self.collected_diagnostics.push(Diagnostic {
                                severity: Severity::Error,
                                message: format!(
                                    "Type '{}' expects {} type argument{} but was given {}",
                                    name,
                                    expected,
                                    if expected == 1 { "" } else { "s" },
                                    args.len(),
                                ),
                                span: None,
                            });
                        }
                        Type::Con(name, args)
                    }
                    _ => {
                        // Shouldn't happen with well-formed type exprs
                        Type::Con("?".into(), vec![func_ty, arg_ty])
                    }
                }
            }
            crate::ast::TypeExpr::Arrow {
                from, to, effects, effect_row_var, ..
            } => {
                let a_ty = self.convert_type_expr(from, params);
                let b_ty = self.convert_type_expr(to, params);
                {
                    let effect_refs: Vec<(String, Vec<Type>)> = effects
                        .iter()
                        .map(|e| {
                            // Record effect name reference
                            let name_end = e.span.start + e.name.len();
                            self.lsp.type_references.push((
                                Span { start: e.span.start, end: name_end },
                                e.name.clone(),
                            ));
                            let args = e
                                .type_args
                                .iter()
                                .map(|te| self.convert_type_expr(te, params))
                                .collect();
                            (e.name.clone(), args)
                        })
                        .collect();
                    let tail = effect_row_var.as_ref().map(|(name, _)| {
                        if let Some((_, id)) = params.iter().find(|(n, _)| n == name) {
                            *id
                        } else {
                            let id = self.next_var;
                            self.next_var += 1;
                            params.push((name.clone(), id));
                            id
                        }
                    });
                    Type::EffArrow(Box::new(a_ty), Box::new(b_ty), EffectRow { effects: effect_refs, tail })
                }
            }
            crate::ast::TypeExpr::Record { fields, .. } => {
                let mut typed_fields: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(fname, texpr)| (fname.clone(), self.convert_type_expr(texpr, params)))
                    .collect();
                typed_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Type::Record(typed_fields)
            }
        }
    }
}
