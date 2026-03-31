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
        Type::Fun(a, b, row) => Type::Fun(
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
                tail: row.tail.as_ref().map(|t| Box::new(rename_vars(t, names))),
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
        Type::Fun(a, b, row) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
            for (_, args) in &row.effects {
                for t in args {
                    collect_free_vars(t, out);
                }
            }
            if let Some(tail) = &row.tail {
                collect_free_vars(tail, out);
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
        Type::Error => {}
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

            (Type::Var(id), _) => self.sub.bind(*id, &b),
            (_, Type::Var(id)) => self.sub.bind(*id, &a),

            (Type::Fun(a1, b1, row1), Type::Fun(a2, b2, row2)) => {
                self.unify(a1, a2)?;
                self.unify(b1, b2)?;
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

        match (r1.tail_var_id(), r2.tail_var_id()) {
            // Both closed: accept if one side is a subset of the other.
            // This is symmetric (unification doesn't know direction), so it
            // accepts both directions of effect subsumption. The directional
            // check (effectful callback where pure expected = error) is
            // enforced by check_callback_effect_subtype in infer.rs at
            // function application sites.
            (None, None) => {
                if extras1.is_empty() || extras2.is_empty() {
                    Ok(())
                } else {
                    // Both have unmatched effects -- genuinely incompatible
                    let mut extras: Vec<_> = extras1.iter().chain(extras2.iter())
                        .map(|(n, _)| n.as_str())
                        .collect();
                    extras.sort();
                    extras.dedup();
                    Err(Diagnostic::error(format!(
                        "effect mismatch: {{{}}}",
                        extras.join(", ")
                    )))
                }
            }
            // row1 is open: bind its tail to the extras from row2
            (Some(tail1), None) => {
                self.sub.bind_row(tail1, EffectRow::closed(extras2))
            }
            // row2 is open: bind its tail to the extras from row1
            (None, Some(tail2)) => {
                self.sub.bind_row(tail2, EffectRow::closed(extras1))
            }
            // Both open: create a fresh row variable for the shared tail
            (Some(tail1), Some(tail2)) => {
                if tail1 == tail2 {
                    return Ok(());
                }
                let fresh_var = self.fresh_var();
                self.sub.bind_row(tail1, EffectRow { effects: extras2, tail: Some(Box::new(fresh_var.clone())) })?;
                self.sub.bind_row(tail2, EffectRow { effects: extras1, tail: Some(Box::new(fresh_var)) })
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
    /// Each constraint is (trait_name, self_type, extra_type_arg_types).
    pub(crate) fn instantiate(&mut self, scheme: &Scheme) -> (Type, Vec<(String, Type, Vec<Type>)>) {
        let mapping: HashMap<u32, Type> = scheme
            .forall
            .iter()
            .map(|&id| (id, self.fresh_var()))
            .collect();
        let ty = self.replace_vars(&scheme.ty, &mapping);
        let constraints = scheme
            .constraints
            .iter()
            .map(|(trait_name, var_id, extra_types)| {
                let fresh = mapping.get(var_id).cloned().unwrap_or(Type::Var(*var_id));
                let extra_fresh: Vec<Type> = extra_types
                    .iter()
                    .map(|ty| self.replace_vars(ty, &mapping))
                    .collect();
                (trait_name.clone(), fresh, extra_fresh)
            })
            .collect();
        (ty, constraints)
    }

    pub(crate) fn replace_vars(&self, ty: &Type, mapping: &HashMap<u32, Type>) -> Type {
        match ty {
            Type::Var(id) => mapping.get(id).cloned().unwrap_or_else(|| ty.clone()),
            Type::Fun(a, b, row) => {
                Type::Fun(
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
                        tail: row.tail.as_ref().map(|t| Box::new(self.replace_vars(t, mapping))),
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
    
        }
    }

    /// Generalize a type over variables not free in the environment.
    pub(crate) fn generalize(&self, ty: &Type) -> Scheme {
        let resolved = self.sub.apply(ty);
        let env_vars = self.env.free_vars(&self.sub);
        // Collect effect type param vars that must not be generalized --
        // these are shared across ops of the same effect within a function scope.
        let effect_vars: HashSet<u32> = self
            .effect_meta
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
            crate::ast::TypeExpr::Named { name, span } => {
                // Record type reference for find-references (skip type variables/params)
                if name.starts_with(|c: char| c.is_uppercase()) {
                    self.lsp.type_references.push((*span, name.clone()));
                }
                // Resolve qualified type names (e.g. "M.Maybe" -> "Maybe") through
                // the scope map.
                let resolved = if name.contains('.') {
                    match self.scope_map.resolve_type(name).map(|s| s.to_string()) {
                        Some(canonical) => canonical,
                        None => {
                            self.collected_diagnostics.push(Diagnostic {
                                severity: Severity::Error,
                                message: format!("unknown qualified type '{}'", name),
                                span: Some(*span),
                            });
                            return Type::Error;
                        }
                    }
                } else {
                    name.clone()
                };
                Type::Con(resolved, vec![])
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
                        let id = if let Some((_, id)) = params.iter().find(|(n, _)| n == name) {
                            *id
                        } else {
                            let id = self.next_var;
                            self.next_var += 1;
                            params.push((name.clone(), id));
                            id
                        };
                        Box::new(Type::Var(id))
                    });
                    if effect_refs.is_empty() && tail.is_none() {
                        Type::arrow(a_ty, b_ty)
                    } else {
                        Type::Fun(Box::new(a_ty), Box::new(b_ty), EffectRow { effects: effect_refs, tail })
                    }
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
            crate::ast::TypeExpr::Labeled { inner, .. } => {
                self.convert_type_expr(inner, params)
            }
        }
    }
}
