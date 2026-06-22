use std::collections::{HashMap, HashSet};

use crate::token::Span;

use crate::ast::Kind;

use super::{Checker, Diagnostic, EffectRow, Scheme, Severity, Type};

/// Substitute every `Type::Var(id)` whose id is a key in `subst` with the
/// corresponding type, recursively. Used to instantiate a type alias body
/// at a use site.
pub(crate) fn substitute_vars(ty: &Type, subst: &HashMap<u32, Type>) -> Type {
    match ty {
        Type::Var(id) => subst.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Type::Fun(a, b, row) => Type::Fun(
            Box::new(substitute_vars(a, subst)),
            Box::new(substitute_vars(b, subst)),
            EffectRow {
                effects: row
                    .effects
                    .iter()
                    .map(|entry| super::EffectEntry {
                        name: entry.name.clone(),
                        args: entry
                            .args
                            .iter()
                            .map(|t| substitute_vars(t, subst))
                            .collect(),
                    })
                    .collect(),
                tails: row
                    .tails
                    .iter()
                    .map(|t| substitute_vars(t, subst))
                    .collect(),
            },
        ),
        Type::Con(name, args) => Type::Con(
            name.clone(),
            args.iter().map(|a| substitute_vars(a, subst)).collect(),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(n, t)| (n.clone(), substitute_vars(t, subst)))
                .collect(),
        ),
        Type::Symbol(_) | Type::Error => ty.clone(),
    }
}

/// Error for the genuinely-ambiguous multi-open-tail case: a closed/partial
/// row is being matched against a row with two or more unconstrained open
/// tails, so it's undetermined which tail should absorb the extra effect(s).
fn ambiguous_row_error(extras: &[super::EffectEntry]) -> Diagnostic {
    let mut names: Vec<&str> = extras
        .iter()
        .map(|e| e.name.rsplit('.').next().unwrap_or(&e.name))
        .collect();
    names.sort();
    names.dedup();
    Diagnostic::error(format!(
        "ambiguous effect row: cannot determine which open row variable should \
         absorb effect{} {{{}}}; a row with two or more open tails (`..a, ..b`) \
         cannot be matched against a row carrying named effects not present in both",
        if names.len() == 1 { "" } else { "s" },
        names.join(", "),
    ))
}

pub(crate) fn kind_name(k: Kind) -> &'static str {
    match k {
        Kind::Star => "Star",
        Kind::Symbol => "Symbol",
    }
}

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
                effects: row
                    .effects
                    .iter()
                    .map(|entry| super::EffectEntry {
                        name: entry.name.clone(),
                        args: entry.args.iter().map(|t| rename_vars(t, names)).collect(),
                    })
                    .collect(),
                tails: row.tails.iter().map(|t| rename_vars(t, names)).collect(),
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
        Type::Symbol(name) => Type::Symbol(name.clone()),
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
            for entry in &row.effects {
                for t in &entry.args {
                    collect_free_vars(t, out);
                }
            }
            for tail in &row.tails {
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
        Type::Symbol(_) => {}
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

            // Symbol-vs-symbol: succeed iff names match (a == b case handled above).
            (Type::Symbol(n1), Type::Symbol(n2)) => Err(Diagnostic::error(format!(
                "type mismatch: expected '{}, got '{}",
                n1, n2
            ))),

            // Var binding: respect kinds.
            (Type::Var(id), Type::Var(id2)) => {
                let k1 = self.var_kind(*id);
                let k2 = self.var_kind(*id2);
                if k1 != k2 {
                    return Err(Diagnostic::error(format!(
                        "kind mismatch: expected kind {}, found kind {}",
                        kind_name(k1),
                        kind_name(k2),
                    )));
                }
                self.sub.bind(*id, &b)
            }
            (Type::Var(id), _) => {
                let vk = self.var_kind(*id);
                let other_kind = self.kind_of(&b);
                if vk != other_kind {
                    return Err(Diagnostic::error(format!(
                        "kind mismatch: expected kind {}, found kind {}",
                        kind_name(vk),
                        kind_name(other_kind),
                    )));
                }
                self.sub.bind(*id, &b)
            }
            (_, Type::Var(id)) => {
                let vk = self.var_kind(*id);
                let other_kind = self.kind_of(&a);
                if vk != other_kind {
                    return Err(Diagnostic::error(format!(
                        "kind mismatch: expected kind {}, found kind {}",
                        kind_name(vk),
                        kind_name(other_kind),
                    )));
                }
                self.sub.bind(*id, &a)
            }

            // Symbol vs non-var/non-symbol: kind mismatch.
            (Type::Symbol(_), _) | (_, Type::Symbol(_)) => Err(Diagnostic::error(format!(
                "kind mismatch: expected kind {}, found kind {}",
                kind_name(self.kind_of(&a)),
                kind_name(self.kind_of(&b)),
            ))),

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

            _ => Err(Diagnostic::error(self.format_type_mismatch(&a, &b))),
        }
    }

    /// Unify two effect rows. Matches effects by name, unifies type args,
    /// then binds leftover effects to row variables (if open).
    fn unify_effect_rows(&mut self, row1: &EffectRow, row2: &EffectRow) -> Result<(), Diagnostic> {
        // Apply row substitutions to resolve any already-bound row variables
        let r1 = self.sub.apply_effect_row(row1);
        let r2 = self.sub.apply_effect_row(row2);

        // Match effects by identity (instance + name) and unify their type args pairwise
        for entry1 in &r1.effects {
            if let Some(entry2) = r2.effects.iter().find(|e| e.matches(entry1)) {
                for (t1, t2) in entry1.args.iter().zip(entry2.args.iter()) {
                    self.unify(t1, t2)?;
                }
            }
        }

        // Collect unmatched effects from each side
        let extras1: Vec<_> = r1
            .effects
            .iter()
            .filter(|e| !r2.effects.iter().any(|e2| e2.matches(e)))
            .cloned()
            .collect();
        let extras2: Vec<_> = r2
            .effects
            .iter()
            .filter(|e| !r1.effects.iter().any(|e1| e1.matches(e)))
            .cloned()
            .collect();

        let tails1 = r1.tail_var_ids();
        let tails2 = r2.tail_var_ids();

        match (tails1.is_empty(), tails2.is_empty()) {
            // Both closed: accept if one side is a subset of the other.
            // This is symmetric (unification doesn't know direction), so it
            // accepts both directions of effect subsumption. The directional
            // check (effectful callback where pure expected = error) is
            // enforced by check_callback_effect_subtype in infer.rs at
            // function application sites.
            (true, true) => {
                if extras1.is_empty() || extras2.is_empty() {
                    Ok(())
                } else {
                    // Both have unmatched effects -- genuinely incompatible
                    let mut extras: Vec<_> = extras1
                        .iter()
                        .chain(extras2.iter())
                        .map(|e| e.name.as_str())
                        .collect();
                    extras.sort();
                    extras.dedup();
                    Err(Diagnostic::error(format!(
                        "effect mismatch: {{{}}}",
                        extras.join(", ")
                    )))
                }
            }
            // row1 open, row2 closed: row1's tails must absorb the effects that
            // row2 has but row1 lacks (extras2).
            (false, true) => self.absorb_extras_into_tails(&tails1, extras2),
            // row2 open, row1 closed: symmetric.
            (true, false) => self.absorb_extras_into_tails(&tails2, extras1),
            // Both open.
            (false, false) => self.unify_open_rows(&tails1, &tails2, extras1, extras2),
        }
    }

    /// Bind a set of open tails so the row absorbs `extras` (named effects the
    /// other, closed side carries that this side lacks).
    ///
    /// - No extras: each tail must be empty, so bind all to the empty row.
    /// - Extras with exactly one tail: that tail absorbs them.
    /// - Extras with two or more tails: genuinely ambiguous — which tail
    ///   absorbs them is undetermined, so report a clear error.
    fn absorb_extras_into_tails(
        &mut self,
        tails: &[u32],
        extras: Vec<super::EffectEntry>,
    ) -> Result<(), Diagnostic> {
        if extras.is_empty() {
            for &t in tails {
                self.sub.bind_row(t, EffectRow::empty())?;
            }
            return Ok(());
        }
        if tails.len() == 1 {
            return self.sub.bind_row(tails[0], EffectRow::closed(extras));
        }
        Err(ambiguous_row_error(&extras))
    }

    /// Unify two open rows (both have at least one tail). The fast path covers
    /// the common single-tail/single-tail case and identical tail sets; cases
    /// where named effects would have to be distributed across two or more
    /// open tails are genuinely ambiguous and produce a clear error.
    fn unify_open_rows(
        &mut self,
        tails1: &[u32],
        tails2: &[u32],
        extras1: Vec<super::EffectEntry>,
        extras2: Vec<super::EffectEntry>,
    ) -> Result<(), Diagnostic> {
        // Identical tail sets with no named extras: already equal.
        let set1: HashSet<u32> = tails1.iter().copied().collect();
        let set2: HashSet<u32> = tails2.iter().copied().collect();
        if set1 == set2 && extras1.is_empty() && extras2.is_empty() {
            return Ok(());
        }

        // Single tail on each side: classic open/open unification through a
        // fresh shared tail that carries whatever is common beyond the extras.
        if tails1.len() == 1 && tails2.len() == 1 {
            let (t1, t2) = (tails1[0], tails2[0]);
            if t1 == t2 {
                // Same variable on both sides; nothing left to do unless one
                // side has extras the other lacks, which can't happen since
                // the variable denotes the same set on both sides.
                return Ok(());
            }
            let fresh = self.fresh_var();
            self.sub.bind_row(
                t1,
                EffectRow {
                    effects: extras2,
                    tails: vec![fresh.clone()],
                },
            )?;
            return self.sub.bind_row(
                t2,
                EffectRow {
                    effects: extras1,
                    tails: vec![fresh],
                },
            );
        }

        // One side has a single tail and the other has several. If the
        // multi-tail side has no named effects the single side must absorb,
        // the single tail can stand for the union of the multi side's tails.
        if tails2.len() == 1 && !tails1.is_empty() && extras1.is_empty() {
            // extras2 (effects r2 has, r1 lacks) must be absorbed by r1's
            // tails — ambiguous when there are 2+ of them.
            if !extras2.is_empty() {
                return Err(ambiguous_row_error(&extras2));
            }
            return self.sub.bind_row(
                tails2[0],
                EffectRow {
                    effects: vec![],
                    tails: tails1.iter().map(|&id| Type::Var(id)).collect(),
                },
            );
        }
        if tails1.len() == 1 && !tails2.is_empty() && extras2.is_empty() {
            if !extras1.is_empty() {
                return Err(ambiguous_row_error(&extras1));
            }
            return self.sub.bind_row(
                tails1[0],
                EffectRow {
                    effects: vec![],
                    tails: tails2.iter().map(|&id| Type::Var(id)).collect(),
                },
            );
        }

        // Two or more open tails on a side with named effects to place, or
        // differing multi-tail sets: undetermined which tail absorbs what.
        let mut all_extras = extras1;
        all_extras.extend(extras2);
        Err(ambiguous_row_error(&all_extras))
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

    /// Format an `expected … got …` type-mismatch message. When the two types
    /// render identically under their bare names (e.g. `A.Foo` and `B.Foo` both
    /// print as `Foo`), fall back to module-qualified rendering so the message
    /// isn't the self-contradictory `expected Foo, got Foo`.
    pub(crate) fn format_type_mismatch(&self, expected: &Type, actual: &Type) -> String {
        let expected_p = self.prettify_type(expected);
        let actual_p = self.prettify_type(actual);
        let expected_str = expected_p.to_string();
        let actual_str = actual_p.to_string();
        if expected_str == actual_str {
            let expected_q = super::render_type_qualified(&expected_p);
            let actual_q = super::render_type_qualified(&actual_p);
            if expected_q != actual_q {
                return format!("type mismatch: expected {expected_q}, got {actual_q}");
            }
        }
        format!("type mismatch: expected {expected_str}, got {actual_str}")
    }

    /// Unify with span context: if unification fails, attach the span to the error.
    pub(crate) fn unify_at(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), Diagnostic> {
        self.unify(a, b).map_err(|e| e.with_span(span))
    }

    // --- Instantiation & Generalization ---

    /// Replace forall'd variables with fresh type variables.
    /// Returns the instantiated type and any trait constraints (remapped to fresh vars).
    /// Each constraint is (trait_name, self_type, extra_type_arg_types).
    pub(crate) fn instantiate(
        &mut self,
        scheme: &Scheme,
    ) -> (Type, Vec<(String, Type, Vec<Type>)>) {
        let mapping: HashMap<u32, Type> = scheme
            .forall
            .iter()
            .map(|&id| {
                let kind = self.var_kind(id);
                (id, self.fresh_var_of_kind(kind))
            })
            .collect();
        let ty = Self::replace_vars(&scheme.ty, &mapping);
        let constraints = scheme
            .constraints
            .iter()
            .map(|(trait_name, var_id, extra_types)| {
                let fresh = mapping.get(var_id).cloned().unwrap_or(Type::Var(*var_id));
                let extra_fresh: Vec<Type> = extra_types
                    .iter()
                    .map(|ty| Self::replace_vars(ty, &mapping))
                    .collect();
                (trait_name.clone(), fresh, extra_fresh)
            })
            .collect();
        (ty, constraints)
    }

    pub(crate) fn replace_vars(ty: &Type, mapping: &HashMap<u32, Type>) -> Type {
        match ty {
            Type::Var(id) => mapping.get(id).cloned().unwrap_or_else(|| ty.clone()),
            Type::Fun(a, b, row) => Type::Fun(
                Box::new(Self::replace_vars(a, mapping)),
                Box::new(Self::replace_vars(b, mapping)),
                EffectRow {
                    effects: row
                        .effects
                        .iter()
                        .map(|entry| super::EffectEntry {
                            name: entry.name.clone(),
                            args: entry
                                .args
                                .iter()
                                .map(|t| Self::replace_vars(t, mapping))
                                .collect(),
                        })
                        .collect(),
                    tails: row
                        .tails
                        .iter()
                        .map(|t| Self::replace_vars(t, mapping))
                        .collect(),
                },
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter()
                    .map(|a| Self::replace_vars(a, mapping))
                    .collect(),
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(fname, ty)| (fname.clone(), Self::replace_vars(ty, mapping)))
                    .collect(),
            ),
            Type::Symbol(name) => Type::Symbol(name.clone()),
            Type::Error => Type::Error,
        }
    }

    /// Apply variable substitution to an effect row.
    pub(crate) fn replace_vars_in_effect_row(
        &self,
        row: &EffectRow,
        mapping: &HashMap<u32, Type>,
    ) -> EffectRow {
        EffectRow {
            effects: row
                .effects
                .iter()
                .map(|entry| super::EffectEntry {
                    name: entry.name.clone(),
                    args: entry
                        .args
                        .iter()
                        .map(|t| Self::replace_vars(t, mapping))
                        .collect(),
                })
                .collect(),
            tails: row
                .tails
                .iter()
                .map(|t| Self::replace_vars(t, mapping))
                .collect(),
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
    /// Defaults to `Kind::Star` for the expected kind at the top level.
    pub(crate) fn convert_type_expr(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
    ) -> Type {
        let ty = self.convert_type_expr_kinded(texpr, params, Kind::Star);
        // After conversion, walk the type to catch any partial alias uses
        // that escaped to the top of nested positions (e.g. `Option Bag`
        // where `Bag` is a 1-arity alias used without an arg).
        self.check_no_partial_alias(&ty, texpr.span());
        ty
    }

    /// Walk `ty` and emit a diagnostic for any `Type::Con(alias_name, args)`
    /// where `args.len() != arity` — that means an alias was used without
    /// being fully applied. Only walks Star-shaped positions; doesn't touch
    /// already-substituted alias bodies (which contain no alias references).
    pub(crate) fn check_no_partial_alias(&mut self, ty: &Type, span: Span) {
        match ty {
            Type::Con(name, args) => {
                if let Some(info) = self.type_aliases.get(name) {
                    let expected = info.param_vars.len();
                    if args.len() != expected {
                        self.collected_diagnostics.push(Diagnostic::error_at(
                            span,
                            format!(
                                "type alias `{}` expects {} type argument{} but was given {}",
                                super::bare_type_name(name),
                                expected,
                                if expected == 1 { "" } else { "s" },
                                args.len(),
                            ),
                        ));
                    }
                }
                for a in args {
                    self.check_no_partial_alias(a, span);
                }
            }
            Type::Fun(a, b, row) => {
                self.check_no_partial_alias(a, span);
                self.check_no_partial_alias(b, span);
                for entry in &row.effects {
                    for a in &entry.args {
                        self.check_no_partial_alias(a, span);
                    }
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    self.check_no_partial_alias(t, span);
                }
            }
            Type::Var(_) | Type::Symbol(_) | Type::Error => {}
        }
    }

    /// If `name` is a registered type alias and `args.len() == arity`,
    /// substitute the alias body with the given args and return the
    /// instantiated type, recursively unfolding any nested aliases. Cycles
    /// must be rejected at registration time so this is guaranteed to
    /// terminate. Returns `None` if `name` isn't an alias or the arity
    /// doesn't match (partial application is caught by
    /// `check_no_partial_alias` at the top-level).
    pub(crate) fn try_unfold_alias(&self, name: &str, args: &[Type]) -> Option<Type> {
        let info = self.type_aliases.get(name)?;
        if args.len() != info.param_vars.len() {
            return None;
        }
        let subst: HashMap<u32, Type> = info
            .param_vars
            .iter()
            .zip(args.iter())
            .map(|(id, ty)| (*id, ty.clone()))
            .collect();
        let substituted = substitute_vars(&info.body, &subst);
        Some(self.unfold_aliases_in_type(substituted))
    }

    /// Walk `ty` and replace every `Type::Con(alias_name, args)` (where
    /// arity matches) with its instantiated body. Used to chase aliases
    /// transitively after substituting one alias's body — handles cases
    /// where an alias's body referred to another alias that wasn't yet
    /// registered when the body was originally converted.
    pub(crate) fn unfold_aliases_in_type(&self, ty: Type) -> Type {
        match ty {
            Type::Con(name, args) => {
                let args: Vec<Type> = args
                    .into_iter()
                    .map(|a| self.unfold_aliases_in_type(a))
                    .collect();
                if let Some(unfolded) = self.try_unfold_alias(&name, &args) {
                    return unfolded;
                }
                Type::Con(name, args)
            }
            Type::Fun(a, b, row) => Type::Fun(
                Box::new(self.unfold_aliases_in_type(*a)),
                Box::new(self.unfold_aliases_in_type(*b)),
                EffectRow {
                    effects: row
                        .effects
                        .into_iter()
                        .map(|entry| super::EffectEntry {
                            name: entry.name,
                            args: entry
                                .args
                                .into_iter()
                                .map(|t| self.unfold_aliases_in_type(t))
                                .collect(),
                        })
                        .collect(),
                    tails: row
                        .tails
                        .into_iter()
                        .map(|t| self.unfold_aliases_in_type(t))
                        .collect(),
                },
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .into_iter()
                    .map(|(n, t)| (n, self.unfold_aliases_in_type(t)))
                    .collect(),
            ),
            other => other,
        }
    }

    /// Like `convert_type_expr` but enforces that the resulting type has
    /// kind `expected_kind`. Used to detect kind mismatches such as
    /// `Maybe 'foo` or `Id Int` (when `Id` expects a Symbol-kinded arg).
    pub(crate) fn convert_type_expr_kinded(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
        expected_kind: Kind,
    ) -> Type {
        match texpr {
            crate::ast::TypeExpr::Named { id, name, span } => {
                // Record type reference for find-references (skip type variables/params)
                if name.starts_with(|c: char| c.is_uppercase()) {
                    self.lsp
                        .type_references
                        .push((*span, self.resolved_type_name(*id, name)));
                }
                let resolved = self.resolved_type_name(*id, name);
                let had_resolution = self.resolution.type_ref(*id).is_some()
                    || self.scope_map.resolve_type(name).is_some();

                // If scope_map didn't resolve it, canonicalize_type_name didn't
                // change it, it's not in type_arity, and it's not a known
                // builtin canonical form (e.g. "Std.Base.Tuple" from parser
                // desugaring), the type is genuinely unknown. Report the error
                // here rather than letting a bare Type::Con propagate and cause
                // confusing "expected Foo, got Foo" mismatches downstream.
                if resolved == *name
                    && !had_resolution
                    && !self.type_arity.contains_key(name)
                    && !super::is_builtin_canonical(name)
                {
                    self.collected_diagnostics
                        .push(Diagnostic::error(format!("unknown type '{name}'")).with_span(*span));
                    return Type::Error;
                }

                // Named types always have kind Star in the current kind system.
                if expected_kind != Kind::Star {
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        *span,
                        format!(
                            "kind mismatch: '{}' has kind Star but kind {} was expected here",
                            name,
                            kind_name(expected_kind),
                        ),
                    ));
                    return Type::Error;
                }
                // If this references a zero-arity alias, unfold it immediately.
                // For positive-arity aliases used here without args we leave
                // a Type::Con(alias_name, []) so the enclosing App can grow
                // it; partial uses are caught by the top-level walker.
                if let Some(unfolded) = self.try_unfold_alias(&resolved, &[]) {
                    return unfolded;
                }
                Type::Con(resolved, vec![])
            }
            crate::ast::TypeExpr::Var { name, .. } => {
                let existing_id = params
                    .iter()
                    .find(|(n, _)| n == name)
                    .map(|(_, id)| *id)
                    .or_else(|| self.outer_named_type_vars.get(name).copied());
                if let Some(id) = existing_id {
                    let actual = self.var_kind(id);
                    if actual != expected_kind {
                        self.collected_diagnostics.push(Diagnostic::error_at(
                            texpr.span(),
                            format!(
                                "kind mismatch: type variable `{}` has kind {} but kind {} was expected here",
                                name,
                                kind_name(actual),
                                kind_name(expected_kind),
                            ),
                        ));
                        return Type::Error;
                    }
                    // Only seed `params` if the binding came from the outer
                    // scope — keeps the local list consistent for callers
                    // that scan it after conversion.
                    if !params.iter().any(|(n, _)| n == name) {
                        params.push((name.clone(), id));
                    }
                    Type::Var(id)
                } else {
                    // New type variable -- create fresh, with the expected kind,
                    // and remember for reuse.
                    let var = self.fresh_var_of_kind(expected_kind);
                    let id = match var {
                        Type::Var(id) => id,
                        _ => unreachable!(),
                    };
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            }
            crate::ast::TypeExpr::App { func, arg, .. } => {
                // The head of an App is always Star-kinded (a type constructor).
                let func_ty = self.convert_type_expr_kinded(func, params, Kind::Star);
                // Determine arg's expected kind from the head's registered kinds.
                let head_name = match &func_ty {
                    Type::Con(name, _) => Some(name.clone()),
                    _ => None,
                };
                let arg_pos = match &func_ty {
                    Type::Con(_, args) => args.len(),
                    _ => 0,
                };
                let arg_expected_kind = head_name
                    .as_ref()
                    .and_then(|n| self.type_param_kinds.get(n))
                    .and_then(|kinds| kinds.get(arg_pos).copied())
                    .unwrap_or(Kind::Star);
                let arg_ty = self.convert_type_expr_kinded(arg, params, arg_expected_kind);
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
                        // If this is a type alias and now fully applied, unfold.
                        if let Some(unfolded) = self.try_unfold_alias(&name, &args) {
                            return unfolded;
                        }
                        Type::Con(name, args)
                    }
                    Type::Error => Type::Error,
                    _ => {
                        // Shouldn't happen with well-formed type exprs
                        Type::Con("?".into(), vec![func_ty, arg_ty])
                    }
                }
            }
            crate::ast::TypeExpr::Arrow {
                from,
                to,
                effects,
                effect_row_var,
                ..
            } => {
                if expected_kind != Kind::Star {
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        texpr.span(),
                        format!(
                            "kind mismatch: function type has kind Star but kind {} was expected here",
                            kind_name(expected_kind),
                        ),
                    ));
                    return Type::Error;
                }
                let a_ty = self.convert_type_expr_kinded(from, params, Kind::Star);
                let b_ty = self.convert_type_expr_kinded(to, params, Kind::Star);
                {
                    let effect_refs: Vec<super::EffectEntry> = effects
                        .iter()
                        .map(|e| {
                            // Record effect name reference
                            let name_end = e.span.start + e.name.len();
                            self.lsp.type_references.push((
                                Span {
                                    start: e.span.start,
                                    end: name_end,
                                },
                                self.resolved_effect_name(e.id, &e.name),
                            ));
                            let args = self.convert_effect_ref_args(e, params);
                            let name = self.resolved_effect_name(e.id, &e.name);
                            if !self.effects.contains_key(&name) {
                                self.collected_diagnostics.push(Diagnostic::error_at(
                                    e.span,
                                    format!("undefined effect: {}", e.name),
                                ));
                            }
                            super::EffectEntry::unnamed(name, args)
                        })
                        .collect();
                    let tails: Vec<Type> = effect_row_var
                        .iter()
                        .map(|(name, _)| {
                            let id = if let Some((_, id)) = params.iter().find(|(n, _)| n == name) {
                                *id
                            } else {
                                let id = self.next_var;
                                self.next_var += 1;
                                params.push((name.clone(), id));
                                id
                            };
                            Type::Var(id)
                        })
                        .collect();
                    if effect_refs.is_empty() && tails.is_empty() {
                        Type::arrow(a_ty, b_ty)
                    } else {
                        Type::Fun(
                            Box::new(a_ty),
                            Box::new(b_ty),
                            EffectRow {
                                effects: effect_refs,
                                tails,
                            },
                        )
                    }
                }
            }
            crate::ast::TypeExpr::Record { fields, .. } => {
                if expected_kind != Kind::Star {
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        texpr.span(),
                        format!(
                            "kind mismatch: record type has kind Star but kind {} was expected here",
                            kind_name(expected_kind),
                        ),
                    ));
                    return Type::Error;
                }
                let mut typed_fields: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(fname, texpr)| {
                        (
                            fname.clone(),
                            self.convert_type_expr_kinded(texpr, params, Kind::Star),
                        )
                    })
                    .collect();
                typed_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Type::Record(typed_fields)
            }
            crate::ast::TypeExpr::Labeled { inner, .. } => {
                self.convert_type_expr_kinded(inner, params, expected_kind)
            }
            // Symbol literals inhabit kind `Symbol`.
            crate::ast::TypeExpr::Symbol { name, span, .. } => {
                if expected_kind != Kind::Symbol {
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        *span,
                        format!(
                            "kind mismatch: symbol literal '{} has kind Symbol but kind {} was expected here",
                            name,
                            kind_name(expected_kind),
                        ),
                    ));
                    return Type::Error;
                }
                Type::Symbol(name.clone())
            }
        }
    }

    pub(crate) fn convert_user_type_expr(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
    ) -> Type {
        let ty = self.convert_type_expr(texpr, params);
        self.canonicalize_handler_effect_types(ty)
    }

    pub(crate) fn canonicalize_handler_effect_types(&mut self, ty: Type) -> Type {
        match ty {
            Type::Fun(param, ret, row) => Type::Fun(
                Box::new(self.canonicalize_handler_effect_types(*param)),
                Box::new(self.canonicalize_handler_effect_types(*ret)),
                EffectRow {
                    effects: row
                        .effects
                        .into_iter()
                        .map(|entry| super::EffectEntry {
                            name: entry.name,
                            args: entry
                                .args
                                .into_iter()
                                .map(|arg| self.canonicalize_handler_effect_types(arg))
                                .collect(),
                        })
                        .collect(),
                    tails: row.tails,
                },
            ),
            Type::Con(name, args) => {
                let args: Vec<Type> = args
                    .into_iter()
                    .map(|arg| self.canonicalize_handler_effect_types(arg))
                    .collect();
                if name == super::canonicalize_type_name("Handler") {
                    let canonical_args = args
                        .into_iter()
                        .map(|arg| match arg {
                            Type::Con(effect_name, effect_args) if !effect_name.contains('.') => {
                                Type::Con(self.canonical_effect_name(&effect_name), effect_args)
                            }
                            other => other,
                        })
                        .collect();
                    Type::Con(name, canonical_args)
                } else {
                    Type::Con(name, args)
                }
            }
            Type::Record(fields) => Type::Record(
                fields
                    .into_iter()
                    .map(|(name, ty)| (name, self.canonicalize_handler_effect_types(ty)))
                    .collect(),
            ),
            other => other,
        }
    }
}
