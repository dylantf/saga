use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, ExprKind, Stmt};
use crate::token::Span;

use super::{Checker, Diagnostic, EffectRow, Scheme, Severity, Type};

/// One step from the two types handed to a top-level unification down to the
/// pair of function types whose effect rows are being compared.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum UnifyStep {
    /// Into argument `i` of a type constructor (`List (...)`, a tuple slot).
    ConArg(usize),
    /// Into a function's parameter type.
    FunParam,
    /// Into a function's return type. Not "depth": functions are curried and
    /// effects sit on an inner arrow, so `A -> B -> C needs {E}` reaches its
    /// row through one return step.
    FunRet,
    /// Into the named field of an anonymous record type.
    RecordField(String),
    /// Into a type argument of an effect in a row (`Fail (..)`).
    EffectArg,
}

/// Two effect rows that are not equal, as handed to the error messages for
/// the effect-row rule.
#[derive(Clone, Debug)]
pub(crate) struct RowSubsumption {
    /// Where in the unified types the rows sit.
    pub(crate) path: Vec<UnifyStep>,
    /// The full rows, in the argument order of the top-level unification.
    pub(crate) left: EffectRow,
    pub(crate) right: EffectRow,
    /// True when the left row is the larger one (the right row is a strict
    /// subset of it); false when the right row is the larger one.
    pub(crate) left_is_larger: bool,
}

/// What a top-level unification is being used for, as far as effect-row
/// subsumption is concerned.
#[derive(Clone, Copy)]
pub(crate) enum RowPosition<'a> {
    /// Not a coercion position: closed rows must be equal.
    Exact,
    /// The two types are already nested inside a larger type (e.g. the
    /// parameter types of two functions being joined): closed rows must be
    /// equal and a mismatch is reported as "at depth".
    Nested,
    /// A coercion position. A value of the *actual* type is used where the
    /// *expected* type is wanted, so the actual row may be a subset of the
    /// expected row, but not the other way round. `expr` is the expression
    /// that produced the actual type, when there is one: tuple, list and
    /// anonymous-record literals (and `if`/`case`/block results) extend the
    /// coercion position to their elements.
    Coercion {
        actual_is_left: bool,
        expr: Option<&'a Expr>,
    },
}

/// `RowPosition` as kept on the checker while a unification runs, so that
/// `unify_effect_rows` can decide each pair of rows as it meets them.
#[derive(Clone, Debug, Default)]
pub(crate) enum RowMode {
    /// `unify` without a position: unequal closed rows are accepted when one
    /// is a subset of the other, in either direction.
    #[default]
    Lenient,
    Exact,
    Nested,
    Coercion {
        actual_is_left: bool,
        shape: DirectShape,
    },
}

/// The literal structure of a coerced expression that extends a coercion
/// position to its elements (see `RowPosition::Coercion`).
#[derive(Clone, Debug)]
pub(crate) enum DirectShape {
    /// No literal structure: only the value's own arrows are direct.
    Leaf,
    Tuple(Vec<DirectShape>),
    Record(Vec<(String, DirectShape)>),
    /// A list literal's elements, all at the one element type.
    List(Vec<DirectShape>),
    /// `if`/`case` branches and a block's last expression: a path is direct
    /// if it is direct into every one of them.
    Branches(Vec<DirectShape>),
}

impl DirectShape {
    pub(crate) fn of(expr: Option<&Expr>) -> DirectShape {
        let Some(expr) = expr else {
            return DirectShape::Leaf;
        };
        match &expr.kind {
            ExprKind::Tuple { elements } => {
                DirectShape::Tuple(elements.iter().map(|e| Self::of(Some(e))).collect())
            }
            ExprKind::AnonRecordCreate { fields } => DirectShape::Record(
                fields
                    .iter()
                    .map(|(name, _, e)| (name.clone(), Self::of(Some(e))))
                    .collect(),
            ),
            ExprKind::App { .. } => match super::infer::collect_list_literal_elements(expr) {
                Some(elements) => {
                    DirectShape::List(elements.iter().map(|e| Self::of(Some(e))).collect())
                }
                None => DirectShape::Leaf,
            },
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => DirectShape::Branches(vec![
                Self::of(Some(then_branch)),
                Self::of(Some(else_branch)),
            ]),
            ExprKind::Case { arms, .. } => DirectShape::Branches(
                arms.iter().map(|arm| Self::of(Some(&arm.node.body))).collect(),
            ),
            ExprKind::Block { stmts, .. } => match stmts.last().map(|s| &s.node) {
                Some(Stmt::Expr(last)) => DirectShape::Branches(vec![Self::of(Some(last))]),
                _ => DirectShape::Branches(vec![]),
            },
            _ => DirectShape::Leaf,
        }
    }

    /// Does `path` lead to a position where subsumption is allowed? True when
    /// the path consists of return steps only (the row sits on the value's
    /// own arrow), after walking through literal structure that mirrors
    /// leading type steps.
    fn is_direct(&self, path: &[UnifyStep]) -> bool {
        let Some(first) = path.first() else {
            return true;
        };
        if *first == UnifyStep::FunRet {
            return path.iter().all(|step| *step == UnifyStep::FunRet);
        }
        match (self, first) {
            (DirectShape::Tuple(elements), UnifyStep::ConArg(i)) => elements
                .get(*i)
                .is_some_and(|elem| elem.is_direct(&path[1..])),
            (DirectShape::Record(fields), UnifyStep::RecordField(name)) => fields
                .iter()
                .find(|(fname, _)| fname == name)
                .is_some_and(|(_, shape)| shape.is_direct(&path[1..])),
            (DirectShape::List(elements), UnifyStep::ConArg(0)) => {
                elements.iter().all(|elem| elem.is_direct(&path[1..]))
            }
            (DirectShape::Branches(branches), _) => {
                !branches.is_empty() && branches.iter().all(|b| b.is_direct(path))
            }
            _ => false,
        }
    }
}

/// What a row variable created for typing `resume` is for (see
/// `Checker::slack_rows`). Both kinds are closed to the empty row when the
/// `with` (or handler declaration) that made them has been checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Slack {
    /// The open tail added to an arrow of a handler's answer type, which
    /// takes whatever the arms' function values perform.
    Answer,
    /// The part of what `resume` performs that comes from the arms
    /// themselves (`ρ_arm`).
    Arm,
}

/// Phrase that identifies the "one application per effect family" error, so
/// callers that rewrite unification errors can let it through unchanged.
pub(crate) const FAMILY_CONFLICT_MARKER: &str = "can hold only one";

/// Prefix of every effect-row rule error (unequal closed rows where they
/// must be equal, or a function used where one with fewer effects is
/// expected), so callers that rewrite unification errors can let it through
/// unchanged.
pub(crate) const ROW_RULE_MARKER: &str = "effect row mismatch: ";

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
        Type::Error => ty.clone(),
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
        Type::Error => {}
    }
}

impl Checker {
    // --- Unification ---

    /// Unify two types with no position information. Unequal closed effect
    /// rows accepted along the way are not reported: use `unify_at` or one of
    /// the `coerce_*` entry points wherever a source span is available.
    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        self.unify_path.clear();
        let saved = std::mem::take(&mut self.row_mode);
        let result = self.unify_rec(a, b);
        self.row_mode = saved;
        result
    }

    /// Recurse into a component of the types being unified, tracking the step
    /// taken so `unify_effect_rows` knows where it is.
    fn unify_step(&mut self, step: UnifyStep, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        self.unify_path.push(step);
        let result = self.unify_rec(a, b);
        self.unify_path.pop();
        result
    }

    fn unify_rec(&mut self, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        let a = self.sub.apply(a);
        let b = self.sub.apply(b);

        match (&a, &b) {
            _ if a == b => Ok(()),

            // Error type unifies with anything (suppresses cascading errors)
            (Type::Error, _) | (_, Type::Error) => Ok(()),

            (Type::Var(id), _) => self.sub.bind(*id, &b),
            (_, Type::Var(id)) => self.sub.bind(*id, &a),

            (Type::Fun(a1, b1, row1), Type::Fun(a2, b2, row2)) => {
                self.unify_step(UnifyStep::FunParam, a1, a2)?;
                self.unify_step(UnifyStep::FunRet, b1, b2)?;
                self.unify_effect_rows(row1, row2)
            }

            (Type::Con(n1, args1), Type::Con(n2, args2))
                if n1 == n2 && args1.len() == args2.len() =>
            {
                for (i, (a, b)) in args1.iter().zip(args2.iter()).enumerate() {
                    self.unify_step(UnifyStep::ConArg(i), a, b)?;
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
                for ((name, t1), (_, t2)) in f1.iter().zip(f2.iter()) {
                    self.unify_step(UnifyStep::RecordField(name.clone()), t1, t2)?;
                }
                Ok(())
            }

            _ => Err(Diagnostic::error(self.format_type_mismatch(&a, &b))),
        }
    }

    /// Unify two effect rows. Matches effects by name, unifies type args,
    /// then binds leftover effects to row variables (if open).
    fn unify_effect_rows(&mut self, row1: &EffectRow, row2: &EffectRow) -> Result<(), Diagnostic> {
        if row1.is_empty() && row2.is_empty() {
            return Ok(());
        }
        // Resolve already-bound row variables. A row holds one application
        // per effect family, so a row variable that was bound to a row naming
        // a family this row also names has its arguments unified here.
        let r1 = self.normalize_row(row1)?;
        let r2 = self.normalize_row(row2)?;

        // Match effects by identity (instance + name) and unify their type args pairwise
        for entry1 in &r1.effects {
            if let Some(entry2) = r2.effects.iter().find(|e| e.matches(entry1)) {
                for (t1, t2) in entry1.args.iter().zip(entry2.args.iter()) {
                    self.unify_step(UnifyStep::EffectArg, t1, t2)?;
                }
            }
        }

        // At a coercion position, directly, a row involving a declared row
        // variable or one created for `resume` is compared by inclusion
        // (`subsume_rows`): equality would bind those variables to make the
        // rows equal, pinning what the caller chooses or what resuming
        // performs. Other rows are unified as equal, which is one way for the
        // inclusion to hold and keeps inference as it was.
        if let Some(actual_is_left) = self.direct_coercion()
            && (self.row_is_protected(&r1) || self.row_is_protected(&r2))
        {
            let (actual, expected) = if actual_is_left {
                (&r1, &r2)
            } else {
                (&r2, &r1)
            };
            return self.subsume_rows(actual, expected, actual_is_left);
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

        // A tail both rows have stands for the same effects on both sides,
        // so it cancels: `{..a, ..b} ~ {..b}` is `{..a} ~ {}` (binding `b`
        // to a row containing `b` would be an infinite row). What the two
        // rows still differ in must then be the same set of effects, except
        // that a shared tail can hold the named effects only one side has:
        // `{Stop, ..r} ~ {..r}` holds when `r` contains Stop.
        let all1 = r1.tail_var_ids();
        let all2 = r2.tail_var_ids();
        let common: Vec<u32> = all1.iter().copied().filter(|t| all2.contains(t)).collect();
        let tails1: Vec<u32> = all1.into_iter().filter(|t| !common.contains(t)).collect();
        let tails2: Vec<u32> = all2.into_iter().filter(|t| !common.contains(t)).collect();
        if !common.is_empty() && tails1.is_empty() && tails2.is_empty() {
            let mut differing = extras1;
            differing.extend(extras2);
            if differing.is_empty() {
                return Ok(());
            }
            if common.len() == 1 {
                let fresh = self.fresh_var();
                return self.bind_row_checked(
                    common[0],
                    EffectRow {
                        effects: differing,
                        tails: vec![fresh],
                    },
                );
            }
            return Err(ambiguous_row_error(&differing));
        }

        match (tails1.is_empty(), tails2.is_empty()) {
            // Both closed: one side may be a subset of the other only where
            // the position allows it (see `unequal_rows`).
            (true, true) => {
                if extras1.is_empty() && extras2.is_empty() {
                    Ok(())
                } else if extras1.is_empty() || extras2.is_empty() {
                    self.unequal_rows(&r1, &r2, !extras1.is_empty())
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
            // row2 has but row1 lacks (extras2). The effects only row1 names
            // are not in row2 at all: see `open_side_extras`.
            (false, true) => {
                self.absorb_extras_into_tails(&tails1, extras2)?;
                self.open_side_extras(&r1, &r2, true, extras1, &common)
            }
            // row2 open, row1 closed: symmetric.
            (true, false) => {
                self.absorb_extras_into_tails(&tails2, extras1)?;
                self.open_side_extras(&r1, &r2, false, extras2, &common)
            }
            // Both open.
            (false, false) => self.unify_open_rows(&tails1, &tails2, extras1, extras2),
        }
    }

    /// A row variable that a coercion must not bind to make room: one fixed
    /// by a declared signature (or standing for a where-bound type's impl
    /// row).
    pub(crate) fn is_rigid_tail(&self, tail: u32) -> bool {
        self.rigid_row_var_for(tail).is_some() || self.is_where_bound_var(tail)
    }

    fn row_is_protected(&self, row: &EffectRow) -> bool {
        row.tail_var_ids()
            .into_iter()
            .any(|t| self.slack_rows.contains_key(&t) || self.is_rigid_tail(t))
    }

    /// `actual ⊆ expected`, for rows already normalised and with the
    /// arguments of the families both name unified. Nothing is bound when
    /// the inclusion already holds (`{} ⊆ {..e}`, `{Stop} ⊆ {Stop, ..e}`).
    /// Otherwise what `actual` has beyond `expected` (named effects, and
    /// tails `expected` lacks) goes into one tail of `expected` that may
    /// grow: one created for `resume`'s answer type, else `ρ_arm`, else an
    /// inference variable; a declared row variable is never chosen. With no
    /// such tail, missing named effects are the coercion error, and each
    /// missing tail must fit in `expected` as it is: an inference variable
    /// is bound to it, a declared one to its named effects (closing it, which
    /// `check_rigid_row_vars_abstract` then reports).
    fn subsume_rows(
        &mut self,
        actual: &EffectRow,
        expected: &EffectRow,
        actual_is_left: bool,
    ) -> Result<(), Diagnostic> {
        let missing: Vec<super::EffectEntry> = actual
            .effects
            .iter()
            .filter(|e| !expected.effects.iter().any(|x| x.matches(e)))
            .cloned()
            .collect();
        let expected_tails = expected.tail_var_ids();
        let missing_tails: Vec<u32> = actual
            .tail_var_ids()
            .into_iter()
            .filter(|t| !expected_tails.contains(t))
            .collect();
        if missing.is_empty() && missing_tails.is_empty() {
            return Ok(());
        }
        let of_kind = |checker: &Self, kind: Slack| -> Vec<u32> {
            expected_tails
                .iter()
                .copied()
                .filter(|t| checker.slack_rows.get(t) == Some(&kind))
                .collect()
        };
        let mut candidates = of_kind(self, Slack::Answer);
        if candidates.is_empty() {
            candidates = of_kind(self, Slack::Arm);
        }
        if candidates.is_empty() {
            candidates = expected_tails
                .iter()
                .copied()
                .filter(|t| !self.slack_rows.contains_key(t) && !self.is_rigid_tail(*t))
                .collect();
        }
        if let [absorber] = candidates[..] {
            let mut tails: Vec<Type> = missing_tails.iter().map(|&t| Type::Var(t)).collect();
            if let Some(&kind) = self.slack_rows.get(&absorber) {
                // What is left of a slack variable is slack too.
                let rest = self.fresh_var();
                if let Type::Var(id) = rest {
                    self.slack_rows.insert(id, kind);
                }
                tails.push(rest);
            }
            return self.bind_row_checked(
                absorber,
                EffectRow {
                    effects: missing,
                    tails,
                },
            );
        }
        if !missing.is_empty() {
            if candidates.len() > 1 {
                return Err(ambiguous_row_error(&missing));
            }
            let (left, right) = if actual_is_left {
                (actual.clone(), expected.clone())
            } else {
                (expected.clone(), actual.clone())
            };
            let subsumption = RowSubsumption {
                path: self.unify_path.clone(),
                left,
                right,
                left_is_larger: actual_is_left,
            };
            let message = self
                .coercion_error(&subsumption, actual_is_left)
                .unwrap_or_else(|| "effect row mismatch".to_string());
            return Err(Diagnostic::error(message));
        }
        for tail in missing_tails {
            let row = if self.is_rigid_tail(tail) {
                EffectRow::closed(
                    expected
                        .effects
                        .iter()
                        .filter(|e| !actual.effects.iter().any(|a| a.matches(e)))
                        .cloned()
                        .collect(),
                )
            } else {
                expected.clone()
            };
            self.bind_row_checked(tail, row)?;
        }
        Ok(())
    }

    /// Named effects of the open side of an open-vs-closed unification that
    /// the closed side lacks (`{Stop | e} ~ {}`). Binding the open side's
    /// tails cannot make them disappear: either a tail both rows share holds
    /// them, or the rows really differ by them. The latter is the same
    /// situation as two closed rows of which one is the larger, and is
    /// judged as such (`unequal_rows`: a coercion position accepts it when
    /// the closed side is the actual one).
    fn open_side_extras(
        &mut self,
        r1: &EffectRow,
        r2: &EffectRow,
        open_is_left: bool,
        extras: Vec<super::EffectEntry>,
        common: &[u32],
    ) -> Result<(), Diagnostic> {
        if extras.is_empty() {
            return Ok(());
        }
        match common {
            [] => {
                let left = self.sub.apply_effect_row(r1);
                let right = self.sub.apply_effect_row(r2);
                self.unequal_rows(&left, &right, open_is_left)
            }
            [shared] => {
                let fresh = self.fresh_var();
                self.bind_row_checked(
                    *shared,
                    EffectRow {
                        effects: extras,
                        tails: vec![fresh],
                    },
                )
            }
            _ => Err(ambiguous_row_error(&extras)),
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
                self.bind_row_checked(t, EffectRow::empty())?;
            }
            return Ok(());
        }
        if tails.len() == 1 {
            return self.bind_row_checked(tails[0], EffectRow::closed(extras));
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
            // A where-bound type variable used as a row (`..a` for
            // `a: Trait`, the effects of the impl chosen for `a`) means that
            // only as itself: renaming it to a fresh row variable would
            // leave a row unrelated to `a`. When it has nothing to absorb,
            // bind the other variable to it instead.
            let where_bound = |checker: &Self, id: u32| checker.is_where_bound_var(id);
            if extras1.is_empty() && where_bound(self, t2) && !where_bound(self, t1) {
                return self.bind_row_checked(
                    t1,
                    EffectRow {
                        effects: extras2,
                        tails: vec![Type::Var(t2)],
                    },
                );
            }
            if extras2.is_empty() && where_bound(self, t1) && !where_bound(self, t2) {
                return self.bind_row_checked(
                    t2,
                    EffectRow {
                        effects: extras1,
                        tails: vec![Type::Var(t1)],
                    },
                );
            }
            let fresh = self.fresh_var();
            self.bind_row_checked(
                t1,
                EffectRow {
                    effects: extras2,
                    tails: vec![fresh.clone()],
                },
            )?;
            return self.bind_row_checked(
                t2,
                EffectRow {
                    effects: extras1,
                    tails: vec![fresh],
                },
            );
        }

        // One side has a single tail and the other has several. The single
        // tail can stand for everything the multi-tail side has that it
        // lacks: that side's extra named effects plus the union of its
        // tails. Named effects only the single-tail side has would have to
        // go into one of the other side's tails, and which one is
        // undetermined.
        if tails2.len() == 1 && !tails1.is_empty() {
            if !extras2.is_empty() {
                return Err(ambiguous_row_error(&extras2));
            }
            return self.bind_row_checked(
                tails2[0],
                EffectRow {
                    effects: extras1,
                    tails: tails1.iter().map(|&id| Type::Var(id)).collect(),
                },
            );
        }
        if tails1.len() == 1 && !tails2.is_empty() {
            if !extras1.is_empty() {
                return Err(ambiguous_row_error(&extras1));
            }
            return self.bind_row_checked(
                tails1[0],
                EffectRow {
                    effects: extras2,
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

    /// Whether `id` is (what the substitution has made of) a type variable
    /// under a `where` bound.
    pub(crate) fn is_where_bound_var(&self, id: u32) -> bool {
        let bounds = &self.trait_state.where_bounds;
        bounds.contains_key(&id)
            || bounds
                .keys()
                .any(|bound| self.sub.apply(&Type::Var(*bound)) == Type::Var(id))
    }

    // --- One application per effect family ---

    /// The error for two applications of one effect family meeting in a row.
    pub(crate) fn family_conflict(
        &self,
        first: &super::EffectEntry,
        second: &super::EffectEntry,
    ) -> Diagnostic {
        let family = first.name.rsplit('.').next().unwrap_or(&first.name);
        // Prettify both entries together so shared variables get one name.
        let both = self.prettify_type(&Type::Record(vec![
            (
                "a".to_string(),
                Type::Con(family.to_string(), first.args.clone()),
            ),
            (
                "b".to_string(),
                Type::Con(family.to_string(), second.args.clone()),
            ),
        ]));
        let (a, b) = match both {
            Type::Record(parts) if parts.len() == 2 => {
                (parts[0].1.to_string(), parts[1].1.to_string())
            }
            _ => (family.to_string(), family.to_string()),
        };
        Diagnostic::error(format!(
            "an effect row {FAMILY_CONFLICT_MARKER} `{family}`, but both `{a}` and `{b}` are \
             needed here. An effect is identified by its name, whatever its type arguments, so \
             its operations always reach the nearest `{family}` handler. To use a second \
             instance alongside the first, declare it with `neweffect` (for example \
             `neweffect Other{family} = {b}`) and use that name instead"
        ))
    }

    /// Unify the type arguments of two applications of the same family.
    /// Fails with the family-conflict error.
    pub(crate) fn unify_family(
        &mut self,
        first: &super::EffectEntry,
        second: &super::EffectEntry,
    ) -> Result<(), Diagnostic> {
        if first.args.len() != second.args.len() {
            return Err(self.family_conflict(first, second));
        }
        for (a, b) in first.args.iter().zip(second.args.iter()) {
            if self.unify_step(UnifyStep::EffectArg, a, b).is_err() {
                return Err(self.family_conflict(first, second));
            }
        }
        Ok(())
    }

    /// Apply the substitution to a row and enforce that it holds one
    /// application per family: entries of the same family have their
    /// arguments unified (a mismatch is the family-conflict error), and the
    /// row's entries are recorded against its open tails so a later binding
    /// of a tail cannot bring in a second, different application.
    pub(crate) fn normalize_row(&mut self, row: &EffectRow) -> Result<EffectRow, Diagnostic> {
        if row.is_empty() {
            return Ok(EffectRow::empty());
        }
        let mut applied = self.sub.apply_effect_row(row);
        let mut unified = false;
        for i in 0..applied.effects.len() {
            for j in (i + 1)..applied.effects.len() {
                if applied.effects[i].matches(&applied.effects[j]) {
                    let (first, second) = (applied.effects[i].clone(), applied.effects[j].clone());
                    self.unify_family(&first, &second)?;
                    unified = true;
                }
            }
        }
        if unified {
            // The duplicates are now equal and collapse.
            applied = self.sub.apply_effect_row(&applied);
        }
        if !applied.effects.is_empty() {
            for tail in applied.tail_var_ids() {
                for entry in &applied.effects {
                    self.add_row_companion(tail, entry)?;
                }
            }
        }
        Ok(applied)
    }

    /// `normalize_row`, attaching `span` to a family-conflict error.
    pub(crate) fn normalize_row_at(
        &mut self,
        row: &EffectRow,
        span: Span,
    ) -> Result<EffectRow, Diagnostic> {
        self.normalize_row(row).map_err(|e| e.with_span(span))
    }

    /// Combine two rows into one, unifying the arguments of families both
    /// name.
    pub(crate) fn merge_rows(
        &mut self,
        a: &EffectRow,
        b: &EffectRow,
        span: Span,
    ) -> Result<EffectRow, Diagnostic> {
        let mut combined = a.clone();
        combined.effects.extend(b.effects.iter().cloned());
        for tail in &b.tails {
            if !combined.tails.contains(tail) {
                combined.tails.push(tail.clone());
            }
        }
        self.normalize_row_at(&combined, span)
    }

    /// Record that row variable `var` shares a row with `entry`: whatever
    /// `var` is bound to may contain `entry`'s family only at `entry`'s
    /// arguments.
    pub(crate) fn add_row_companion(
        &mut self,
        var: u32,
        entry: &super::EffectEntry,
    ) -> Result<(), Diagnostic> {
        // A row variable that is also a type variable (`..a` for a
        // where-bound `a`) may have been renamed, or resolved to a type.
        let var = match self.sub.apply(&Type::Var(var)) {
            Type::Var(id) => id,
            _ => return Ok(()),
        };
        if let Some(bound) = self.sub.row_map.get(&var).cloned() {
            // Already bound: check what it was bound to instead.
            for existing in bound.effects.iter().filter(|e| e.matches(entry)) {
                self.unify_family(existing, entry)?;
            }
            for tail in &bound.tails {
                if let Type::Var(id) = self.sub.apply(tail)
                    && id != var
                {
                    self.add_row_companion(id, entry)?;
                }
            }
            return Ok(());
        }
        let resolved = super::EffectEntry {
            name: entry.name.clone(),
            args: entry.args.iter().map(|t| self.sub.apply(t)).collect(),
        };
        let companions = self.sub.row_companions.entry(var).or_default();
        if !companions.iter().any(|c| c.same_instantiation(&resolved)) {
            companions.push(resolved);
        }
        Ok(())
    }

    /// Bind a row variable, enforcing one application per family: the bound
    /// row may name a family the variable shares a row with only at the same
    /// arguments, and the new tails inherit the variable's obligations.
    pub(crate) fn bind_row_checked(&mut self, id: u32, row: EffectRow) -> Result<(), Diagnostic> {
        let companions = self
            .sub
            .row_companions
            .get(&id)
            .cloned()
            .unwrap_or_default();
        let tail_ids: Vec<u32> = row
            .tail_var_ids()
            .into_iter()
            .filter(|tail| *tail != id)
            .collect();
        for companion in &companions {
            let mut named = false;
            for entry in row.effects.iter().filter(|e| e.matches(companion)) {
                named = true;
                self.unify_family(companion, entry)?;
            }
            if !named {
                for &tail in &tail_ids {
                    self.add_row_companion(tail, companion)?;
                }
            }
        }
        for entry in &row.effects {
            for &tail in &tail_ids {
                self.add_row_companion(tail, entry)?;
            }
        }
        self.sub.bind_row(id, row)
    }

    /// The row variables on the arrows of `ty` (following the return spine).
    pub(crate) fn spine_row_tails(&self, ty: &Type) -> Vec<u32> {
        let mut out = Vec::new();
        let mut current = self.sub.apply(ty);
        while let Type::Fun(_, ret, row) = current {
            out.extend(self.sub.apply_effect_row(&row).tail_var_ids());
            current = *ret;
        }
        out
    }

    /// Enforce one application per family on every row in `ty` (see
    /// `normalize_row`).
    pub(crate) fn check_type_rows(&mut self, ty: &Type) -> Result<(), Diagnostic> {
        match ty {
            Type::Fun(a, b, row) => {
                self.check_type_rows(a)?;
                self.check_type_rows(b)?;
                for entry in &row.effects {
                    for arg in &entry.args {
                        self.check_type_rows(arg)?;
                    }
                }
                self.normalize_row(row).map(|_| ())
            }
            Type::Con(_, args) => {
                for arg in args {
                    self.check_type_rows(arg)?;
                }
                Ok(())
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    self.check_type_rows(t)?;
                }
                Ok(())
            }
            Type::Var(_) | Type::Error => Ok(()),
        }
    }

    /// Collect the type variables that appear in an effect's arguments in a
    /// declared type (`e` in `needs {Fail e}` or `Handler (Fail e)`), each
    /// with the family it was written under.
    pub(crate) fn collect_effect_arg_vars(&self, ty: &Type, out: &mut Vec<(u32, String)>) {
        let push_entry = |name: &str, args: &[Type], out: &mut Vec<(u32, String)>| {
            let mut vars = Vec::new();
            for arg in args {
                collect_free_vars(arg, &mut vars);
            }
            for var in vars {
                if !out.iter().any(|(seen, _)| *seen == var) {
                    out.push((var, name.to_string()));
                }
            }
        };
        match ty {
            Type::Fun(a, b, row) => {
                self.collect_effect_arg_vars(a, out);
                self.collect_effect_arg_vars(b, out);
                for entry in &row.effects {
                    push_entry(&entry.name, &entry.args, out);
                    for arg in &entry.args {
                        self.collect_effect_arg_vars(arg, out);
                    }
                }
            }
            Type::Con(name, args) => {
                if name == super::canonicalize_type_name("Handler") {
                    for arg in args {
                        if let Type::Con(effect, effect_args) = arg {
                            push_entry(effect, effect_args, out);
                        }
                    }
                }
                for arg in args {
                    self.collect_effect_arg_vars(arg, out);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    self.collect_effect_arg_vars(t, out);
                }
            }
            Type::Var(_) | Type::Error => {}
        }
    }

    /// A type variable written as an effect's argument in a signature
    /// (`needs {Fail e}`) is chosen by the caller, who handles or performs
    /// the effect at that type. The body must work for every choice: it may
    /// not have pinned the variable to a type, nor merged two of them.
    ///
    /// `names` are the variables the signature's author named. A function
    /// owns its signature, so an argument it left out (`needs {Fail}`) is a
    /// hole its body fills in, and is skipped. A handler arm or an impl
    /// method implements a signature declared elsewhere (the operation's,
    /// the trait method's), which every other user instantiates afresh:
    /// there every variable is the user's choice, written or not
    /// (`all_abstract`).
    pub(crate) fn check_effect_arg_vars_abstract(
        &self,
        vars: &[(u32, String)],
        names: &[(String, u32)],
        all_abstract: bool,
        what: &str,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let name_of = |var: u32| {
            names
                .iter()
                .find(|(_, id)| *id == var)
                .map(|(name, _)| name.clone())
        };
        let mut roots: Vec<(u32, u32, String)> = Vec::new();
        for (var, effect) in vars {
            let name = name_of(*var);
            if name.is_none() && !all_abstract {
                continue;
            }
            let family = effect.rsplit('.').next().unwrap_or(effect).to_string();
            match self.sub.apply(&Type::Var(*var)) {
                Type::Var(root) => {
                    if let Some((_, other, other_family)) =
                        roots.iter().find(|(r, o, _)| *r == root && o != var)
                    {
                        let message = match (name, name_of(*other)) {
                            (Some(a), Some(b)) => format!(
                                "{what} declares the effect argument `{a}` (of `{family}`) and \
                                 `{b}` as independent type variables, but its body only works \
                                 when they are the same type. The caller chooses them; use one \
                                 variable for both in the signature"
                            ),
                            _ => format!(
                                "{what} is declared with independent type variables as effect \
                                 arguments (of `{family}` and of `{other_family}`), but this \
                                 implementation only works when they are the same type. \
                                 Whoever uses it chooses them; use one variable for both in \
                                 the declaration"
                            ),
                        };
                        return Err(Diagnostic::error_at(span, message));
                    }
                    roots.push((root, *var, family));
                }
                Type::Error => {}
                other => {
                    let shown = self.prettify_type(&other);
                    let message = match name {
                        Some(var) => format!(
                            "{what} declares `{family} {var}` for any type `{var}`, but its \
                             body only works when `{var}` is `{shown}`. The caller chooses \
                             `{var}` and performs or handles `{family}` at that type; write \
                             `{shown}` in the signature, or make the body work for every `{var}`"
                        ),
                        None => format!(
                            "{what} is declared with `{family}` at any type, but this \
                             implementation only works when that type is `{shown}`. Whoever \
                             uses it chooses the type and performs or handles `{family}` at \
                             it; write `{shown}` in the declaration, or make the \
                             implementation work for every type"
                        ),
                    };
                    return Err(Diagnostic::error_at(span, message));
                }
            }
        }
        Ok(())
    }

    /// Companion of `check_effect_arg_vars_abstract` for a handler arm or an
    /// impl method: an effect-argument variable of the implemented signature
    /// must not reach what outlives the implementation (`performed`, the
    /// effects it performs outward; `result`, e.g. a handler's answer type).
    /// Every user of the signature chooses that variable afresh, but the
    /// surroundings see one type: it would be pinned there, after this body
    /// was checked.
    pub(crate) fn check_effect_arg_vars_stay_inside(
        &self,
        vars: &[(u32, String)],
        performed: &[super::EffectEntry],
        result: Option<&Type>,
        what: &str,
        span: Span,
    ) -> Result<(), Diagnostic> {
        if vars.is_empty() {
            return Ok(());
        }
        let mut outside = Vec::new();
        for entry in performed {
            for arg in &entry.args {
                collect_free_vars(&self.sub.apply(arg), &mut outside);
            }
        }
        if let Some(ty) = result {
            collect_free_vars(&self.sub.apply(ty), &mut outside);
        }
        for (var, effect) in vars {
            let Type::Var(root) = self.sub.apply(&Type::Var(*var)) else {
                continue;
            };
            if outside.contains(&root) {
                let family = effect.rsplit('.').next().unwrap_or(effect);
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "{what} is declared with `{family}` at any type, but this \
                         implementation passes that type on to its surroundings (in an effect \
                         it performs, or in its result). Whoever uses it chooses the type, each \
                         time, while the surroundings see a single type; handle `{family}` \
                         inside the implementation in a way that works for every type"
                    ),
                ));
            }
        }
        Ok(())
    }

    /// The type variables an instantiated operation signature uses as effect
    /// arguments, each with its family.
    pub(crate) fn op_sig_effect_arg_vars(&self, sig: &super::EffectOpSig) -> Vec<(u32, String)> {
        let mut out = Vec::new();
        for (_, param_ty) in &sig.params {
            self.collect_effect_arg_vars(param_ty, &mut out);
        }
        self.collect_effect_arg_vars(&sig.return_type, &mut out);
        let as_fun = Type::Fun(
            Box::new(Type::unit()),
            Box::new(Type::unit()),
            sig.needs.clone(),
        );
        self.collect_effect_arg_vars(&as_fun, &mut out);
        out
    }

    /// Collect the row variables written in a declared type, with the
    /// effects named next to each. See `Checker::rigid_row_vars`.
    pub(crate) fn collect_rigid_row_vars(
        ty: &Type,
        names: &[(String, u32)],
        out: &mut HashMap<u32, super::RigidRowVar>,
    ) {
        match ty {
            Type::Fun(a, b, row) => {
                Self::collect_rigid_row_vars(a, names, out);
                Self::collect_rigid_row_vars(b, names, out);
                for entry in &row.effects {
                    for arg in &entry.args {
                        Self::collect_rigid_row_vars(arg, names, out);
                    }
                }
                Self::collect_rigid_row_vars_in_row(row, names, out);
            }
            Type::Con(_, args) => {
                for arg in args {
                    Self::collect_rigid_row_vars(arg, names, out);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    Self::collect_rigid_row_vars(t, names, out);
                }
            }
            Type::Var(_) | Type::Error => {}
        }
    }

    pub(crate) fn collect_rigid_row_vars_in_row(
        row: &EffectRow,
        names: &[(String, u32)],
        out: &mut HashMap<u32, super::RigidRowVar>,
    ) {
        for id in row.tail_var_ids() {
            let info = out.entry(id).or_insert_with(|| super::RigidRowVar {
                name: names
                    .iter()
                    .find(|(_, var)| *var == id)
                    .map(|(name, _)| name.clone())
                    .unwrap_or_else(|| "e".to_string()),
                companions: vec![],
            });
            for entry in &row.effects {
                if !info.companions.iter().any(|c| c.same_instantiation(entry)) {
                    info.companions.push(entry.clone());
                }
            }
        }
    }

    /// A row variable written in a signature is chosen by the caller, so the
    /// body may not rely on what it contains. Two things are checked once
    /// the body has been inferred:
    ///
    /// - the variable was not pinned down: it was not unified with a row
    ///   naming a type-parameterised effect, and (unless `allow_closing`) it
    ///   was not closed. It may have been renamed, split into other
    ///   variables, or widened with effects that take no type argument
    ///   (which is how a callback is passed where more effects are allowed);
    /// - the body did not put it in a row with a type-parameterised effect
    ///   that the signature does not name next to it. `{State Int, ..e}`
    ///   means "if `e` contains `State`, it is `State Int`", which is only
    ///   true if callers are held to it by the signature.
    ///
    /// `what` names the declaration for the error.
    ///
    /// `allow_closing` is for handler arms. An arm may hand an operation's
    /// callback on to something that accepts fewer effects, which closes the
    /// callback's row variable; the callback still finds the effects of that
    /// row at the place the operation was performed (see "Effect-Operation
    /// Callbacks With Open Tails" in `docs/effect-implementation.md`), not
    /// at whatever the arm installs around it.
    pub(crate) fn check_rigid_row_vars_abstract(
        &mut self,
        rigid: &HashMap<u32, super::RigidRowVar>,
        what: &str,
        span: Span,
        allow_closing: bool,
    ) -> Result<(), Diagnostic> {
        let mut vars: Vec<(u32, super::RigidRowVar)> =
            rigid.iter().map(|(id, info)| (*id, info.clone())).collect();
        vars.sort_by_key(|(id, _)| *id);
        for (var, info) in vars {
            let resolved = self.sub.apply_effect_row(&EffectRow {
                effects: vec![],
                tails: vec![Type::Var(var)],
            });
            let pinned: Vec<super::EffectEntry> = resolved
                .effects
                .iter()
                .filter(|entry| {
                    self.effects
                        .get(&entry.name)
                        .is_some_and(|info| !info.type_params.is_empty())
                })
                .cloned()
                .collect();
            let closed = resolved.tails.is_empty() && !allow_closing;
            if !pinned.is_empty() || closed {
                let (required, fix) = if pinned.is_empty() && resolved.effects.is_empty() {
                    (
                        "to be empty".to_string(),
                        format!("remove `..{}` from the signature", info.name),
                    )
                } else if pinned.is_empty() {
                    (
                        format!("to be exactly {}", self.describe_effects(&resolved.effects)),
                        format!("remove `..{}` from the signature", info.name),
                    )
                } else {
                    let effects = self.describe_effects(&pinned);
                    let inner = effects.trim_start_matches('{').trim_end_matches('}');
                    (
                        format!("to contain {effects}"),
                        format!(
                            "name them where `..{name}` is written (`needs {{{inner}, ..{name}}}`)",
                            name = info.name
                        ),
                    )
                };
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "{what} declares the open effect row `..{name}`, but its body requires \
                         that row {required}. A row variable in a signature is chosen by the \
                         caller, so the body cannot rely on what it contains; {fix}",
                        name = info.name,
                    ),
                ));
            }

            for root in resolved.tail_var_ids() {
                let declared = self
                    .rigid_row_var_for(root)
                    .map(|r| r.companions)
                    .unwrap_or_default();
                let assumed = self
                    .sub
                    .row_companions
                    .get(&root)
                    .cloned()
                    .unwrap_or_default();
                for companion in assumed {
                    let parameterised = self
                        .effects
                        .get(&companion.name)
                        .is_some_and(|e| !e.type_params.is_empty());
                    if !parameterised {
                        continue;
                    }
                    let mut covered = false;
                    for decl in declared.iter().filter(|d| d.matches(&companion)) {
                        let saved = self.sub.clone();
                        if self.unify_family(decl, &companion).is_ok() {
                            covered = true;
                            break;
                        }
                        self.sub = saved;
                    }
                    if covered {
                        continue;
                    }
                    let family = companion.name.rsplit('.').next().unwrap_or(&companion.name);
                    let shown = self.prettify_effect_entry(&companion);
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "{what} declares the open effect row `..{name}`, and its body uses \
                             `..{name}` together with `{shown}`. The caller chooses `..{name}`, \
                             and it might contain `{family}` at another type; its operations \
                             would then be treated as `{shown}`. Say so in the signature by \
                             naming the effect where `..{name}` is written (`needs {{{shown}, \
                             ..{name}}}`), or keep the two apart with a `neweffect`",
                            name = info.name,
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    /// A row variable about to be generalised loses what the substitution
    /// knows about it, so anything it must stay consistent with has to be
    /// visible in the type itself. Returns a type-parameterised effect that
    /// `var` shares a row with somewhere, but that no row of `ty` names next
    /// to `var`.
    pub(crate) fn unexpressed_row_companion(
        &mut self,
        ty: &Type,
        var: u32,
    ) -> Option<super::EffectEntry> {
        let assumed = self.sub.row_companions.get(&var).cloned()?;
        let resolved = self.sub.apply(ty);
        let mut structural = HashMap::new();
        Self::collect_rigid_row_vars(&resolved, &[], &mut structural);
        let named = structural
            .remove(&var)
            .map(|info| info.companions)
            .unwrap_or_default();
        for companion in assumed {
            let parameterised = self
                .effects
                .get(&companion.name)
                .is_some_and(|e| !e.type_params.is_empty());
            if !parameterised {
                continue;
            }
            let mut covered = false;
            for decl in named.iter().filter(|d| d.matches(&companion)) {
                let saved = self.sub.clone();
                if self.unify_family(decl, &companion).is_ok() {
                    covered = true;
                    break;
                }
                self.sub = saved;
            }
            if !covered {
                return Some(companion);
            }
        }
        None
    }

    /// Record the entries of every open row in `ty` against its tails (see
    /// `add_row_companion`). Used on freshly instantiated types, whose rows
    /// may have a tail bound before the row itself is next unified.
    pub(crate) fn register_open_rows(&mut self, ty: &Type) {
        match ty {
            Type::Fun(a, b, row) => {
                self.register_open_rows(a);
                self.register_open_rows(b);
                for entry in &row.effects {
                    for arg in &entry.args {
                        self.register_open_rows(arg);
                    }
                }
                if !row.effects.is_empty() && !row.tails.is_empty() {
                    // A conflict here would be inside the type itself; it is
                    // reported when the row is next unified.
                    let _ = self.normalize_row(row);
                }
            }
            Type::Con(_, args) => {
                for arg in args {
                    self.register_open_rows(arg);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    self.register_open_rows(t);
                }
            }
            Type::Var(_) | Type::Error => {}
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
    ///
    /// This is the entry point for positions that are *not* coercion
    /// positions: unequal closed effect rows are a type error here.
    pub(crate) fn unify_at(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), Diagnostic> {
        self.unify_in_position(a, b, span, RowPosition::Exact)
    }

    /// Unify two types that already sit inside a larger type (see
    /// `RowPosition::Nested`).
    pub(crate) fn unify_nested_at(
        &mut self,
        a: &Type,
        b: &Type,
        span: Span,
    ) -> Result<(), Diagnostic> {
        self.unify_in_position(a, b, span, RowPosition::Nested)
    }

    /// Unify at a coercion position: a value of type `actual` (produced by
    /// `expr`, when there is one) is used where `expected` is wanted. Same
    /// unification as `unify_at(actual, expected, span)`; only the judgement
    /// of unequal closed effect rows differs.
    pub(crate) fn coerce_at(
        &mut self,
        actual: &Type,
        expected: &Type,
        span: Span,
        expr: Option<&Expr>,
    ) -> Result<(), Diagnostic> {
        self.unify_in_position(
            actual,
            expected,
            span,
            RowPosition::Coercion {
                actual_is_left: true,
                expr,
            },
        )
    }

    /// `coerce_at` for call sites that unify as `(expected, actual)`. The
    /// argument order is kept because it decides which side a type variable
    /// is bound from and how mismatch errors read.
    pub(crate) fn coerce_expected_first_at(
        &mut self,
        expected: &Type,
        actual: &Type,
        span: Span,
        expr: Option<&Expr>,
    ) -> Result<(), Diagnostic> {
        self.unify_in_position(
            expected,
            actual,
            span,
            RowPosition::Coercion {
                actual_is_left: false,
                expr,
            },
        )
    }

    fn unify_in_position(
        &mut self,
        a: &Type,
        b: &Type,
        span: Span,
        position: RowPosition<'_>,
    ) -> Result<(), Diagnostic> {
        self.unify_path.clear();
        let mode = match position {
            RowPosition::Exact => RowMode::Exact,
            RowPosition::Nested => RowMode::Nested,
            RowPosition::Coercion {
                actual_is_left,
                expr,
            } => RowMode::Coercion {
                actual_is_left,
                shape: DirectShape::of(expr),
            },
        };
        let saved = std::mem::replace(&mut self.row_mode, mode);
        let result = self.unify_rec(a, b);
        self.row_mode = saved;
        result.map_err(|e| e.with_span(span))
    }

    /// Whether the rows being unified sit at a coercion position directly
    /// (on the coerced value's own arrows, see `DirectShape::is_direct`), and
    /// if so whether the actual type is the left one.
    fn direct_coercion(&self) -> Option<bool> {
        match &self.row_mode {
            RowMode::Coercion {
                actual_is_left,
                shape,
            } if shape.is_direct(&self.unify_path) => Some(*actual_is_left),
            _ => None,
        }
    }

    /// Two rows that differ only in that one has named effects the other
    /// lacks (`left_is_larger` says which), after any open tails have been
    /// bound. Without a position (`unify`) this is accepted either way. At a
    /// coercion position, directly, the actual row may be the smaller one;
    /// everywhere else the rows must be equal.
    fn unequal_rows(
        &self,
        left: &EffectRow,
        right: &EffectRow,
        left_is_larger: bool,
    ) -> Result<(), Diagnostic> {
        let subsumption = RowSubsumption {
            path: self.unify_path.clone(),
            left: left.clone(),
            right: right.clone(),
            left_is_larger,
        };
        let message = match &self.row_mode {
            RowMode::Lenient => None,
            RowMode::Coercion { .. } => match self.direct_coercion() {
                Some(actual_is_left) => self.coercion_error(&subsumption, actual_is_left),
                None => Some(self.strict_row_error(&subsumption, false)),
            },
            RowMode::Exact => Some(self.strict_row_error(&subsumption, true)),
            RowMode::Nested => Some(self.strict_row_error(&subsumption, false)),
        };
        match message {
            Some(message) => Err(Diagnostic::error(message)),
            None => Ok(()),
        }
    }

    /// Error for unequal closed rows where no subsumption is
    /// allowed at all: inside a type-constructor argument, a function
    /// parameter, an anonymous-record field or an effect's type argument
    /// ("at depth": no variance tracking, so either direction is wrong), or
    /// directly at a position that is not a coercion position.
    fn strict_row_error(&self, subsumption: &RowSubsumption, exact: bool) -> String {
        let (larger, smaller) = if subsumption.left_is_larger {
            (&subsumption.left, &subsumption.right)
        } else {
            (&subsumption.right, &subsumption.left)
        };
        let returns_only = subsumption
            .path
            .iter()
            .all(|step| *step == UnifyStep::FunRet);
        if exact && returns_only {
            format!(
                "{}function types with different effect rows ({} and {}) cannot be used as \
                 the same type here. Effects may only be added implicitly where a value is \
                 passed, returned, annotated or placed in a literal; make both function types \
                 declare the same `needs` row.",
                ROW_RULE_MARKER,
                self.describe_row(larger),
                self.describe_row(smaller),
            )
        } else {
            format!(
                "{}function types with different effect rows ({} and {}) cannot be used as \
                 the same type inside a larger type. Effect rows nested in a type argument, a \
                 function parameter or a record field must be identical; make both function \
                 types declare the same `needs` row.",
                ROW_RULE_MARKER,
                self.describe_row(larger),
                self.describe_row(smaller),
            )
        }
    }

    /// Error for one arrow of a function value at a coercion position.
    ///
    /// The actual row may have fewer effects than the expected row
    /// (subsumption). The reverse is an effectful function used as a less
    /// effectful one, and is reported. Rows are compared arrow by arrow: an
    /// effect on a different arrow of a curried type is performed at a
    /// different application, so `fun a -> { e! (); fun b -> .. }` is not an
    /// `A -> B -> C needs {E}`.
    fn coercion_error(&self, subsumption: &RowSubsumption, actual_is_left: bool) -> Option<String> {
        if subsumption.left_is_larger != actual_is_left {
            return None;
        }
        let (actual, expected) = if actual_is_left {
            (&subsumption.left, &subsumption.right)
        } else {
            (&subsumption.right, &subsumption.left)
        };
        let unexpected: Vec<super::EffectEntry> = actual
            .effects
            .iter()
            .filter(|e| !expected.effects.iter().any(|x| x.matches(e)))
            .cloned()
            .collect();
        let unexpected = self.describe_effects(&unexpected);
        let expected = if expected.effects.is_empty() {
            "a function with no effects is expected".to_string()
        } else {
            format!(
                "a function that only allows {} is expected",
                self.describe_effects(&expected.effects)
            )
        };
        Some(format!(
            "{}a function that uses {} is used where {}. Handle {} first \
             (for example `fun x -> f x with handler`), or add `needs {}` to the \
             expected function type.",
            ROW_RULE_MARKER,
            self.describe_effects(&actual.effects),
            expected,
            unexpected,
            unexpected,
        ))
    }

    fn describe_effects(&self, effects: &[super::EffectEntry]) -> String {
        let mut names: Vec<String> = effects
            .iter()
            .map(|e| self.prettify_effect_entry(e))
            .collect();
        names.sort();
        format!("{{{}}}", names.join(", "))
    }

    fn describe_row(&self, row: &EffectRow) -> String {
        if row.effects.is_empty() {
            "no effects".to_string()
        } else {
            self.describe_effects(&row.effects)
        }
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
            .map(|&id| (id, self.fresh_var()))
            .collect();
        let ty = Self::replace_vars(&scheme.ty, &mapping);
        if !mapping.is_empty() {
            self.register_open_rows(&ty);
        }
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
    pub(crate) fn convert_type_expr(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
    ) -> Type {
        let ty = self.convert_type_expr_inner(texpr, params);
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
            Type::Var(_) | Type::Error => {}
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
    /// kind `expected_kind`. Kind infrastructure is retained, but since `Kind`
    /// now has only `Star` no mismatch is currently possible.
    pub(crate) fn convert_type_expr_inner(
        &mut self,
        texpr: &crate::ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
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
                    // Only seed `params` if the binding came from the outer
                    // scope — keeps the local list consistent for callers
                    // that scan it after conversion.
                    if !params.iter().any(|(n, _)| n == name) {
                        params.push((name.clone(), id));
                    }
                    Type::Var(id)
                } else {
                    // New type variable -- create fresh and remember for reuse.
                    let id = self.next_var;
                    self.next_var += 1;
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            }
            crate::ast::TypeExpr::App { func, arg, .. } => {
                let func_ty = self.convert_type_expr_inner(func, params);
                let arg_ty = self.convert_type_expr_inner(arg, params);
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
                let a_ty = self.convert_type_expr_inner(from, params);
                let b_ty = self.convert_type_expr_inner(to, params);
                {
                    let mut effect_refs: Vec<super::EffectEntry> = Vec::new();
                    for e in effects {
                        let entry = {
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
                        };
                        if let Err(err) = self.push_declared_effect(&mut effect_refs, entry, e.span)
                        {
                            self.collected_diagnostics.push(err);
                        }
                    }
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
                let mut typed_fields: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(fname, texpr)| {
                        (fname.clone(), self.convert_type_expr_inner(texpr, params))
                    })
                    .collect();
                typed_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Type::Record(typed_fields)
            }
            crate::ast::TypeExpr::Labeled { inner, .. } => {
                self.convert_type_expr_inner(inner, params)
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
                            Type::Con(effect_name, effect_args) => {
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
