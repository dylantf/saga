use super::*;

/// The unqualified base of a (possibly `Mod.Sub.`-qualified) name. Constructor
/// names enter the fold from two sources that disagree on qualification: the
/// `Generic.to` builder writes fully-qualified `Std.Generic.Adt`, while impl
/// patterns carry the name as the user wrote it (`Adt`). Cancellation compares
/// on the base so the two meet.
pub(crate) fn base_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// If `expr` is a saturated data-constructor application `Con a1 … an`, return
/// the constructor name and its arguments in source order. `None` otherwise.
pub(crate) fn known_ctor(expr: &Expr) -> Option<(&str, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg } => {
                args.push(arg.as_ref());
                current = func;
            }
            ExprKind::Constructor { name } => {
                args.reverse();
                return Some((name.as_str(), args));
            }
            _ => return None,
        }
    }
}

/// `case Con(args) of { … }` where the scrutinee is *any* known constructor:
/// select the matching arm and bind its sub-patterns to `args`, dropping the
/// other arms. Returns `None` when the scrutinee isn't a known constructor or the
/// match can't be decided statically (a guard on a matching arm, or an
/// undecidable pattern shape) — in which case the case is left intact.
///
/// Fires on any constructor (`Ok`/`Err`, user ADTs, …). It is sound and bounded
/// because it only matches a scrutinee that is a *literal* constructor
/// application — a shape that arises from the fold's own inlining/commuting, not
/// from ordinary source.
/// Project a field out of a compile-time-constant record literal:
/// `(Options { rename_all: AsIs, … }).rename_all` ⟶ `AsIs`. This is what makes a
/// constant `opts` argument, once substituted into an inlined codec body, fold to
/// the literal field value — exposing e.g. `case opts.tag_format of { … }` as a
/// `case <known ctor> of { … }` that [`case_of_known_constructor`] then collapses.
///
/// Handles `RecordUpdate` by returning the updated field if present, else
/// re-projecting through the base record. Gated on the whole record being
/// [`is_duplicable`]: projecting one field discards the sibling field exprs, which
/// is only sound when those siblings are pure (no dropped effects). A non-pure
/// record is left as a `FieldAccess` for lowering, unchanged from today.
pub(crate) fn project_record_field(expr: &Expr) -> Option<Expr> {
    let ExprKind::FieldAccess {
        expr: inner, field, ..
    } = &expr.kind
    else {
        return None;
    };
    if !is_duplicable(inner) {
        return None;
    }
    match &inner.kind {
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => fields
            .iter()
            .find(|(name, _, _)| name == field)
            .map(|(_, _, value)| value.clone()),
        ExprKind::RecordUpdate { record, fields, .. } => {
            if let Some((_, _, value)) = fields.iter().find(|(name, _, _)| name == field) {
                Some(value.clone())
            } else {
                // Field not overridden by the update — project through the base.
                Some(Expr::synth(
                    expr.span,
                    ExprKind::FieldAccess {
                        expr: record.clone(),
                        field: field.clone(),
                        record_name: None,
                    },
                ))
            }
        }
        _ => None,
    }
}

pub(crate) fn case_of_known_constructor(expr: &Expr) -> Option<Expr> {
    let ExprKind::Case {
        scrutinee, arms, ..
    } = &expr.kind
    else {
        return None;
    };
    known_ctor(scrutinee)?; // bail unless the scrutinee is a known constructor

    for ann in arms {
        let arm = &ann.node;
        match static_match(&arm.pattern, scrutinee) {
            // Definitely doesn't match — skip to the next arm.
            Match::No => continue,
            // Can't decide this arm statically (e.g. a nested constructor against
            // a non-literal sub-value): we can't safely pick *or* skip it, so
            // leave the whole case for a later round once more is known.
            Match::Unknown => return None,
            // Definitely matches. A guard could still fail at runtime, so only
            // commit when there's none.
            Match::Yes => {
                if arm.guard.is_some() {
                    return None;
                }
                return Some(commit_matched_arm(&arm.pattern, scrutinee, &arm.body));
            }
        }
    }
    None
}

/// True if `body`'s result `case` would statically commit to one arm when its
/// scrutinee parameter `param` is known to be the nullary constructor `ctor_name`.
/// This is the "will inlining this function immediately collapse?" gate for
/// [`Folder::try_inline_fun`] — it mirrors the arm-scan in
/// [`case_of_known_constructor`] over a synthetic `ctor_name` value.
pub(crate) fn body_cancels_with(param: &str, ctor_name: &str, body: &Expr) -> bool {
    let ExprKind::Case {
        scrutinee, arms, ..
    } = &result_expr(body).kind
    else {
        return false;
    };
    let ExprKind::Var { name } = &scrutinee.kind else {
        return false;
    };
    if name != param {
        return false;
    }
    let synthetic = Expr::synth(
        scrutinee.span,
        ExprKind::Constructor {
            name: ctor_name.to_string(),
        },
    );
    decides_against(arms, &synthetic)
}

/// True if a `case` over the known constructor `value` statically commits to one
/// arm (some arm `static_match`es `Yes` with no guard, and no earlier arm is
/// `Unknown`). The bool half of [`case_of_known_constructor`]'s arm scan.
pub(crate) fn decides_against(arms: &[Annotated<CaseArm>], value: &Expr) -> bool {
    for ann in arms {
        match static_match(&ann.node.pattern, value) {
            Match::No => continue,
            Match::Unknown => return false,
            Match::Yes => return ann.node.guard.is_none(),
        }
    }
    false
}

/// Result of statically deciding whether `pat` matches a (partially) known value.
pub(crate) enum Match {
    Yes,
    No,
    Unknown,
}

/// Decide whether `pat` matches `value`, recursing through nested constructors.
/// A multi-variant `Generic.from` has several arms sharing an outer constructor
/// (`Adt _ (Or_Left …)`, `Adt _ (Or_Right …)`, …), so deciding on the outer
/// constructor alone would wrongly commit to the first; the recursion routes each
/// `Or` branch to the correct arm.
pub(crate) fn static_match(pat: &Pat, value: &Expr) -> Match {
    match pat {
        // Irrefutable binders always match.
        Pat::Wildcard { .. } | Pat::Var { .. } => Match::Yes,
        Pat::Constructor { name, args, .. } => {
            let Some((cname, cargs)) = known_ctor(value) else {
                return Match::Unknown; // value isn't a literal ctor — can't decide
            };
            if base_name(cname) != base_name(name) || cargs.len() != args.len() {
                return Match::No;
            }
            let mut result = Match::Yes;
            for (subpat, subval) in args.iter().zip(&cargs) {
                match static_match(subpat, subval) {
                    Match::No => return Match::No,
                    Match::Unknown => result = Match::Unknown,
                    Match::Yes => {}
                }
            }
            result
        }
        Pat::Lit { value: litpat, .. } => match &value.kind {
            ExprKind::Lit { value: litval, .. } => {
                if litval == litpat {
                    Match::Yes
                } else {
                    Match::No
                }
            }
            _ => Match::Unknown,
        },
        // Tuple/record/etc. against a constructor value: don't try to decide.
        _ => Match::Unknown,
    }
}

/// Bind a definitely-matching arm's pattern against the known scrutinee value and
/// return the rewritten arm body. The pattern's match was already confirmed
/// `Match::Yes` by [`static_match`].
pub(crate) fn commit_matched_arm(pat: &Pat, scrutinee: &Expr, body: &Expr) -> Expr {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } => body.clone(),
        Pat::Var { name, .. } => {
            let mut body = body.clone();
            substitute_var(&mut body, name, scrutinee);
            body
        }
        Pat::Constructor { args: subpats, .. } => {
            // `static_match` Yes ⇒ the scrutinee is the matching ctor.
            let (_, cargs) = known_ctor(scrutinee).expect("matched arm has known ctor scrutinee");
            bind_subpats(subpats, &cargs, body)
        }
        _ => body.clone(),
    }
}

/// Bind a constructor pattern's sub-patterns to the scrutinee's arguments in the
/// arm body. `subpats[i]` binds `cargs[i]`:
///
/// - A `Var` sub-pattern bound to a **duplicable** (pure, cheap) argument is
///   substituted, so a known-constructor argument stays syntactically visible
///   for further cancellation. A non-duplicable argument is let-bound instead
///   (single-arm `case`), so a possibly-effectful argument runs exactly once.
/// - A `Wildcard` bound to a duplicable argument is dropped; a non-duplicable
///   one is let-bound (its effects still run, its value discarded).
/// - A nested constructor sub-pattern becomes a single-arm `case` (which
///   `case_of_known_constructor` can then collapse in turn).
///
/// This matches the effect semantics of the original `case arg of pat -> body`
/// β-reduction: every argument is evaluated exactly once, in order.
pub(crate) fn bind_subpats(subpats: &[Pat], cargs: &[&Expr], body: &Expr) -> Expr {
    let mut result = body.clone();
    for (subpat, carg) in subpats.iter().zip(cargs).rev() {
        match subpat {
            Pat::Wildcard { .. } if is_duplicable(carg) => {}
            Pat::Var { name, .. } if is_duplicable(carg) => substitute_var(&mut result, name, carg),
            _ => {
                let mut scrut = (*carg).clone();
                freshen_expr_ids(&mut scrut);
                result = Expr::synth(
                    body.span,
                    ExprKind::Case {
                        scrutinee: Box::new(scrut),
                        arms: vec![Annotated::bare(CaseArm {
                            pattern: clone_fresh_pat(subpat),
                            guard: None,
                            body: result,
                            span: body.span,
                        })],
                        dangling_trivia: vec![],
                    },
                );
            }
        }
    }
    result
}

/// True for expressions that are pure and cheap enough to substitute inline
/// (possibly at several use sites) without changing evaluation effects or
/// duplicating significant work. Substituting a non-duplicable argument could
/// re-run its effects or discard them, so those are let-bound instead. `to`'s
/// `Rep` trees — built from field accesses, literals, and constructor
/// applications — are duplicable, which is what lets fusion proceed.
pub(crate) fn is_duplicable(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Var { .. }
        | ExprKind::Lit { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. } => true,
        ExprKind::FieldAccess { expr: inner, .. } | ExprKind::Ascription { expr: inner, .. } => {
            is_duplicable(inner)
        }
        ExprKind::Tuple { elements } => elements.iter().all(is_duplicable),
        // A record literal is a pure build (it lowers to a tagged tuple), the exact
        // analogue of a saturated data-constructor application below — duplicable
        // when every field value is. This lets a constant `Options { … }` argument
        // substitute inline rather than be hidden behind a `bind_subpats` case-bound
        // `Var`, which is what lets `project_record_field` see it.
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            fields.iter().all(|(_, _, v)| is_duplicable(v))
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            is_duplicable(record) && fields.iter().all(|(_, _, v)| is_duplicable(v))
        }
        // A saturated data-constructor application is a pure build; allow it when
        // every argument is duplicable. A non-constructor application (a function
        // call) may be effectful, so `known_ctor` returning `None` rejects it.
        ExprKind::App { .. } => {
            known_ctor(expr).is_some_and(|(_, args)| args.iter().all(|a| is_duplicable(a)))
        }
        _ => false,
    }
}

pub(crate) fn clone_fresh_pat(pat: &Pat) -> Pat {
    let mut p = pat.clone();
    freshen_pat_ids(&mut p);
    p
}

/// Peel a chain of `App` nodes, returning the innermost non-`App` head and the
/// applied arguments in source order.
/// β-reduce a saturated application of a *literal* lambda:
/// `(fun p… -> body)(a…)` ⟶ `body` with each `p` bound to its `a`.
///
/// Reuses [`bind_subpats`]: each duplicable argument is substituted inline. The
/// substitution is capture-avoiding ([`substitute_var`]) and the lambda body
/// keeps its NodeIds (the node appears once and is replaced in place, never
/// duplicated), so resolution entries stay valid.
///
/// **Only fires when every argument is [`is_duplicable`]** (pure: vars, literals,
/// constructors, field accesses). This is the soundness boundary, not just a
/// heuristic: a non-duplicable arg (a callback lambda, an effectful call) would
/// be `bind_subpats`-freshened into a `case` scrutinee, and freshening orphans
/// the NodeId-keyed effect-operation resolution computed upstream — so reducing
/// `(fun f -> f ())(fun () -> log! "x")` would lose the `log!` evidence. Pure
/// args carry no such state, and substituting them (even at several use sites)
/// duplicates no effects.
///
/// Fires only on full saturation (`params.len() == args.len()`): a partial
/// application is a closure and must stay un-reduced, and an over-application
/// (`params.len() < args.len()`) means the lambda returns a function — leave it
/// for a later pass.
///
/// Note this runs as part of the generic fold, which short-circuits in a module
/// with **no dict constructors** ([`fold_program`]'s `ctors.is_empty()` guard):
/// the fusible shapes all arise from inlined dict-method bodies, so a module
/// with no dictionaries has nothing for this pass to do.
pub(crate) fn beta_reduce_lambda_app(expr: &Expr) -> Option<Expr> {
    let (head, args) = peel_app(expr);
    let ExprKind::Lambda { params, body } = &head.kind else {
        return None;
    };
    if params.is_empty() || params.len() != args.len() {
        return None;
    }
    if !args.iter().all(|a| is_duplicable(a)) {
        return None;
    }
    Some(bind_subpats(params, &args, body))
}

pub(crate) fn peel_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}
