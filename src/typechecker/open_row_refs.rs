//! Open-row trait methods used as function values.
//!
//! A trait method declared with an open row (`fun decode : a -> Int needs
//! {..e}`) performs whatever the selected impl performs. When the method is
//! applied to all its arguments, the call site adds those effects
//! (`emit_concrete_trait_impl_effects`). When it is only *referenced*
//! (`apply decode x`, `pick () = decode`, `Box { run: decode }`, a partial
//! application), nothing is performed yet: the effects belong on the arrow of
//! the value, and the impl is often not known until the reference has been
//! unified with its context.
//!
//! Each such reference is recorded here with the row variable its arrow
//! carries. Once the constrained type is known, that row is required to
//! contain the impl's effects. If the type is still a variable when the
//! enclosing scope ends (the dictionary comes from a `where` bound, or the
//! binding is generalised), the row becomes `..a`, the same forwarding form a
//! call uses.
//!
//! The same applies to a function whose own row is `..a` for a where-bound
//! `a` (`fun use : a -> Int needs {..a} where {a: Decode}`) when it is
//! referenced without being fully applied.

use super::*;
use crate::ast::NodeId;

/// One reference to an open-row trait method (or a function forwarding one)
/// used as a value.
#[derive(Debug, Clone)]
pub(crate) struct OpenRowRef {
    pub trait_name: String,
    /// The constrained type: the impl is selected by what this resolves to.
    pub self_ty: Type,
    /// The method, when the reference names it directly; `None` for a
    /// function with a where bound, which may call any of the trait's
    /// open-row methods.
    pub method: Option<String>,
    /// Row variables on the value's arrows that stand for the impl's effects.
    pub tails: Vec<u32>,
    /// The name as written, for diagnostics.
    pub display: String,
    pub span: Span,
}

/// What to do with references whose constrained type is still a variable.
#[derive(Clone, Copy)]
pub(crate) enum OpenRowFinish<'a> {
    /// Keep them: later unification may still decide the impl.
    Keep,
    /// These variables are about to be generalised by a `let`; a reference
    /// constrained by one of them forwards `..a`.
    Generalized(&'a [u32]),
    /// The enclosing declaration is done; every remaining reference forwards
    /// `..a`. `forward` records the variable so the declaration must name it
    /// in its own row (`check_fun_clauses`).
    Scope { forward: bool },
}

fn arrow_count(ty: &Type) -> usize {
    let mut n = 0;
    let mut current = ty;
    while let Type::Fun(_, ret, _) = current {
        n += 1;
        current = ret;
    }
    n
}

/// Replace `..from` in the rows of `ty` with `..to`. Returns whether any row
/// had that tail.
fn replace_row_tail(ty: &Type, from: u32, to: &Type, found: &mut bool) -> Type {
    match ty {
        Type::Fun(a, b, row) => {
            let effects = row
                .effects
                .iter()
                .map(|entry| EffectEntry {
                    name: entry.name.clone(),
                    args: entry
                        .args
                        .iter()
                        .map(|arg| replace_row_tail(arg, from, to, found))
                        .collect(),
                })
                .collect();
            let tails = row
                .tails
                .iter()
                .map(|tail| {
                    if *tail == Type::Var(from) {
                        *found = true;
                        to.clone()
                    } else {
                        tail.clone()
                    }
                })
                .collect();
            Type::Fun(
                Box::new(replace_row_tail(a, from, to, found)),
                Box::new(replace_row_tail(b, from, to, found)),
                EffectRow { effects, tails },
            )
        }
        Type::Con(name, args) => Type::Con(
            name.clone(),
            args.iter()
                .map(|arg| replace_row_tail(arg, from, to, found))
                .collect(),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(label, t)| (label.clone(), replace_row_tail(t, from, to, found)))
                .collect(),
        ),
        Type::Var(_) | Type::Error => ty.clone(),
    }
}

impl Checker {
    /// Called where a name's scheme has just been instantiated to `ty` with
    /// `constraints`. Records the reference if its arrows carry an open-row
    /// trait method's effects and it is not a call that supplies every
    /// argument (those are handled at the call). May return a rewritten type.
    pub(crate) fn note_open_row_reference(
        &mut self,
        name: &str,
        ty: Type,
        constraints: &[(String, Type, Vec<Type>)],
        span: Span,
        node_id: NodeId,
    ) -> Type {
        if constraints.is_empty() {
            return ty;
        }
        let applied_args = match self.call_head {
            Some((head, args)) if head == node_id => Some(args),
            _ => None,
        };
        if applied_args.is_some_and(|args| args >= arrow_count(&ty)) {
            return ty;
        }
        let bare = name.rsplit('.').next().unwrap_or(name);
        let mut ty = ty;
        for (trait_name, self_ty, extra) in constraints {
            // Multi-parameter traits are not resolved here (nor at calls).
            if !extra.is_empty() {
                continue;
            }
            let Type::Var(self_var) = self_ty else {
                continue;
            };
            let Some(info) = self.trait_state.traits.get(trait_name) else {
                continue;
            };
            if !info.methods.iter().any(|m| m.effect_sig.is_open_row) {
                continue;
            }
            let method = info.methods.iter().find(|m| m.name == bare);
            let (method, tails) = match method {
                Some(m) if m.effect_sig.is_open_row => {
                    let tails = super::check_decl::innermost_effect_row(&ty)
                        .map(|row| row.tail_var_ids())
                        .unwrap_or_default();
                    (Some(m.name.clone()), tails)
                }
                // A pure or closed sibling: its row is its declared type.
                Some(_) => continue,
                None => {
                    // A function that forwards the trait's row as `..a`.
                    let fresh = self.fresh_var();
                    let mut found = false;
                    let rewritten = replace_row_tail(&ty, *self_var, &fresh, &mut found);
                    if !found {
                        continue;
                    }
                    ty = rewritten;
                    let Type::Var(fresh_id) = fresh else {
                        unreachable!("fresh_var returns a variable")
                    };
                    (None, vec![fresh_id])
                }
            };
            if tails.is_empty() {
                continue;
            }
            self.trait_state.open_row_refs.push(OpenRowRef {
                trait_name: trait_name.clone(),
                self_ty: self_ty.clone(),
                method,
                tails,
                display: bare.to_string(),
                span,
            });
        }
        ty
    }

    /// The effects the impl of `trait_name` for the type `type_name`
    /// performs through open-row methods: those of `method` when it names a
    /// method of the trait, else the union over the trait's open-row
    /// methods. `None` when there is nothing to add (no such impl, no
    /// open-row method, or `method` is not open-row).
    pub(crate) fn open_row_impl_effects(
        &self,
        trait_name: &str,
        type_name: &str,
        arity: usize,
        method: Option<&str>,
    ) -> Option<Vec<EffectEntry>> {
        // Single-param trait lookup: arity-keyed target first (tuples),
        // then the bare canonical name. Multi-param traits (non-empty
        // trait_type_args) are not handled here yet.
        let arity_key = super::arity_keyed_target_name(type_name, arity);
        let info = self
            .trait_state
            .impls
            .get(&(trait_name.to_string(), vec![], arity_key))
            .or_else(|| {
                self.trait_state
                    .impls
                    .get(&(trait_name.to_string(), vec![], type_name.to_string()))
            })?;
        if info.method_effects.is_empty() {
            return None;
        }
        // Only *open-row* trait methods need this. Their effects are NOT in
        // the method's declared type, so the normal row-tracking never sees
        // them. A closed-named method (`to_json : a -> Json needs
        // {JsonOptions}`) already carries its effect in the type: it
        // propagates -- and gets subtracted by an enclosing handler --
        // through the normal path. Re-emitting it would resurrect an effect
        // the callee already handled (e.g. `serialize x = serialize_with x
        // with json_defaults`, where `serialize` is pure but PersonD's
        // `ToJson` impl performs `JsonOptions`).
        let open_row_methods: HashSet<&str> = self
            .trait_state
            .traits
            .get(trait_name)
            .map(|t| {
                t.methods
                    .iter()
                    .filter(|m| m.effect_sig.is_open_row)
                    .map(|m| m.name.as_str())
                    .collect()
            })
            .unwrap_or_default();
        if open_row_methods.is_empty() {
            return None;
        }
        match method {
            // The method itself: only if THAT method is open-row (a
            // pure/closed sibling of an open-row method stays on the normal
            // path).
            Some(m) if info.method_effects.contains_key(m) => {
                if open_row_methods.contains(m) {
                    Some(info.method_effects.get(m).cloned().unwrap_or_default())
                } else {
                    None
                }
            }
            // A where-bound function (`count_foos 42`): union the effects of
            // the trait's open-row methods only.
            _ => {
                let mut by_key: std::collections::BTreeMap<String, EffectEntry> =
                    std::collections::BTreeMap::new();
                for (mname, effs) in &info.method_effects {
                    if open_row_methods.contains(mname.as_str()) {
                        for entry in effs {
                            by_key.insert(super::applied_effect_key(entry), entry.clone());
                        }
                    }
                }
                Some(by_key.into_values().collect())
            }
        }
    }

    /// Settle the recorded references whose constrained type is now known,
    /// and (per `finish`) those that will stay generic. Errors are reported
    /// at the reference and do not stop checking.
    pub(crate) fn resolve_open_row_refs(&mut self, finish: OpenRowFinish<'_>) {
        if self.trait_state.open_row_refs.is_empty() {
            return;
        }
        let pending = std::mem::take(&mut self.trait_state.open_row_refs);
        // A variable under a `where` bound of the enclosing declaration
        // will never become a known type: forward right away, so a `with`
        // around the value's use sees a row it cannot handle.
        let where_bound = self.rigid_where_bound_vars();
        let mut kept = Vec::new();
        for reference in pending {
            match self.sub.apply(&reference.self_ty) {
                Type::Var(var) => {
                    let forward = match finish {
                        OpenRowFinish::Scope { forward } => Some(forward),
                        _ if where_bound.contains(&var) => Some(true),
                        OpenRowFinish::Generalized(vars) => vars.contains(&var).then_some(false),
                        OpenRowFinish::Keep => None,
                    };
                    match forward {
                        None => kept.push(reference),
                        Some(forward) => {
                            if let Err(e) = self.forward_open_row_ref(&reference, var, forward) {
                                self.collected_diagnostics.push(e);
                            }
                        }
                    }
                }
                Type::Con(type_name, args) => {
                    let Some(effects) = self.open_row_impl_effects(
                        &reference.trait_name,
                        &type_name,
                        args.len(),
                        reference.method.as_deref(),
                    ) else {
                        continue;
                    };
                    let self_ty = Type::Con(type_name, args);
                    if let Err(e) =
                        self.require_open_row_ref_effects(&reference, &effects, &self_ty)
                    {
                        self.collected_diagnostics.push(e);
                    }
                }
                _ => {}
            }
        }
        // Nothing is recorded while settling, so order is preserved.
        self.trait_state.open_row_refs.extend(kept);
    }

    fn open_row_ref_row(&mut self, reference: &OpenRowRef) -> Result<EffectRow, Diagnostic> {
        self.normalize_row_at(
            &EffectRow {
                effects: vec![],
                tails: reference.tails.iter().map(|id| Type::Var(*id)).collect(),
            },
            reference.span,
        )
    }

    fn describe_open_row_effects(&self, effects: &[EffectEntry]) -> String {
        if effects.is_empty() {
            return "no effects".to_string();
        }
        let mut names: Vec<String> = effects
            .iter()
            .map(|e| self.prettify_effect_entry(e))
            .collect();
        names.sort();
        format!("{{{}}}", names.join(", "))
    }

    /// The impl is known: the value's arrow must carry its effects.
    fn require_open_row_ref_effects(
        &mut self,
        reference: &OpenRowRef,
        effects: &[EffectEntry],
        self_ty: &Type,
    ) -> Result<(), Diagnostic> {
        if effects.is_empty() {
            return Ok(());
        }
        let row = self.open_row_ref_row(reference)?;
        let pretty_trait = reference
            .trait_name
            .rsplit('.')
            .next()
            .unwrap_or(&reference.trait_name)
            .to_string();
        let whose = format!(
            "`{}` is used here as a function value. For `{}` it runs the impl of `{}`, which \
             needs {}",
            reference.display,
            self.prettify_type(self_ty),
            pretty_trait,
            self.describe_open_row_effects(effects),
        );
        let mut missing = Vec::new();
        for entry in effects {
            match row.effects.iter().find(|e| e.matches(entry)).cloned() {
                Some(existing) => {
                    if !existing.same_instantiation(entry) {
                        self.unify_family(&existing, entry).map_err(|e| {
                            Diagnostic::error_at(reference.span, format!("{whose}. {}", e.message))
                        })?;
                    }
                }
                None => missing.push(entry.clone()),
            }
        }
        if missing.is_empty() {
            return Ok(());
        }
        let Some(tail) = row.tail_var_ids().first().copied() else {
            return Err(Diagnostic::error_at(
                reference.span,
                format!(
                    "{whose}, but the function type expected here allows only {}. Handle {} \
                     around a call (`fun x -> {} x with ...`), or use a function type that \
                     names those effects",
                    self.describe_open_row_effects(&row.effects),
                    self.describe_open_row_effects(&missing),
                    reference.display,
                ),
            ));
        };
        self.bind_row_checked(tail, EffectRow::closed(missing))
            .map_err(|e| Diagnostic::error_at(reference.span, format!("{whose}. {}", e.message)))
    }

    /// The impl stays unknown here (it is chosen with the type variable
    /// `var`): the value's arrow carries `..var`.
    fn forward_open_row_ref(
        &mut self,
        reference: &OpenRowRef,
        var: u32,
        forward: bool,
    ) -> Result<(), Diagnostic> {
        let row = self.open_row_ref_row(reference)?;
        let target = Type::Var(var);
        // `..var` may itself have been unified with other row variables.
        let target_row = self.sub.apply_effect_row(&EffectRow {
            effects: vec![],
            tails: vec![target.clone()],
        });
        let already_forwarded = target_row.effects.is_empty()
            && !target_row.tails.is_empty()
            && target_row.tails.iter().all(|t| row.tails.contains(t));
        if !already_forwarded {
            let free_tail = row
                .tail_var_ids()
                .into_iter()
                .find(|tail| self.rigid_row_var_for(*tail).is_none());
            let Some(tail) = free_tail else {
                let pretty_trait = reference
                    .trait_name
                    .rsplit('.')
                    .next()
                    .unwrap_or(&reference.trait_name);
                let var_name = self
                    .trait_state
                    .where_bound_var_names
                    .get(&var)
                    .cloned()
                    .unwrap_or_else(|| "a".to_string());
                return Err(Diagnostic::error_at(
                    reference.span,
                    format!(
                        "`{name}` is used here as a function value at a type whose impl of \
                         `{pretty_trait}` is chosen by the caller, so it may need any effects, \
                         but the function type expected here allows only {allowed}. Give that \
                         function type the row `needs {{..{var_name}}}`",
                        name = reference.display,
                        allowed = self.describe_open_row_effects(&row.effects),
                    ),
                ));
            };
            self.bind_row_checked(
                tail,
                EffectRow {
                    effects: vec![],
                    tails: vec![target],
                },
            )
            .map_err(|e| e.with_span(reference.span))?;
        }
        if forward {
            self.trait_forward_row_vars
                .entry(var)
                .or_insert_with(|| reference.trait_name.clone());
        }
        Ok(())
    }
}
