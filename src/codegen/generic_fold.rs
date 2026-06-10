//! Phase 4/5 (generic fold): trait-neutral inlining of known dict-method calls,
//! and cancellation of the intermediate `Generic` `Rep` constructor tree.
//!
//! **Phase 4** collapses a statically-known *parameterized* dictionary chain —
//! e.g. `to_json` dispatched through `__dict_ToJson_Adt(__dict_ToJson_Variant(
//! __dict_ToJson_Leaf(__dict_ToJson_Int)))` — by inlining the outer impl's method
//! lambda and β-reducing it against the call arguments. The result is a nested
//! `case` over the argument whose body re-dispatches through the *concrete
//! sub-dictionary*; folding recurses until the chain bottoms out at a **nullary**
//! dict call (which Phases 2/3 specialize at lowering) or runs out of fuel (left
//! as an ordinary `element/2` dict call). This removes the intermediate
//! `Adt`/`Variant`/`Leaf`/`Record`/… *dictionary* tuples and `element/2`
//! projections.
//!
//! **Phase 5** additionally cancels the `Rep` constructor *values*. When the
//! routed-derive delegating impl `m x = m (to x)` is folded, `to` (the `Rep`
//! builder) is inlined so its constructor result is syntactically visible, then
//! the codec's case-matches are cancelled against it (`case Con(args) of Con pats
//! -> …` ⟶ bind `pats := args`). The driver keys off `Generic` routing and only
//! cancels `Std.Generic` representation constructors, so it is trait-agnostic
//! (`ToJson`/`PostgresRow`/`CsvRow`/…) and never rewrites arbitrary user codecs.
//!
//! ## Local vs. cross-module
//!
//! - **Local impls** (`DictConstructor` in this module's program) are inlined
//!   directly; their references resolve in this module — fresh inlined nodes have
//!   no front-end resolution entry (their NodeIds are new), so backend
//!   `resolve_names` falls back to name-based resolution in this module's scope.
//! - **Cross-module impls** (a `DictConstructor` from another compiled module,
//!   supplied via [`external_ctors_from_modules`]) are inlined by copying the
//!   producer's method body. Because BEAM does not inline across modules, we do
//!   the cross-module move here, at the AST level, before emitting Core — the
//!   GHC "ship the unfolding, specialize at the consumer" move adapted to
//!   separate-compilation BEAM. The producer body's own references (private
//!   helpers, other impls) are carried over via the producer's resolution map
//!   (see [`FoldOutput::carried_resolution`]); at lowering they become direct
//!   cross-module calls (every function is exported in Core — privacy is a
//!   front-end concern).
//!
//! ## Where it runs and why it is safe
//!
//! The pass operates on the elaborated, normalized AST **before** name
//! resolution and the optimizer/`call_effects` analyses, so every downstream
//! NodeId-keyed analysis recomputes over the rewritten tree. Inlining is a
//! meaning-preserving β-reduction — we never hand-thread evidence or effects
//! (specialization swaps callees, not the effect ABI). Soundness rests on:
//! - Inlined bodies are cloned with **fresh NodeIds** so two call sites that
//!   inline the same method never collide in the side tables. For cross-module
//!   bodies the producer's resolution entries are remapped onto those fresh ids.
//! - Impl/derive method bodies have **no free local variables** (they reference
//!   only their own params, the `where`-bound dict params we substitute away,
//!   trait methods, helpers, and constructors), so reusing the method's
//!   parameter names as `case` binders cannot capture.
//! - Resolution runs *after* the fold, so local fresh nodes are resolved fresh
//!   (by name) and carried cross-module entries override any consumer-scope guess.

use crate::ast::{
    Annotated, CaseArm, ComprehensionQualifier, Decl, Expr, ExprKind, Handler, HandlerArm,
    HandlerBody, HandlerItem, NodeId, Pat, Program, Stmt, StringPart,
};
use crate::codegen::resolve::ResolutionMap;
use crate::desugar::{freshen_expr_ids, freshen_pat_ids};
use std::collections::HashMap;

/// Maximum inline-chain depth per call site. A parameterized dict chain deeper
/// than this (a deeply nested record, or a recursive type) bottoms out as an
/// ordinary dict-passing call — correct, just unfused. `Rep` trees are shallow
/// (bounded by field/constructor nesting), so this is generous in practice.
const INLINE_FUEL: u32 = 64;

/// The `Generic` routing trait and its `to` method index. The fusion driver
/// inlines `to` (the `Rep` builder) so its constructor result can be cancelled
/// against the codec's case-matches. (`from`, the decode direction, is Phase 6.)
const GENERIC_TRAIT: &str = "Std.Generic.Generic";
const GENERIC_TO_METHOD: usize = 0;
/// `Generic.from` (the `Rep` *consumer*, decode direction). Inlining it exposes
/// the consuming `case rep { Rep__T (…) -> T … }` so the produced `Rep` cancels.
const GENERIC_FROM_METHOD: usize = 1;

/// The `Std.Generic` representation constructors. The fusion engine only cancels
/// *these* (plus the per-type `Rep__T` wrappers), which scopes it to the
/// Generic-routing machinery — trait-agnostic across `ToJson`/`PostgresRow`/… —
/// rather than inlining arbitrary user/stdlib codecs (which would broaden the
/// blast radius and risk breaking their scoping).
const REP_CTORS: &[&str] = &[
    "U1", "Leaf", "Labeled", "And", "Or_Left", "Or_Right", "Variant", "Record", "Adt",
];

/// A parameterized `DictConstructor` defined in another compiled module, with
/// the producer's resolution map for carrying its body's name resolutions.
pub struct ExternalCtor<'a> {
    pub dict_params: &'a [String],
    pub methods: &'a [Expr],
    pub resolution: &'a ResolutionMap,
}

/// External dict constructors keyed by dict-constructor name.
pub type ExternalCtors<'a> = HashMap<String, ExternalCtor<'a>>;

/// Result of folding a module: the rewritten program plus resolution entries for
/// inlined cross-module nodes (keyed by their fresh NodeId), to be merged into
/// the consumer's resolution map *after* `resolve_names` so they override any
/// consumer-scope resolution of those fresh nodes.
pub struct FoldOutput {
    pub program: Program,
    pub carried_resolution: ResolutionMap,
}

/// Collect every module's parameterized `DictConstructor`s as external ctors,
/// borrowing each producer's resolution map for carrying. Used at consumer emit
/// time, where `ctx.modules` holds all other compiled modules.
pub fn external_ctors_from_modules(
    modules: &HashMap<String, super::CompiledModule>,
) -> ExternalCtors<'_> {
    let mut map = ExternalCtors::new();
    for compiled in modules.values() {
        for decl in &compiled.elaborated {
            if let Decl::DictConstructor {
                name,
                dict_params,
                methods,
                ..
            } = decl
            {
                map.insert(
                    name.clone(),
                    ExternalCtor {
                        dict_params,
                        methods,
                        resolution: &compiled.resolution,
                    },
                );
            }
        }
    }
    map
}

/// One dict constructor available for inlining — local (`resolution: None`) or
/// external (carry the producer's resolution).
struct CtorView<'a> {
    dict_params: &'a [String],
    methods: &'a [Expr],
    resolution: Option<&'a ResolutionMap>,
}

struct Folder<'a> {
    ctors: HashMap<&'a str, CtorView<'a>>,
    carried: ResolutionMap,
}

/// Inline known dict-method calls throughout a module's function and
/// dict-constructor bodies, cancelling `Generic` `Rep` constructors where they
/// become statically visible. `externals` supplies cross-module impls; pass an
/// empty map for local-only folding.
pub fn fold_program(program: &Program, externals: &ExternalCtors<'_>) -> FoldOutput {
    let mut ctors: HashMap<&str, CtorView<'_>> = HashMap::new();
    // Externals first; a local impl of the same name (shouldn't happen — dict
    // names are globally unique) would take precedence.
    for (name, ext) in externals {
        ctors.insert(
            name.as_str(),
            CtorView {
                dict_params: ext.dict_params,
                methods: ext.methods,
                resolution: Some(ext.resolution),
            },
        );
    }
    for decl in program {
        if let Decl::DictConstructor {
            name,
            dict_params,
            methods,
            ..
        } = decl
        {
            ctors.insert(
                name.as_str(),
                CtorView {
                    dict_params,
                    methods,
                    resolution: None,
                },
            );
        }
    }

    if ctors.is_empty() {
        return FoldOutput {
            program: program.clone(),
            carried_resolution: ResolutionMap::new(),
        };
    }

    let mut folder = Folder {
        ctors,
        carried: ResolutionMap::new(),
    };
    let mut out = program.clone();
    for decl in &mut out {
        folder.fold_decl(decl);
    }
    FoldOutput {
        program: out,
        carried_resolution: folder.carried,
    }
}

impl Folder<'_> {
    fn fold_decl(&mut self, decl: &mut Decl) {
        match decl {
            Decl::FunBinding { body, .. } => self.fold_expr(body, INLINE_FUEL),
            Decl::DictConstructor { methods, .. } => {
                for method in methods {
                    self.fold_expr(method, INLINE_FUEL);
                }
            }
            _ => {}
        }
    }

    /// Fold one expression in place: simplify children first (bottom-up, so a
    /// node sees collapsed children), then run a fuel-bounded local fixpoint at
    /// this node. `fuel` bounds the rewrite chain rooted at this node.
    fn fold_expr(&mut self, expr: &mut Expr, fuel: u32) {
        for child in child_exprs_mut(expr) {
            self.fold_expr(child, fuel);
        }
        let mut budget = fuel;
        while budget > 0 {
            let Some(rewritten) = self.rewrite_once(expr) else {
                break;
            };
            *expr = rewritten;
            budget -= 1;
            // A rewrite introduces new structure (an inlined body, a floated
            // case); re-simplify the rewritten node's children.
            for child in child_exprs_mut(expr) {
                self.fold_expr(child, fuel);
            }
        }
    }

    /// One simplification step at `expr`, or `None` at a fixpoint. Ordered
    /// collapse-before-inline (the key Phase-4/5 insight): cancel known
    /// constructors and float/commute cases outward *before* inlining, so the
    /// inline fuel never sees an un-collapsed `Rep` tree.
    fn rewrite_once(&mut self, expr: &Expr) -> Option<Expr> {
        // Type ascriptions are erased at codegen; drop them so the rewrites
        // below see through `(to x : Rep__T)`.
        if let ExprKind::Ascription { expr: inner, .. } = &expr.kind {
            return Some((**inner).clone());
        }
        if let Some(e) = case_of_known_constructor(expr) {
            return Some(e);
        }
        // Phase 6 (decode): `case (case S {…}) {…}` ⟶ commute, so the producer
        // codec's `Ok (RepCtor …)` meets the consuming `from`/`Result` case.
        if let Some(e) = case_of_case(expr) {
            return Some(e);
        }
        if let Some(e) = float_case_out_of_arg(expr) {
            return Some(e);
        }
        // Phase 6 (decode): inline a nullary producer codec that is the scrutinee
        // of a case, so its `Ok (RepCtor …)` result becomes a literal ctor under
        // that case (which `case_of_case` + cancellation then collapse).
        if let Some(e) = self.inline_codec_scrutinee(expr) {
            return Some(e);
        }
        self.try_inline(expr)
    }

    /// If `expr` is a saturated call to a known dict method that we should
    /// inline, produce its inlined form (the method body β-reduced against the
    /// arguments). Records carried resolution when the impl is cross-module.
    /// Returns `None` otherwise.
    fn try_inline(&mut self, expr: &Expr) -> Option<Expr> {
        let (head, args) = peel_app(expr);
        let ExprKind::DictMethodAccess {
            dict,
            trait_name,
            method_index,
        } = &head.kind
        else {
            return None;
        };

        let (dict_head, sub_dicts) = peel_app(dict);
        let ExprKind::DictRef { name } = &dict_head.kind else {
            return None; // `Var` head => runtime dict; leave on the dispatch path.
        };

        // Nullary dicts normally lower to a direct call (Phase 2/3). Inline a
        // nullary body only in a *fusion* context, where the inline immediately
        // unblocks constructor cancellation: it's `Generic.to` (the `Rep`
        // builder, encode) or `Generic.from` (the `Rep` consumer, decode), or its
        // argument is already a known `Rep` constructor (a codec walking a known
        // `Rep`). Otherwise leave it — e.g. `encode u.id` on a plain value stays
        // a direct leaf call. Parameterized dicts (Phase 4a) always inline.
        if sub_dicts.is_empty() {
            let is_generic_to = trait_name == GENERIC_TRAIT && *method_index == GENERIC_TO_METHOD;
            let is_generic_from =
                trait_name == GENERIC_TRAIT && *method_index == GENERIC_FROM_METHOD;
            let arg_is_rep_ctor = args.iter().any(|a| known_rep_ctor(a).is_some());
            if !is_generic_to && !is_generic_from && !arg_is_rep_ctor {
                return None;
            }
        }

        self.perform_inline(name, &sub_dicts, &args, *method_index)
    }

    /// Inline a nullary producer codec that is the *scrutinee* of a case (decode
    /// direction). The routed-from codec `FromJson_Rep__T.from_json s` is nullary
    /// and its argument is the input (not a `Rep` ctor), so the `try_inline` gates
    /// don't fire — but its result is `Ok (RepCtor …)`, consumed by the enclosing
    /// `case`. Inlining it here makes that `Ok (RepCtor …)` a literal ctor under
    /// the case, which `case_of_case` + cancellation then collapse. Gated on the
    /// codec body being a constructor-producing `case` (a `Result`-map), so it
    /// never inlines arbitrary nullary methods that merely sit in scrutinee
    /// position.
    fn inline_codec_scrutinee(&mut self, expr: &Expr) -> Option<Expr> {
        let ExprKind::Case {
            scrutinee,
            arms,
            dangling_trivia,
        } = &expr.kind
        else {
            return None;
        };
        let (head, sargs) = peel_app(scrutinee);
        let ExprKind::DictMethodAccess {
            dict, method_index, ..
        } = &head.kind
        else {
            return None;
        };
        let (dict_head, sub_dicts) = peel_app(dict);
        let ExprKind::DictRef { name } = &dict_head.kind else {
            return None;
        };
        // Only nullary codecs here; parameterized ones inline via `try_inline`.
        if !sub_dicts.is_empty() || !self.codec_body_produces_rep(name, *method_index) {
            return None;
        }
        let inlined = self.perform_inline(name, &sub_dicts, &sargs, *method_index)?;
        Some(Expr::synth(
            expr.span,
            ExprKind::Case {
                scrutinee: Box::new(inlined),
                arms: arms.clone(),
                dangling_trivia: dangling_trivia.clone(),
            },
        ))
    }

    /// True when dict `name`'s method `method_index` body is a `Rep`-producing
    /// `case` — the routed-from bridge shape `case _ { Ok x -> Ok (Rep__T x); Err
    /// e -> Err e }`. Used to gate [`Self::inline_codec_scrutinee`] so it only
    /// inlines genuine `Rep`-tree producers.
    fn codec_body_produces_rep(&self, name: &str, method_index: usize) -> bool {
        let Some(ctor) = self.ctors.get(name) else {
            return false;
        };
        let Some(method) = ctor.methods.get(method_index) else {
            return false;
        };
        let ExprKind::Lambda { body, .. } = &method.kind else {
            return false;
        };
        body_is_rep_producing_case(body)
    }

    /// Perform the inline: look up dict `name`'s method `method_index`, β-reduce
    /// its lambda against `args`, substituting the `where`-bound dict params with
    /// `sub_dicts`. Freshens the body's NodeIds (carrying a cross-module
    /// producer's resolution onto the fresh ids). Returns `None` on
    /// missing/partial/over-application.
    fn perform_inline(
        &mut self,
        name: &str,
        sub_dicts: &[&Expr],
        args: &[&Expr],
        method_index: usize,
    ) -> Option<Expr> {
        // Copy out the borrowed ctor fields (all `&'a`) so the `&self.ctors`
        // borrow ends before we mutate `self.carried` below.
        let (dict_params, methods, resolution) = {
            let ctor = self.ctors.get(name)?;
            (ctor.dict_params, ctor.methods, ctor.resolution)
        };
        if dict_params.len() != sub_dicts.len() {
            return None;
        }
        let method = methods.get(method_index)?;
        let ExprKind::Lambda { params, body } = &method.kind else {
            return None;
        };
        if params.len() != args.len() {
            return None; // Partial/over-application — leave on the dispatch path.
        }

        // Clone the method body and freshen its NodeIds. For a cross-module body,
        // remap the producer's resolution entries onto the fresh ids so its
        // references lower as direct cross-module calls. For a local body,
        // freshening orphans the id-keyed front resolution, but backend
        // `resolve_names` falls back to name-based resolution in this module's
        // scope (so no carry is needed).
        let mut new_body = body.as_ref().clone();
        match resolution {
            Some(producer_res) => {
                let mut old_ids = Vec::new();
                collect_expr_ids(&mut new_body, &mut old_ids);
                freshen_expr_ids(&mut new_body);
                let mut new_ids = Vec::new();
                collect_expr_ids(&mut new_body, &mut new_ids);
                debug_assert_eq!(
                    old_ids.len(),
                    new_ids.len(),
                    "id collection must be structurally stable across freshening"
                );
                for (old, new) in old_ids.iter().zip(&new_ids) {
                    if let Some(sym) = producer_res.get(old) {
                        self.carried.insert(*new, sym.clone());
                    }
                }
            }
            None => freshen_expr_ids(&mut new_body),
        }

        // Substitute the `where`-bound dict params with the concrete sub-dicts.
        let subst: HashMap<&str, &Expr> = dict_params
            .iter()
            .map(String::as_str)
            .zip(sub_dicts.iter().copied())
            .collect();
        substitute_dict_vars(&mut new_body, &subst);

        // β-reduce against the arguments: a `Var`/`Wildcard` parameter binds by
        // substitution (so a known-constructor argument stays syntactically
        // visible — e.g. `to`'s `val` param isn't wrapped in a trivial `case x of
        // val -> …` that would hide the constructor from floating); a constructor
        // parameter becomes a single-arm `case`. Patterns are exhaustive for the
        // dispatched type (the impl method typechecked).
        Some(bind_subpats(params, args, &new_body))
    }
}

/// Replace every `Var` whose name is a substituted dict param with the
/// corresponding concrete sub-dictionary expression (cloned with fresh ids).
fn substitute_dict_vars(expr: &mut Expr, subst: &HashMap<&str, &Expr>) {
    if let ExprKind::Var { name } = &expr.kind
        && let Some(replacement) = subst.get(name.as_str())
    {
        let mut value = (*replacement).clone();
        freshen_expr_ids(&mut value);
        *expr = value;
        return;
    }
    for child in child_exprs_mut(expr) {
        substitute_dict_vars(child, subst);
    }
}

/// Collect the NodeId of `expr` and all descendant expressions in a
/// deterministic pre-order. Run before and after `freshen_expr_ids` on the same
/// (structurally unchanged) tree to build an old→new id mapping by position.
fn collect_expr_ids(expr: &mut Expr, out: &mut Vec<NodeId>) {
    out.push(expr.id);
    for child in child_exprs_mut(expr) {
        collect_expr_ids(child, out);
    }
}

/// The unqualified base of a (possibly `Mod.Sub.`-qualified) name. Constructor
/// names enter the fold from two sources that disagree on qualification: the
/// `Generic.to` builder writes fully-qualified `Std.Generic.Adt`, while impl
/// patterns carry the name as the user wrote it (`Adt`). Cancellation compares
/// on the base so the two meet.
fn base_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// True for a `Std.Generic` representation constructor or a per-type `Rep__T`
/// wrapper — the only constructors the fusion engine cancels.
fn is_rep_ctor(name: &str) -> bool {
    let base = base_name(name);
    base.starts_with("Rep__") || REP_CTORS.contains(&base)
}

/// Like [`known_ctor`], but only for `Rep` constructors (see [`is_rep_ctor`]).
fn known_rep_ctor(expr: &Expr) -> Option<(&str, Vec<&Expr>)> {
    let (name, args) = known_ctor(expr)?;
    is_rep_ctor(name).then_some((name, args))
}

/// If `expr` is a saturated data-constructor application `Con a1 … an`, return
/// the constructor name and its arguments in source order. `None` otherwise.
fn known_ctor(expr: &Expr) -> Option<(&str, Vec<&Expr>)> {
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
/// Not restricted to `Rep` constructors: this fires on `Ok`/`Err` too (Phase 6
/// cancels the `Result` wrapper threaded through the decode codec). It is sound
/// and bounded for arbitrary constructors because it only matches a scrutinee
/// that is a *literal* constructor application — a shape that arises from the
/// fold's own inlining/commuting, not from ordinary source.
fn case_of_known_constructor(expr: &Expr) -> Option<Expr> {
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

/// Result of statically deciding whether `pat` matches a (partially) known value.
enum Match {
    Yes,
    No,
    Unknown,
}

/// Decide whether `pat` matches `value`, recursing through nested constructors.
/// A multi-variant `Generic.from` has several arms sharing an outer constructor
/// (`Adt _ (Or_Left …)`, `Adt _ (Or_Right …)`, …), so deciding on the outer
/// constructor alone would wrongly commit to the first; the recursion routes each
/// `Or` branch to the correct arm.
fn static_match(pat: &Pat, value: &Expr) -> Match {
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
fn commit_matched_arm(pat: &Pat, scrutinee: &Expr, body: &Expr) -> Expr {
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
fn bind_subpats(subpats: &[Pat], cargs: &[&Expr], body: &Expr) -> Expr {
    let mut result = body.clone();
    for (subpat, carg) in subpats.iter().zip(cargs).rev() {
        match subpat {
            Pat::Wildcard { .. } if is_duplicable(carg) => {}
            Pat::Var { name, .. } if is_duplicable(carg) => {
                substitute_var(&mut result, name, carg)
            }
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
fn is_duplicable(expr: &Expr) -> bool {
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
        // A saturated data-constructor application is a pure build; allow it when
        // every argument is duplicable. A non-constructor application (a function
        // call) may be effectful, so `known_ctor` returning `None` rejects it.
        ExprKind::App { .. } => {
            known_ctor(expr).is_some_and(|(_, args)| args.iter().all(|a| is_duplicable(a)))
        }
        _ => false,
    }
}

/// Replace free occurrences of `Var{name}` with `replacement` (cloned with fresh
/// ids per occurrence), **capture-avoiding**: substitution does not descend into
/// a sub-scope that re-binds `name`. This matters because bottom-up folding nests
/// inlined bodies that independently reuse binder names (every building-block
/// codec names its payload `inner`), so the same name is shadowed at several
/// depths; a naive substitution would rewrite the shadowed occurrences too.
fn substitute_var(expr: &mut Expr, name: &str, replacement: &Expr) {
    match &mut expr.kind {
        ExprKind::Var { name: var_name } => {
            if var_name == name {
                let mut value = replacement.clone();
                freshen_expr_ids(&mut value);
                *expr = value;
            }
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            substitute_var(scrutinee, name, replacement);
            for ann in arms {
                // The arm pattern binds for its guard + body; if it re-binds
                // `name`, those are a shadowed scope — leave them.
                if pat_binds(&ann.node.pattern, name) {
                    continue;
                }
                if let Some(g) = &mut ann.node.guard {
                    substitute_var(g, name, replacement);
                }
                substitute_var(&mut ann.node.body, name, replacement);
            }
        }
        ExprKind::Lambda { params, body } => {
            if !params.iter().any(|p| pat_binds(p, name)) {
                substitute_var(body, name, replacement);
            }
        }
        ExprKind::Block { stmts, .. } => {
            // Sequential scoping: a `let`/`letfun` binding `name` shadows it for
            // every following statement and the block tail.
            let mut shadowed = false;
            for ann in stmts {
                match &mut ann.node {
                    Stmt::Let { pattern, value, .. } => {
                        if !shadowed {
                            substitute_var(value, name, replacement);
                        }
                        if pat_binds(pattern, name) {
                            shadowed = true;
                        }
                    }
                    Stmt::LetFun {
                        name: fn_name,
                        params,
                        guard,
                        body,
                        ..
                    } => {
                        let body_shadowed = shadowed
                            || fn_name == name
                            || params.iter().any(|p| pat_binds(p, name));
                        if !body_shadowed {
                            if let Some(g) = guard {
                                substitute_var(g, name, replacement);
                            }
                            substitute_var(body, name, replacement);
                        }
                        if fn_name == name {
                            shadowed = true;
                        }
                    }
                    Stmt::Expr(e) => {
                        if !shadowed {
                            substitute_var(e, name, replacement);
                        }
                    }
                }
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let mut shadowed = false;
            for (pat, e) in bindings {
                if !shadowed {
                    substitute_var(e, name, replacement);
                }
                if pat_binds(pat, name) {
                    shadowed = true;
                }
            }
            if !shadowed {
                substitute_var(success, name, replacement);
            }
            // Else arms run in the outer scope (the do-bindings failed), each
            // scoped only by its own pattern.
            for ann in else_arms {
                if pat_binds(&ann.node.pattern, name) {
                    continue;
                }
                if let Some(g) = &mut ann.node.guard {
                    substitute_var(g, name, replacement);
                }
                substitute_var(&mut ann.node.body, name, replacement);
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            let mut shadowed = false;
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(pat, e)
                    | ComprehensionQualifier::Let(pat, e) => {
                        if !shadowed {
                            substitute_var(e, name, replacement);
                        }
                        if pat_binds(pat, name) {
                            shadowed = true;
                        }
                    }
                    ComprehensionQualifier::Guard(e) => {
                        if !shadowed {
                            substitute_var(e, name, replacement);
                        }
                    }
                }
            }
            if !shadowed {
                substitute_var(body, name, replacement);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann in arms {
                if pat_binds(&ann.node.pattern, name) {
                    continue;
                }
                if let Some(g) = &mut ann.node.guard {
                    substitute_var(g, name, replacement);
                }
                substitute_var(&mut ann.node.body, name, replacement);
            }
            if let Some((timeout, body)) = after_clause {
                substitute_var(timeout, name, replacement);
                substitute_var(body, name, replacement);
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            substitute_var(inner, name, replacement);
            substitute_in_handler(handler, name, replacement);
        }
        ExprKind::HandlerExpr { body } => {
            for arm in &mut body.arms {
                substitute_in_handler_arm(&mut arm.node, name, replacement);
            }
        }
        // No other `ExprKind` binds variables, so the generic child recursion is
        // capture-safe for them.
        _ => {
            for child in child_exprs_mut(expr) {
                substitute_var(child, name, replacement);
            }
        }
    }
}

/// Does `pat` bind `name`? (Used to stop capture-avoiding substitution at a
/// shadowing binder.)
fn pat_binds(pat: &Pat, name: &str) -> bool {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } => false,
        Pat::Var { name: n, .. } => n == name,
        Pat::Constructor { args, .. } => args.iter().any(|p| pat_binds(p, name)),
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            elements.iter().any(|p| pat_binds(p, name))
        }
        Pat::Or { patterns, .. } => patterns.iter().any(|p| pat_binds(p, name)),
        // A field with no alias binds the field name itself (`{ status }`); an
        // aliased field (`{ code: c }`) binds the alias pattern's vars.
        Pat::Record {
            fields, as_name, ..
        } => {
            as_name.as_deref() == Some(name) || record_fields_bind(fields, name)
        }
        Pat::AnonRecord { fields, .. } => record_fields_bind(fields, name),
        Pat::StringPrefix { rest, .. } => pat_binds(rest, name),
        Pat::ConsPat { head, tail, .. } => pat_binds(head, name) || pat_binds(tail, name),
        Pat::BitStringPat { segments, .. } => {
            segments.iter().any(|s| pat_binds(&s.value, name))
        }
    }
}

fn record_fields_bind(fields: &[(String, Option<Pat>)], name: &str) -> bool {
    fields.iter().any(|(fname, sub)| match sub {
        Some(p) => pat_binds(p, name),
        None => fname == name,
    })
}

fn substitute_in_handler(handler: &mut Handler, name: &str, replacement: &Expr) {
    match handler {
        Handler::Named(_) => {}
        Handler::Inline { items, .. } => {
            for item in items {
                match &mut item.node {
                    HandlerItem::Named(_) => {}
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        substitute_in_handler_arm(arm, name, replacement);
                    }
                }
            }
        }
    }
}

fn substitute_in_handler_arm(arm: &mut HandlerArm, name: &str, replacement: &Expr) {
    // The arm's operation parameters bind for its body and finally block.
    if arm.params.iter().any(|p| pat_binds(p, name)) {
        return;
    }
    substitute_var(&mut arm.body, name, replacement);
    if let Some(fb) = &mut arm.finally_block {
        substitute_var(fb, name, replacement);
    }
}

/// `f (case s of { p -> e, … })` ⟶ `case s of { p -> f e, … }`, floating a case
/// out of an application's argument so the codec meets the constructor each arm
/// produces. Only fires when some arm body is a known `Rep` constructor (so the
/// result unblocks an inline), to avoid gratuitously duplicating `f` across arms.
fn float_case_out_of_arg(expr: &Expr) -> Option<Expr> {
    let ExprKind::App { func, arg } = &expr.kind else {
        return None;
    };
    let ExprKind::Case {
        scrutinee, arms, ..
    } = &arg.kind
    else {
        return None;
    };
    if !arms.iter().any(|a| known_rep_ctor(&a.node.body).is_some()) {
        return None;
    }
    let new_arms = arms
        .iter()
        .map(|ann| {
            let arm = &ann.node;
            // `func` is duplicated into each arm, so freshen each copy.
            let mut func_copy = (**func).clone();
            freshen_expr_ids(&mut func_copy);
            Annotated::bare(CaseArm {
                pattern: clone_fresh_pat(&arm.pattern),
                guard: arm.guard.clone(),
                body: Expr::synth(
                    arm.body.span,
                    ExprKind::App {
                        func: Box::new(func_copy),
                        arg: Box::new(arm.body.clone()),
                    },
                ),
                span: arm.span,
            })
        })
        .collect();
    Some(Expr::synth(
        expr.span,
        ExprKind::Case {
            scrutinee: Box::new((**scrutinee).clone()),
            arms: new_arms,
            dangling_trivia: vec![],
        },
    ))
}

fn clone_fresh_pat(pat: &Pat) -> Pat {
    let mut p = pat.clone();
    freshen_pat_ids(&mut p);
    p
}

fn clone_fresh_arm(arm: &CaseArm) -> Annotated<CaseArm> {
    let mut body = arm.body.clone();
    freshen_expr_ids(&mut body);
    let guard = arm.guard.as_ref().map(|g| {
        let mut g = g.clone();
        freshen_expr_ids(&mut g);
        g
    });
    Annotated::bare(CaseArm {
        pattern: clone_fresh_pat(&arm.pattern),
        guard,
        body,
        span: arm.span,
    })
}

/// case-of-case commuting conversion (Phase 6, decode direction):
/// `case (case S { p_i -> e_i }) { outer }` ⟶ `case S { p_i -> case e_i { outer } }`.
///
/// This pushes the consuming `case` (the delegating `{Ok f -> Ok (from f); Err e
/// -> Err e}` once `from` is inlined) down to where the producer codec's
/// `Ok (RepCtor …)` / `Err e` constructors are built, so `case_of_known_constructor`
/// can then cancel them. Two guards keep it sound and non-explosive:
///
/// - **Unblocks cancellation**: fires only when some inner arm body `e_i` is a
///   known constructor application (mirrors `float_case_out_of_arg`), so the
///   duplicated `outer` arms immediately collapse rather than lingering.
/// - **Capture-avoiding**: each inner arm pattern `p_i` now also scopes the
///   `outer` arms it wraps; if any `p_i` binds a name that occurs *free* in
///   `outer`, commuting would capture it, so we leave the case intact.
fn case_of_case(expr: &Expr) -> Option<Expr> {
    let ExprKind::Case {
        scrutinee,
        arms: outer_arms,
        ..
    } = &expr.kind
    else {
        return None;
    };
    let ExprKind::Case {
        scrutinee: inner_scrut,
        arms: inner_arms,
        ..
    } = &scrutinee.kind
    else {
        return None;
    };
    // Anchor on `Rep` production somewhere in an inner arm's subtree: only
    // commute when the codec eventually builds a `Rep` tree, so this never
    // duplicates the outer arms across an unrelated nested `case` (e.g. a
    // hand-written parser's `Result` threading, which carries no `Rep`).
    if !inner_arms
        .iter()
        .any(|a| subtree_produces_rep(&a.node.body))
    {
        return None;
    }
    let outer_free = free_vars_arms(outer_arms);
    let captures = inner_arms.iter().any(|a| {
        let mut bound = Vec::new();
        pat_bound_names(&a.node.pattern, &mut bound);
        bound.iter().any(|n| outer_free.contains(n))
    });
    if captures {
        return None;
    }

    let new_arms = inner_arms
        .iter()
        .map(|ann| {
            let arm = &ann.node;
            // Duplicate `outer` into this arm (fresh ids per copy), wrapping the
            // inner arm body as the new scrutinee.
            let outer_copy: Vec<Annotated<CaseArm>> =
                outer_arms.iter().map(|a| clone_fresh_arm(&a.node)).collect();
            let wrapped = Expr::synth(
                arm.body.span,
                ExprKind::Case {
                    scrutinee: Box::new(arm.body.clone()),
                    arms: outer_copy,
                    dangling_trivia: vec![],
                },
            );
            Annotated::bare(CaseArm {
                pattern: clone_fresh_pat(&arm.pattern),
                guard: arm.guard.clone(),
                body: wrapped,
                span: arm.span,
            })
        })
        .collect();
    Some(Expr::synth(
        expr.span,
        ExprKind::Case {
            scrutinee: Box::new((**inner_scrut).clone()),
            arms: new_arms,
            dangling_trivia: vec![],
        },
    ))
}

/// True when `body` is a `Rep`-producing `case` — the routed-from bridge codec
/// shape `case _ { Ok x -> Ok (Rep__T x); Err e -> Err e }`. Sees through a
/// leading ascription. Anchoring on a *`Rep`* constructor (not any ctor) keeps
/// the decode rewrites a no-op on unrelated codecs — e.g. a hand-written JSON
/// object parser that returns `Ok (value, rest)` produces a tuple, not a `Rep`,
/// so it is left untouched rather than inlined without any cancellation payoff.
fn body_is_rep_producing_case(body: &Expr) -> bool {
    match &body.kind {
        ExprKind::Case { arms, .. } => arms.iter().any(|a| produces_rep_ctor(&a.node.body)),
        ExprKind::Ascription { expr, .. } => body_is_rep_producing_case(expr),
        _ => false,
    }
}

/// True when `e` builds a `Rep` constructor, possibly under wrapper constructors
/// (`Ok (Rep__T …)`, `Ok (Adt …)`). Used to anchor the decode rewrites to actual
/// `Rep`-tree production so they don't fire on unrelated `Result`-returning code.
fn produces_rep_ctor(e: &Expr) -> bool {
    match known_ctor(e) {
        Some((name, args)) => is_rep_ctor(name) || args.iter().any(|a| produces_rep_ctor(a)),
        None => false,
    }
}

/// True when `e` builds a `Rep` constructor *anywhere* in its subtree. A record's
/// `And` node is built deep inside the field-codec's nested `Result` threading
/// (`Ok l -> case … { Ok r -> Ok (And l r) … }`), so the top-level arms don't
/// directly produce a `Rep`; `case_of_case` needs the subtree view to know the
/// commute will eventually reach a cancellation. A hand-written object parser
/// threads tuples with no `Rep` anywhere, so it stays `false`.
fn subtree_produces_rep(e: &Expr) -> bool {
    if produces_rep_ctor(e) {
        return true;
    }
    let mut tmp = e.clone();
    child_exprs_mut(&mut tmp)
        .into_iter()
        .any(|c| subtree_produces_rep(c))
}

/// Names bound by a pattern (appended to `out`). Used by the case-of-case capture
/// guard and is the dual of [`pat_binds`].
fn pat_bound_names(pat: &Pat, out: &mut Vec<String>) {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Constructor { args, .. } => {
            for a in args {
                pat_bound_names(a, out);
            }
        }
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            for a in elements {
                pat_bound_names(a, out);
            }
        }
        Pat::Or { patterns, .. } => {
            for a in patterns {
                pat_bound_names(a, out);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            if let Some(n) = as_name {
                out.push(n.clone());
            }
            record_field_bound_names(fields, out);
        }
        Pat::AnonRecord { fields, .. } => record_field_bound_names(fields, out),
        Pat::StringPrefix { rest, .. } => pat_bound_names(rest, out),
        Pat::ConsPat { head, tail, .. } => {
            pat_bound_names(head, out);
            pat_bound_names(tail, out);
        }
        Pat::BitStringPat { segments, .. } => {
            for s in segments {
                pat_bound_names(&s.value, out);
            }
        }
    }
}

fn record_field_bound_names(fields: &[(String, Option<Pat>)], out: &mut Vec<String>) {
    for (fname, sub) in fields {
        match sub {
            Some(p) => pat_bound_names(p, out),
            None => out.push(fname.clone()),
        }
    }
}

/// Free variables across a list of case arms (each arm pattern binds within its
/// guard + body). Binder-aware so a name bound *inside* an arm isn't counted as
/// free — the case-of-case capture guard needs the precise set, not an
/// over-approximation (the decode codec reuses `e` for every `Err` arm).
fn free_vars_arms(arms: &[Annotated<CaseArm>]) -> std::collections::HashSet<String> {
    let mut acc = std::collections::HashSet::new();
    for ann in arms {
        let arm = &ann.node;
        let mut bound = Vec::new();
        pat_bound_names(&arm.pattern, &mut bound);
        if let Some(g) = &arm.guard {
            collect_free_vars(g, &bound, &mut acc);
        }
        collect_free_vars(&arm.body, &bound, &mut acc);
    }
    acc
}

/// Collect free `Var` names of `expr` into `acc`, treating names in `bound` (and
/// any binders encountered along the way) as not free. Mirrors the binder
/// structure of [`substitute_var`].
fn collect_free_vars(expr: &Expr, bound: &[String], acc: &mut std::collections::HashSet<String>) {
    match &expr.kind {
        ExprKind::Var { name } => {
            if !bound.contains(name) {
                acc.insert(name.clone());
            }
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            collect_free_vars(scrutinee, bound, acc);
            for ann in arms {
                let arm = &ann.node;
                let mut inner = bound.to_vec();
                pat_bound_names(&arm.pattern, &mut inner);
                if let Some(g) = &arm.guard {
                    collect_free_vars(g, &inner, acc);
                }
                collect_free_vars(&arm.body, &inner, acc);
            }
        }
        ExprKind::Lambda { params, body } => {
            let mut inner = bound.to_vec();
            for p in params {
                pat_bound_names(p, &mut inner);
            }
            collect_free_vars(body, &inner, acc);
        }
        ExprKind::Block { stmts, .. } => {
            let mut inner = bound.to_vec();
            for ann in stmts {
                match &ann.node {
                    Stmt::Let { pattern, value, .. } => {
                        collect_free_vars(value, &inner, acc);
                        pat_bound_names(pattern, &mut inner);
                    }
                    Stmt::LetFun {
                        name,
                        params,
                        guard,
                        body,
                        ..
                    } => {
                        inner.push(name.clone());
                        let mut body_scope = inner.clone();
                        for p in params {
                            pat_bound_names(p, &mut body_scope);
                        }
                        if let Some(g) = guard {
                            collect_free_vars(g, &body_scope, acc);
                        }
                        collect_free_vars(body, &body_scope, acc);
                    }
                    Stmt::Expr(e) => collect_free_vars(e, &inner, acc),
                }
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let mut inner = bound.to_vec();
            for (pat, e) in bindings {
                collect_free_vars(e, &inner, acc);
                pat_bound_names(pat, &mut inner);
            }
            collect_free_vars(success, &inner, acc);
            for ann in else_arms {
                let arm = &ann.node;
                let mut arm_scope = bound.to_vec();
                pat_bound_names(&arm.pattern, &mut arm_scope);
                if let Some(g) = &arm.guard {
                    collect_free_vars(g, &arm_scope, acc);
                }
                collect_free_vars(&arm.body, &arm_scope, acc);
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            let mut inner = bound.to_vec();
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(pat, e)
                    | ComprehensionQualifier::Let(pat, e) => {
                        collect_free_vars(e, &inner, acc);
                        pat_bound_names(pat, &mut inner);
                    }
                    ComprehensionQualifier::Guard(e) => collect_free_vars(e, &inner, acc),
                }
            }
            collect_free_vars(body, &inner, acc);
        }
        // Other binders (Receive, With, HandlerExpr) don't appear in the decode
        // fusion shapes; fall through to the generic child walk, which keeps the
        // outer `bound` set. This can only *over*-count free vars there (treating
        // their binders as free), which makes the capture guard more conservative
        // — never unsound.
        _ => {
            let mut e = expr.clone();
            for child in child_exprs_mut(&mut e) {
                collect_free_vars(child, bound, acc);
            }
        }
    }
}

/// Peel a chain of `App` nodes, returning the innermost non-`App` head and the
/// applied arguments in source order.
fn peel_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}

/// Mutable references to the direct child expressions of `expr`. Descends into
/// `DictMethodAccess.dict` (the dictionary sub-expression). The match is
/// exhaustive so a newly-added `ExprKind` is a compile error here, not a silent
/// gap. Returning a `Vec<&mut Expr>` (rather than taking a visitor closure) lets
/// callers recurse without a `&mut self`-capturing closure, which would not
/// borrow-check.
fn child_exprs_mut(expr: &mut Expr) -> Vec<&mut Expr> {
    let mut out: Vec<&mut Expr> = Vec::new();
    match &mut expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}

        ExprKind::DictMethodAccess { dict, .. } => out.push(dict),

        ExprKind::App { func, arg } => {
            out.push(func);
            out.push(arg);
        }
        ExprKind::BinOp { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        ExprKind::UnaryMinus { expr: inner } => out.push(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            out.push(cond);
            out.push(then_branch);
            out.push(else_branch);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            out.push(scrutinee);
            for ann_arm in arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    out.push(g);
                }
                out.push(&mut ann_arm.node.body);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for ann_stmt in stmts {
                push_stmt_child_exprs(&mut ann_stmt.node, &mut out);
            }
        }
        ExprKind::Lambda { body, .. } => out.push(body),
        ExprKind::FieldAccess { expr: inner, .. } => out.push(inner),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, val) in fields {
                out.push(val);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            out.push(record);
            for (_, _, val) in fields {
                out.push(val);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                out.push(arg);
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            out.push(inner);
            push_handler_child_exprs(handler, &mut out);
        }
        ExprKind::Resume { value } => out.push(value),
        ExprKind::HandlerExpr { body } => push_handler_body_child_exprs(body, &mut out),
        ExprKind::Tuple { elements } => {
            for e in elements {
                out.push(e);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, e) in bindings {
                out.push(e);
            }
            out.push(success);
            for ann_arm in else_arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    out.push(g);
                }
                out.push(&mut ann_arm.node.body);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann_arm in arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    out.push(g);
                }
                out.push(&mut ann_arm.node.body);
            }
            if let Some((timeout, body)) = after_clause {
                out.push(timeout);
                out.push(body);
            }
        }
        ExprKind::Ascription { expr: inner, .. } => out.push(inner),
        ExprKind::BitString { segments } => {
            for seg in segments {
                out.push(&mut seg.value);
                if let Some(size) = &mut seg.size {
                    out.push(size);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                out.push(&mut seg.node);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                out.push(&mut seg.node);
            }
        }
        ExprKind::Cons { head, tail } => {
            out.push(head);
            out.push(tail);
        }
        ExprKind::ListLit { elements } => {
            for e in elements {
                out.push(e);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    out.push(e);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            out.push(body);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Let(_, e)
                    | ComprehensionQualifier::Guard(e) => out.push(e),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                out.push(arg);
            }
        }
    }
    out
}

fn push_stmt_child_exprs<'e>(stmt: &'e mut Stmt, out: &mut Vec<&'e mut Expr>) {
    match stmt {
        Stmt::Let { value, .. } => out.push(value),
        Stmt::LetFun { guard, body, .. } => {
            if let Some(g) = guard {
                out.push(g);
            }
            out.push(body);
        }
        Stmt::Expr(e) => out.push(e),
    }
}

fn push_handler_child_exprs<'e>(handler: &'e mut Handler, out: &mut Vec<&'e mut Expr>) {
    match handler {
        Handler::Named(_) => {}
        Handler::Inline { items, .. } => {
            for item in items {
                match &mut item.node {
                    HandlerItem::Named(_) => {}
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        push_handler_arm_child_exprs(arm, out);
                    }
                }
            }
        }
    }
}

fn push_handler_body_child_exprs<'e>(body: &'e mut HandlerBody, out: &mut Vec<&'e mut Expr>) {
    for arm in &mut body.arms {
        push_handler_arm_child_exprs(&mut arm.node, out);
    }
}

fn push_handler_arm_child_exprs<'e>(arm: &'e mut HandlerArm, out: &mut Vec<&'e mut Expr>) {
    out.push(&mut arm.body);
    if let Some(fb) = &mut arm.finally_block {
        out.push(fb);
    }
}

