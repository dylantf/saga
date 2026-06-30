use super::*;

/// Inline statically-known dict-method calls throughout a module's function and
/// dict-constructor bodies, then collapse the constructors they expose
/// (constant record projection, β-reduction, case-of-known-constructor).
/// `externals`/`external_funs` supply cross-module impls and carryable plain
/// functions; pass empty maps for local-only folding.
pub fn fold_program(
    program: &Program,
    externals: &ExternalCtors<'_>,
    external_funs: &ExternalFuns<'_>,
) -> FoldOutput {
    let mut ctors: HashMap<&str, CtorView<'_>> = HashMap::new();
    // Externals first; a local impl of the same name (shouldn't happen — dict
    // names are globally unique) would take precedence.
    for (name, ext) in externals {
        ctors.insert(
            name.as_str(),
            CtorView {
                source_module: Some(ext.source_module),
                dict_params: ext.dict_params,
                methods: ext.methods,
                resolution: Some(ext.resolution),
                record_types: Some(ext.record_types),
                constructors: Some(ext.constructors),
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
                    source_module: None,
                    dict_params,
                    methods,
                    resolution: None,
                    record_types: None,
                    constructors: None,
                },
            );
        }
    }

    // The fold only does anything in a module with dict constructors (a deriving
    // module). Keep that short-circuit on `ctors`, so plain-function inlining never
    // forces a fold of a non-deriving module — and `funs` is only built here.
    if ctors.is_empty() {
        return FoldOutput {
            program: program.clone(),
            carried_resolution: ResolutionMap::new(),
            carried_record_types: HashMap::new(),
            carried_constructors: HashMap::new(),
            carried_constructor_names: HashMap::new(),
            carried_names: HashMap::new(),
        };
    }

    // Carryable plain functions: external (carry producer resolution) plus local
    // (resolution by name in this module's scope). Local definitions are bare-name
    // keyed too, so a name carryable both locally and externally, or defined by more
    // than one local clause, is dropped to keep the keying unambiguous.
    let mut funs: HashMap<&str, FunView<'_>> = HashMap::new();
    let mut dropped_funs: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for (name, ext) in external_funs {
        funs.insert(
            name.as_str(),
            FunView {
                source_module: Some(ext.source_module),
                params: ext.params,
                body: ext.body,
                resolution: Some(ext.resolution),
                record_types: Some(ext.record_types),
                constructors: Some(ext.constructors),
            },
        );
    }
    for decl in program {
        if let Some((name, params, body)) = carryable_fun(decl) {
            if dropped_funs.contains(name) {
                continue;
            }
            if funs.remove(name).is_some() {
                dropped_funs.insert(name);
                continue;
            }
            funs.insert(
                name,
                FunView {
                    source_module: None,
                    params,
                    body,
                    resolution: None,
                    record_types: None,
                    constructors: None,
                },
            );
        }
    }

    let mut folder = Folder {
        ctors,
        funs,
        carried: ResolutionMap::new(),
        carried_record_types: HashMap::new(),
        carried_constructors: HashMap::new(),
        carried_constructor_names: HashMap::new(),
        carried_names: HashMap::new(),
    };
    let mut out = program.clone();
    for decl in &mut out {
        folder.fold_decl(decl);
    }
    FoldOutput {
        program: out,
        carried_resolution: folder.carried,
        carried_record_types: folder.carried_record_types,
        carried_constructors: folder.carried_constructors,
        carried_constructor_names: folder.carried_constructor_names,
        carried_names: folder.carried_names,
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
        // Project a field out of a constant record literal: `(Options {…}).field`
        // ⟶ the field value. Exposes `opts.<field>` as a known constructor for the
        // case-collapse below once a constant `opts` is substituted into a codec.
        if let Some(e) = project_record_field(expr) {
            return Some(e);
        }
        // β-reduce a saturated application of a literal lambda. The load-bearing
        // case is `symbol_name`'s reflection closure `(fun __proxy -> "field")(Proxy)`
        // — elaboration emits one per derived record field; reducing it drops the
        // phantom `Proxy` and exposes the literal key (the precondition for folding
        // `apply_name_style` and any later key→iodata fusion).
        if let Some(e) = beta_reduce_lambda_app(expr) {
            return Some(e);
        }
        if let Some(e) = case_of_known_constructor(expr) {
            return Some(e);
        }
        // Inline-to-cancel a dispatch-shaped plain function (e.g. `apply_name_style
        // AsIs "id"`) when a constructor argument makes its body's `case` collapse.
        if let Some(e) = self.try_inline_fun(expr) {
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
            dict, method_index, ..
        } = &head.kind
        else {
            return None;
        };

        let (dict_head, sub_dicts) = peel_app(dict);
        let ExprKind::DictRef { name } = &dict_head.kind else {
            return None; // `Var` head => runtime dict; leave on the dispatch path.
        };

        // Nullary dicts lower to a direct call (Phase 2/3); there is nothing to
        // fuse, so leave them on the dispatch path. Only parameterized dicts
        // (Phase 4a) are inlined here, collapsing the dict chain.
        if sub_dicts.is_empty() {
            return None;
        }

        self.perform_inline(name, &sub_dicts, &args, *method_index)
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
        let (dict_params, methods, resolution, record_types, constructors, source_module) = {
            let ctor = self.ctors.get(name)?;
            (
                ctor.dict_params,
                ctor.methods,
                ctor.resolution,
                ctor.record_types,
                ctor.constructors,
                ctor.source_module,
            )
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

        // Clone the method body and freshen its NodeIds, carrying the producer's
        // resolution for a cross-module body.
        let mut new_body =
            self.freshen_with_carry(body, resolution, record_types, constructors, source_module);

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

    /// Clone `body` and freshen its NodeIds. For a cross-module body
    /// (`resolution: Some`), remap the producer's resolution entries onto the
    /// fresh ids so the body's references (private helpers, other functions) lower
    /// as direct cross-module calls — both id-keyed (`carried`) and name-keyed
    /// (`carried_names`, robust to later re-freshening). For a local body
    /// (`None`), freshening orphans the id-keyed front resolution, but backend
    /// `resolve_names` re-resolves by name in this module's scope, so no carry is
    /// needed. Shared by dict-method and plain-function inlining.
    fn freshen_with_carry(
        &mut self,
        body: &Expr,
        resolution: Option<&ResolutionMap>,
        record_types: Option<&HashMap<NodeId, String>>,
        constructors: Option<&HashMap<NodeId, String>>,
        source_module: Option<&str>,
    ) -> Expr {
        let mut new_body = body.clone();
        match resolution {
            Some(producer_res) => {
                let mut old_ids = Vec::new();
                collect_carried_ids(&mut new_body, &mut old_ids);
                freshen_expr_ids(&mut new_body);
                let mut new_ids = Vec::new();
                collect_carried_ids(&mut new_body, &mut new_ids);
                debug_assert_eq!(
                    old_ids.len(),
                    new_ids.len(),
                    "id collection must be structurally stable across freshening"
                );
                for (old, new) in old_ids.iter().zip(&new_ids) {
                    if let Some(sym) = producer_res.get(old) {
                        // Anchor producer-local `BeamFunction`s (`erlang_mod: None`)
                        // to the producer module so they lower as remote calls in
                        // the consumer instead of unbound variables.
                        let anchored = sym.anchored_to_source_module();
                        if is_fn_ref(&anchored.kind) {
                            self.carried_names
                                .entry(anchored.name.clone())
                                .or_insert_with(|| anchored.clone());
                        }
                        self.carried.insert(*new, anchored);
                    }
                    if let Some(producer_record_types) = record_types
                        && let Some(record_type) = producer_record_types.get(old)
                    {
                        self.carried_record_types.insert(*new, record_type.clone());
                    }
                    if let Some(producer_constructors) = constructors
                        && let Some(constructor) = producer_constructors.get(old)
                    {
                        self.carried_constructors.insert(*new, constructor.clone());
                    } else if let Some(module) = source_module {
                        self.carried_constructors
                            .entry(*new)
                            .or_insert_with(|| format!("{module}.__origin"));
                    }
                }
                if let Some(module) = source_module {
                    let mut ctor_names = Vec::new();
                    collect_constructor_names(&mut new_body, &mut ctor_names);
                    for name in ctor_names {
                        self.carried_constructor_names
                            .entry(name)
                            .or_insert_with(|| module.to_string());
                    }
                }
            }
            None => freshen_expr_ids(&mut new_body),
        }
        new_body
    }

    /// Inline a saturated call to a known dispatch-shaped plain function when an
    /// argument is a literal constructor that makes the function body's `case`
    /// collapse — "inline-to-cancel". The canonical case is `apply_name_style AsIs
    /// "id"`: `apply_name_style`'s body is `case ns { AsIs -> s; … }`, so inlining
    /// it with `ns := AsIs` yields `case AsIs { AsIs -> "id"; … }`, which
    /// [`case_of_known_constructor`] collapses to `"id"` on the next round.
    ///
    /// Tightly gated to avoid bloat / divergence: the function must be in `self.funs`
    /// (only single-clause, guardless, dispatch-shaped, **non-self-recursive**
    /// functions are carried there — see [`carryable_fun`]), fully saturated, and *some*
    /// argument must be a `known_ctor` whose parameter is scrutinized by a `case`
    /// that decides against it ([`body_cancels_with`]). A call whose arg is a
    /// constructor the body doesn't decide on (e.g. `snake_to_camel "id"`) is left
    /// alone. The non-recursive carry filter bounds inlining depth; `INLINE_FUEL`
    /// (the outer per-node budget) backstops any pathological mutual recursion.
    fn try_inline_fun(&mut self, expr: &Expr) -> Option<Expr> {
        let (head, args) = peel_app(expr);
        let name = match &head.kind {
            ExprKind::Var { name } => name.as_str(),
            ExprKind::QualifiedName { name, .. } => base_name(name),
            _ => return None,
        };
        let (params, body, resolution, record_types, constructors, source_module) = {
            let fun = self.funs.get(name)?;
            (
                fun.params,
                fun.body,
                fun.resolution,
                fun.record_types,
                fun.constructors,
                fun.source_module,
            )
        };
        if params.len() != args.len() {
            return None; // Partial/over-application — leave it.
        }
        // The collapse gate: some arg is a literal ctor whose param the body decides
        // on. Reject otherwise so we never inline a call that won't immediately fold.
        let collapses = params.iter().zip(&args).any(|(p, a)| {
            let Pat::Var { name: pname, .. } = p else {
                return false;
            };
            known_ctor(a).is_some_and(|(cname, _)| body_cancels_with(pname, cname, body))
        });
        if !collapses {
            return None;
        }
        let fresh_body =
            self.freshen_with_carry(body, resolution, record_types, constructors, source_module);
        Some(bind_subpats(params, &args, &fresh_body))
    }
}
