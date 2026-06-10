//! Phase 4 (generic fold): trait-neutral inlining of *parameterized* known
//! dict-method calls.
//!
//! A statically-known parameterized dictionary chain — e.g. `to_json` dispatched
//! through `__dict_ToJson_Adt(__dict_ToJson_Variant(__dict_ToJson_Leaf(
//! __dict_ToJson_Int)))` — is collapsed by inlining the outer impl's method
//! lambda and β-reducing it against the call arguments. The result is a nested
//! `case` over the argument whose body re-dispatches through the *concrete
//! sub-dictionary*; folding recurses into that until the chain bottoms out at a
//! **nullary** dict call (which Phases 2/3 specialize at lowering) or runs out of
//! fuel (left as an ordinary `element/2` dict call).
//!
//! This removes the intermediate `Adt`/`Variant`/`Leaf`/`Record`/… *dictionary*
//! tuples and `element/2` projections. It does not cancel the `Rep` constructor
//! allocations themselves — that needs the argument to be a known constructor
//! (Phase 5, where `to x` is inlined).
//!
//! ## Local vs. cross-module
//!
//! - **Local impls** (`DictConstructor` in this module's program) are inlined
//!   directly; their references already resolve in this module.
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
//!   and carried cross-module entries override any consumer-scope guess.

use crate::ast::{
    Annotated, CaseArm, ComprehensionQualifier, Decl, Expr, ExprKind, Handler, HandlerArm,
    HandlerBody, HandlerItem, NodeId, Program, Stmt, StringPart,
};
use crate::codegen::resolve::ResolutionMap;
use crate::desugar::{freshen_expr_ids, freshen_pat_ids};
use std::collections::HashMap;

/// Maximum inline-chain depth per call site. A parameterized dict chain deeper
/// than this (a deeply nested record, or a recursive type) bottoms out as an
/// ordinary dict-passing call — correct, just unfused. `Rep` trees are shallow
/// (bounded by field/constructor nesting), so this is generous in practice.
const INLINE_FUEL: u32 = 64;

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

/// Inline parameterized known dict-method calls throughout a module's function
/// and dict-constructor bodies. `externals` supplies cross-module impls; pass an
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

    /// Fold one expression in place: inline an inlinable parameterized
    /// dict-method call at this node, then recurse into children. `fuel` bounds
    /// the inline chain rooted at this node; structural recursion into a sibling
    /// that is not itself inlined preserves the parent's fuel.
    fn fold_expr(&mut self, expr: &mut Expr, fuel: u32) {
        if fuel > 0
            && let Some(inlined) = self.try_inline(expr)
        {
            *expr = inlined;
            for child in child_exprs_mut(expr) {
                self.fold_expr(child, fuel - 1);
            }
            return;
        }
        for child in child_exprs_mut(expr) {
            self.fold_expr(child, fuel);
        }
    }

    /// If `expr` is a saturated call to a parameterized, known dict method,
    /// produce its inlined form (a nested `case` over the arguments whose body
    /// re-dispatches through the concrete sub-dicts). Records carried resolution
    /// when the impl is cross-module. Returns `None` otherwise.
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
        if sub_dicts.is_empty() {
            return None; // Nullary impl — Phases 2/3 specialize this at lowering.
        }

        // Copy out the borrowed ctor fields (all `&'a`) so the `&self.ctors`
        // borrow ends before we mutate `self.carried` below.
        let (dict_params, methods, resolution) = {
            let ctor = self.ctors.get(name.as_str())?;
            (ctor.dict_params, ctor.methods, ctor.resolution)
        };
        if dict_params.len() != sub_dicts.len() {
            return None;
        }
        let method = methods.get(*method_index)?;
        let ExprKind::Lambda { params, body } = &method.kind else {
            return None;
        };
        if params.len() != args.len() {
            return None; // Partial/over-application — leave on the dispatch path.
        }

        // Clone the method body and freshen its NodeIds. For a cross-module
        // body, remap the producer's resolution entries onto the fresh ids so
        // its references lower as direct cross-module calls.
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

        // β-reduce: one single-arm `case` per (param, arg) pair, outermost arg
        // first. Patterns are exhaustive for the dispatched type (the impl method
        // typechecked), so the single arm cannot fail.
        let mut result = new_body;
        for (param, arg) in params.iter().zip(args.iter()).rev() {
            let mut pattern = param.clone();
            freshen_pat_ids(&mut pattern);
            result = Expr::synth(
                expr.span,
                ExprKind::Case {
                    scrutinee: Box::new((*arg).clone()),
                    arms: vec![Annotated::bare(CaseArm {
                        pattern,
                        guard: None,
                        body: result,
                        span: expr.span,
                    })],
                    dangling_trivia: vec![],
                },
            );
        }
        Some(result)
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
