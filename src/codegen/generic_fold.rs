//! Phase 4 (Slice 4a): trait-neutral inlining of *parameterized* known
//! dict-method calls — the "generic fold".
//!
//! A statically-known parameterized dictionary chain — e.g.
//! `encode` dispatched through `__dict_Encodable_Adt(__dict_Encodable_Variant(
//! __dict_Encodable_Leaf(__dict_Encodable_Int)))` — is collapsed by inlining the
//! outer impl's method lambda and β-reducing it against the call arguments. The
//! result is a nested `case` over the argument, whose body re-dispatches through
//! the *concrete sub-dictionary*; folding recurses into that until the chain
//! bottoms out at a **nullary** dict call (which Phases 2/3 then specialize at
//! lowering) or runs out of fuel (left as an ordinary `element/2` dict call).
//!
//! This is the dictionary-chain analog of `case_of_known_constructor`: it
//! removes the intermediate `Adt`/`Variant`/`Leaf`/`Record`/… *dictionary*
//! tuples and `element/2` projections. It does **not** cancel the `Rep`
//! constructor allocations themselves — that needs the argument to be a known
//! constructor (Phase 5, where `to x` is inlined).
//!
//! ## Where it runs and why it is safe
//!
//! The pass operates on the elaborated, normalized AST **before** name
//! resolution and before the optimizer/`call_effects` analyses. Inlining a
//! method body is a meaning-preserving β-reduction, so every downstream
//! NodeId-keyed analysis simply recomputes over the rewritten tree — we never
//! hand-thread evidence or effects (Anchor 2: specialization swaps callees, not
//! the effect ABI).
//!
//! Soundness rests on three facts:
//! - Inlined method bodies are cloned with **fresh NodeIds**
//!   ([`freshen_expr_ids`]), so two call sites that inline the same method never
//!   collide in the side tables.
//! - Impl/derive method bodies have **no free local variables** (they reference
//!   only their own params, the `where`-bound dict params we substitute away,
//!   trait methods, and constructors), so reusing the method's parameter names
//!   as `case` binders cannot capture — and the strictly-inward dataflow of a
//!   `Rep` walk makes any name shadowing semantically correct anyway.
//! - Resolution runs *after* the fold, so fresh nodes are resolved fresh.
//!
//! Only **local** dict constructors are inlined (Slice 4a); an imported
//! parameterized impl whose method body is not in this module stays on the
//! dict-passing path.

use crate::ast::{
    Annotated, CaseArm, ComprehensionQualifier, Decl, Expr, ExprKind, Handler, HandlerArm,
    HandlerBody, HandlerItem, Program, Stmt, StringPart,
};
use crate::desugar::{freshen_expr_ids, freshen_pat_ids};
use std::collections::HashMap;

/// Maximum inline-chain depth per call site. A parameterized dict chain deeper
/// than this (a deeply nested record, or a recursive type) bottoms out as an
/// ordinary dict-passing call — correct, just unfused. `Rep` trees are shallow
/// (bounded by field/constructor nesting), so this is generous in practice.
const INLINE_FUEL: u32 = 64;

/// Borrowed view of a local `DictConstructor` decl, for inlining its methods.
struct DictCtor<'a> {
    /// `where`-clause sub-dictionary parameter names, e.g. `__dict_Encodable_a`.
    dict_params: &'a [String],
    /// Method lambdas in trait-declaration order.
    methods: &'a [Expr],
}

/// Inline parameterized known dict-method calls throughout a module's function
/// and dict-constructor bodies. Returns a rewritten copy of `program`.
pub fn fold_program(program: &Program) -> Program {
    let ctors = collect_dict_ctors(program);
    if ctors.is_empty() {
        return program.clone();
    }
    let mut out = program.clone();
    for decl in &mut out {
        fold_decl(decl, &ctors);
    }
    out
}

fn collect_dict_ctors(program: &Program) -> HashMap<&str, DictCtor<'_>> {
    let mut map = HashMap::new();
    for decl in program {
        if let Decl::DictConstructor {
            name,
            dict_params,
            methods,
            ..
        } = decl
        {
            map.insert(
                name.as_str(),
                DictCtor {
                    dict_params,
                    methods,
                },
            );
        }
    }
    map
}

fn fold_decl(decl: &mut Decl, ctors: &HashMap<&str, DictCtor<'_>>) {
    match decl {
        Decl::FunBinding { body, .. } => fold_expr(body, ctors, INLINE_FUEL),
        Decl::DictConstructor { methods, .. } => {
            for method in methods {
                fold_expr(method, ctors, INLINE_FUEL);
            }
        }
        _ => {}
    }
}

/// Fold one expression in place. Tries to inline an inlinable parameterized
/// dict-method call at this node, then recurses into children. `fuel` bounds the
/// inline chain rooted at this node; structural recursion into a sibling that is
/// not itself inlined preserves the parent's fuel.
fn fold_expr(expr: &mut Expr, ctors: &HashMap<&str, DictCtor<'_>>, fuel: u32) {
    if fuel > 0
        && let Some(inlined) = try_inline(expr, ctors)
    {
        *expr = inlined;
        // The inlined node's body re-dispatches through the concrete sub-dict;
        // recurse with decremented fuel so a recursive chain terminates.
        for_each_child_expr_mut(expr, &mut |child| fold_expr(child, ctors, fuel - 1));
        return;
    }
    for_each_child_expr_mut(expr, &mut |child| fold_expr(child, ctors, fuel));
}

/// If `expr` is a saturated call to a parameterized, locally-known dict method,
/// produce its inlined form (a nested `case` over the arguments whose body
/// re-dispatches through the concrete sub-dicts). Returns `None` otherwise.
fn try_inline(expr: &Expr, ctors: &HashMap<&str, DictCtor<'_>>) -> Option<Expr> {
    let (head, args) = peel_app(expr);
    let ExprKind::DictMethodAccess {
        dict, method_index, ..
    } = &head.kind
    else {
        return None;
    };

    // Resolve the dictionary to a known constructor + its sub-dict arguments.
    let (dict_head, sub_dicts) = peel_app(dict);
    let ExprKind::DictRef { name } = &dict_head.kind else {
        return None; // `Var` head => runtime dict; leave on the dispatch path.
    };
    if sub_dicts.is_empty() {
        return None; // Nullary impl — Phases 2/3 specialize this at lowering.
    }

    let ctor = ctors.get(name.as_str())?; // local impls only (Slice 4a).
    if ctor.dict_params.len() != sub_dicts.len() {
        return None; // Arity mismatch we don't understand — stay safe.
    }
    let method = ctor.methods.get(*method_index)?;
    let ExprKind::Lambda { params, body } = &method.kind else {
        return None;
    };
    if params.len() != args.len() {
        return None; // Partial/over-application — leave on the dispatch path.
    }

    // Clone the method body with fresh NodeIds, then substitute the `where`-bound
    // dict params with the concrete sub-dictionaries from this call site.
    let mut new_body = body.as_ref().clone();
    freshen_expr_ids(&mut new_body);
    let subst: HashMap<&str, &Expr> = ctor
        .dict_params
        .iter()
        .map(String::as_str)
        .zip(sub_dicts.iter().copied())
        .collect();
    substitute_dict_vars(&mut new_body, &subst);

    // β-reduce: wrap the body in one single-arm `case` per (param, arg) pair,
    // outermost argument first. A var/wildcard param yields a trivial binding
    // case; a constructor param yields the destructuring the impl method wrote.
    // The patterns are exhaustive for the dispatched type (the typechecker
    // accepted the impl method), so the single arm cannot fail.
    let mut result = new_body;
    for (param, arg) in params.iter().zip(args.iter()).rev() {
        let mut pattern = param.clone();
        freshen_pat_ids(&mut pattern);
        let scrutinee = (*arg).clone();
        result = Expr::synth(
            expr.span,
            ExprKind::Case {
                scrutinee: Box::new(scrutinee),
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

/// Replace every `Var` whose name is a substituted dict param with the
/// corresponding concrete sub-dictionary expression (cloned with fresh ids).
/// Recurses into all child expressions, including `DictMethodAccess.dict`.
fn substitute_dict_vars(expr: &mut Expr, subst: &HashMap<&str, &Expr>) {
    if let ExprKind::Var { name } = &expr.kind
        && let Some(replacement) = subst.get(name.as_str())
    {
        let mut value = (*replacement).clone();
        freshen_expr_ids(&mut value);
        *expr = value;
        return;
    }
    for_each_child_expr_mut(expr, &mut |child| substitute_dict_vars(child, subst));
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

/// Invoke `f` on each direct child expression of `expr`. Unlike
/// [`freshen_expr_ids`], this descends into `DictMethodAccess.dict` (the
/// dictionary sub-expression) so substitution and folding reach it. The match is
/// exhaustive so a newly-added `ExprKind` is a compile error here, not a silent
/// gap.
fn for_each_child_expr_mut(expr: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    match &mut expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}

        ExprKind::DictMethodAccess { dict, .. } => f(dict),

        ExprKind::App { func, arg } => {
            f(func);
            f(arg);
        }
        ExprKind::BinOp { left, right, .. } => {
            f(left);
            f(right);
        }
        ExprKind::UnaryMinus { expr: inner } => f(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            f(cond);
            f(then_branch);
            f(else_branch);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            f(scrutinee);
            for ann_arm in arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    f(g);
                }
                f(&mut ann_arm.node.body);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for ann_stmt in stmts {
                for_each_child_expr_of_stmt_mut(&mut ann_stmt.node, f);
            }
        }
        ExprKind::Lambda { body, .. } => f(body),
        ExprKind::FieldAccess { expr: inner, .. } => f(inner),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, val) in fields {
                f(val);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            f(record);
            for (_, _, val) in fields {
                f(val);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                f(arg);
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            f(inner);
            for_each_child_expr_of_handler_mut(handler, f);
        }
        ExprKind::Resume { value } => f(value),
        ExprKind::HandlerExpr { body } => for_each_child_expr_of_handler_body_mut(body, f),
        ExprKind::Tuple { elements } => {
            for e in elements {
                f(e);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, e) in bindings {
                f(e);
            }
            f(success);
            for ann_arm in else_arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    f(g);
                }
                f(&mut ann_arm.node.body);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann_arm in arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    f(g);
                }
                f(&mut ann_arm.node.body);
            }
            if let Some((timeout, body)) = after_clause {
                f(timeout);
                f(body);
            }
        }
        ExprKind::Ascription { expr: inner, .. } => f(inner),
        ExprKind::BitString { segments } => {
            for seg in segments {
                f(&mut seg.value);
                if let Some(size) = &mut seg.size {
                    f(size);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                f(&mut seg.node);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                f(&mut seg.node);
            }
        }
        ExprKind::Cons { head, tail } => {
            f(head);
            f(tail);
        }
        ExprKind::ListLit { elements } => {
            for e in elements {
                f(e);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    f(e);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            f(body);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Let(_, e)
                    | ComprehensionQualifier::Guard(e) => f(e),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                f(arg);
            }
        }
    }
}

fn for_each_child_expr_of_stmt_mut(stmt: &mut Stmt, f: &mut dyn FnMut(&mut Expr)) {
    match stmt {
        Stmt::Let { value, .. } => f(value),
        Stmt::LetFun { guard, body, .. } => {
            if let Some(g) = guard {
                f(g);
            }
            f(body);
        }
        Stmt::Expr(e) => f(e),
    }
}

fn for_each_child_expr_of_handler_mut(handler: &mut Handler, f: &mut dyn FnMut(&mut Expr)) {
    match handler {
        Handler::Named(_) => {}
        Handler::Inline { items, .. } => {
            for item in items {
                match &mut item.node {
                    HandlerItem::Named(_) => {}
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        for_each_child_expr_of_handler_arm_mut(arm, f);
                    }
                }
            }
        }
    }
}

fn for_each_child_expr_of_handler_body_mut(body: &mut HandlerBody, f: &mut dyn FnMut(&mut Expr)) {
    for arm in &mut body.arms {
        for_each_child_expr_of_handler_arm_mut(&mut arm.node, f);
    }
}

fn for_each_child_expr_of_handler_arm_mut(arm: &mut HandlerArm, f: &mut dyn FnMut(&mut Expr)) {
    f(&mut arm.body);
    if let Some(fb) = &mut arm.finally_block {
        f(fb);
    }
}
