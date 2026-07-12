use super::*;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::*;
use std::collections::{HashSet, VecDeque};

impl<'a> Lowerer<'a> {
    pub(crate) fn collect_top_level_scoped_vars(expr: &CExpr, out: &mut HashSet<String>) {
        match expr {
            CExpr::Let(var, _, body) => {
                out.insert(var.clone());
                Self::collect_top_level_scoped_vars(body, out);
            }
            CExpr::LetRec(_, body) => Self::collect_top_level_scoped_vars(body, out),
            CExpr::Annotated { expr, .. } => Self::collect_top_level_scoped_vars(expr, out),
            _ => {}
        }
    }

    pub(crate) fn collect_var_refs(expr: &CExpr, out: &mut HashSet<String>) {
        let mut bound = HashSet::new();
        Self::collect_free_var_refs(expr, &mut bound, out);
    }

    /// Scope-aware free-variable collector. Tracks which names are locally
    /// bound by `Let`/`Fun`/`LetRec`/`Case` patterns and only records vars
    /// that escape those bindings. Without this, naive walking treats inner
    /// shadowing names (e.g. a handler lambda that rebinds `Conn = _HArg0`)
    /// as references to the outer name, producing spurious dependencies.
    pub(crate) fn collect_free_var_refs(
        expr: &CExpr,
        bound: &mut HashSet<String>,
        out: &mut HashSet<String>,
    ) {
        match expr {
            CExpr::Var(v) => {
                if !bound.contains(v) {
                    out.insert(v.clone());
                }
            }
            CExpr::Lit(_) | CExpr::Nil | CExpr::FunRef(_, _) => {}
            CExpr::Fun(params, body) => {
                let added: Vec<String> = params
                    .iter()
                    .filter(|p| bound.insert((*p).clone()))
                    .cloned()
                    .collect();
                Self::collect_free_var_refs(body, bound, out);
                for p in &added {
                    bound.remove(p);
                }
            }
            CExpr::Let(var, val, body) => {
                Self::collect_free_var_refs(val, bound, out);
                let added = bound.insert(var.clone());
                Self::collect_free_var_refs(body, bound, out);
                if added {
                    bound.remove(var);
                }
            }
            CExpr::Apply(func, args) => {
                Self::collect_free_var_refs(func, bound, out);
                for arg in args {
                    Self::collect_free_var_refs(arg, bound, out);
                }
            }
            CExpr::Call(_, _, args) | CExpr::Tuple(args) | CExpr::Values(args) => {
                for arg in args {
                    Self::collect_free_var_refs(arg, bound, out);
                }
            }
            CExpr::Case(scrutinee, arms) => {
                Self::collect_free_var_refs(scrutinee, bound, out);
                for arm in arms {
                    let mut pat_vars = Vec::new();
                    Self::collect_pat_vars(&arm.pat, &mut pat_vars);
                    let added: Vec<String> = pat_vars
                        .into_iter()
                        .filter(|v| bound.insert(v.clone()))
                        .collect();
                    if let Some(guard) = &arm.guard {
                        Self::collect_free_var_refs(guard, bound, out);
                    }
                    Self::collect_free_var_refs(&arm.body, bound, out);
                    for v in &added {
                        bound.remove(v);
                    }
                }
            }
            CExpr::Cons(head, tail) => {
                Self::collect_free_var_refs(head, bound, out);
                Self::collect_free_var_refs(tail, bound, out);
            }
            CExpr::LetRec(defs, body) => {
                // letrec: all defined names are in scope inside every def and the body
                let added: Vec<String> = defs
                    .iter()
                    .filter_map(|(name, _, _)| {
                        if bound.insert(name.clone()) {
                            Some(name.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                for (_, _, def) in defs {
                    Self::collect_free_var_refs(def, bound, out);
                }
                Self::collect_free_var_refs(body, bound, out);
                for v in &added {
                    bound.remove(v);
                }
            }
            CExpr::Receive(arms, timeout, timeout_body) => {
                for arm in arms {
                    let mut pat_vars = Vec::new();
                    Self::collect_pat_vars(&arm.pat, &mut pat_vars);
                    let added: Vec<String> = pat_vars
                        .into_iter()
                        .filter(|v| bound.insert(v.clone()))
                        .collect();
                    if let Some(guard) = &arm.guard {
                        Self::collect_free_var_refs(guard, bound, out);
                    }
                    Self::collect_free_var_refs(&arm.body, bound, out);
                    for v in &added {
                        bound.remove(v);
                    }
                }
                Self::collect_free_var_refs(timeout, bound, out);
                Self::collect_free_var_refs(timeout_body, bound, out);
            }
            CExpr::Try {
                expr,
                ok_var,
                ok_body,
                catch_vars,
                catch_body,
            } => {
                Self::collect_free_var_refs(expr, bound, out);
                let ok_added = bound.insert(ok_var.clone());
                Self::collect_free_var_refs(ok_body, bound, out);
                if ok_added {
                    bound.remove(ok_var);
                }
                let catch_added: Vec<String> = [&catch_vars.0, &catch_vars.1, &catch_vars.2]
                    .iter()
                    .filter_map(|v| {
                        if bound.insert((*v).clone()) {
                            Some((*v).clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                Self::collect_free_var_refs(catch_body, bound, out);
                for v in &catch_added {
                    bound.remove(v);
                }
            }
            CExpr::Binary(segs) => {
                for seg in segs {
                    match seg {
                        crate::codegen::cerl::CBinSeg::BinaryAll(expr) => {
                            Self::collect_free_var_refs(expr, bound, out);
                        }
                        crate::codegen::cerl::CBinSeg::Segment { value, size, .. } => {
                            Self::collect_free_var_refs(value, bound, out);
                            if let crate::codegen::cerl::BinSegSize::Expr(size_expr) = size {
                                Self::collect_free_var_refs(size_expr, bound, out);
                            }
                        }
                        crate::codegen::cerl::CBinSeg::Byte(_) => {}
                    }
                }
            }
            CExpr::Annotated { expr, .. } => Self::collect_free_var_refs(expr, bound, out),
        }
    }

    pub(crate) fn collect_pat_vars(pat: &CPat, out: &mut Vec<String>) {
        match pat {
            CPat::Var(v) => out.push(v.clone()),
            CPat::Lit(_) | CPat::Wildcard | CPat::Nil => {}
            CPat::Tuple(ps) | CPat::Values(ps) => {
                for p in ps {
                    Self::collect_pat_vars(p, out);
                }
            }
            CPat::Cons(head, tail) => {
                Self::collect_pat_vars(head, out);
                Self::collect_pat_vars(tail, out);
            }
            CPat::Alias(name, inner) => {
                out.push(name.clone());
                Self::collect_pat_vars(inner, out);
            }
            CPat::Binary(segs) => {
                for seg in segs {
                    match seg {
                        crate::codegen::cerl::CBinSeg::BinaryAll(p) => {
                            Self::collect_pat_vars(p, out);
                        }
                        crate::codegen::cerl::CBinSeg::Segment { value, size, .. } => {
                            Self::collect_pat_vars(value, out);
                            if let crate::codegen::cerl::BinSegSize::Expr(_) = size {
                                // size expr is not a binding site
                            }
                        }
                        crate::codegen::cerl::CBinSeg::Byte(_) => {}
                    }
                }
            }
        }
    }

    pub(crate) fn wrap_ready_pending_lets(
        mut body: CExpr,
        pending: &mut VecDeque<PendingLet>,
        bound: &mut HashSet<String>,
    ) -> CExpr {
        let bound_snapshot = bound.clone();
        let mut ready = Vec::new();
        let mut waiting = VecDeque::new();

        while let Some(item) = pending.pop_front() {
            if item.deps.is_subset(&bound_snapshot) {
                ready.push(item);
            } else {
                waiting.push_back(item);
            }
        }

        *pending = waiting;

        for item in ready.into_iter().rev() {
            body = CExpr::Let(item.var, Box::new(item.val), Box::new(body));
        }

        body
    }

    pub(crate) fn place_pending_lets(
        body: CExpr,
        pending: &mut VecDeque<PendingLet>,
        bound: &mut HashSet<String>,
    ) -> CExpr {
        let body = Self::wrap_ready_pending_lets(body, pending, bound);
        match body {
            CExpr::Let(var, val, inner) => {
                bound.insert(var.clone());
                let inner = Self::place_pending_lets(*inner, pending, bound);
                CExpr::Let(var, val, Box::new(inner))
            }
            CExpr::LetRec(defs, body) => {
                let body = Self::place_pending_lets(*body, pending, bound);
                CExpr::LetRec(defs, Box::new(body))
            }
            CExpr::Annotated { expr, line, file } => CExpr::Annotated {
                expr: Box::new(Self::place_pending_lets(*expr, pending, bound)),
                line,
                file,
            },
            other => Self::wrap_ready_pending_lets(other, pending, bound),
        }
    }

    pub(crate) fn attach_scoped_handler_bindings(
        &self,
        result: CExpr,
        condition_bindings: Vec<(String, CExpr)>,
        handler_bindings: Vec<(String, CExpr)>,
    ) -> CExpr {
        let mut relevant_names = HashSet::new();
        Self::collect_top_level_scoped_vars(&result, &mut relevant_names);
        for (var, _) in &condition_bindings {
            relevant_names.insert(var.clone());
        }
        for (var, _) in &handler_bindings {
            relevant_names.insert(var.clone());
        }
        let mut pending: VecDeque<PendingLet> = condition_bindings
            .into_iter()
            .chain(handler_bindings)
            .map(|(var, val)| {
                let mut refs = HashSet::new();
                Self::collect_var_refs(&val, &mut refs);
                let deps = refs
                    .into_iter()
                    .filter(|name| name != &var && relevant_names.contains(name))
                    .collect();
                PendingLet { var, val, deps }
            })
            .collect();

        let mut bound = HashSet::new();
        let output = Self::place_pending_lets(result, &mut pending, &mut bound);
        if pending.is_empty() {
            output
        } else {
            let waiting_on: Vec<String> = pending
                .iter()
                .map(|item| format!("{} -> {:?}", item.var, item.deps))
                .collect();
            panic!(
                "internal lowering error: could not place scoped handler bindings: {}",
                waiting_on.join(", ")
            );
        }
    }

    pub(crate) fn named_return_lambda(&mut self, item: &NamedHandlerItem) -> Option<CExpr> {
        match item {
            NamedHandlerItem::Static { info, .. } => info
                .return_clause
                .as_ref()
                .map(|ret| self.build_return_lambda(ret, info.source_module.as_deref())),
            NamedHandlerItem::Conditional {
                cond_var,
                then_info,
                else_info,
                ..
            } => {
                if then_info.return_clause.is_some() || else_info.return_clause.is_some() {
                    let then_fun = then_info
                        .return_clause
                        .as_ref()
                        .map(|ret| {
                            self.build_return_lambda(ret, then_info.source_module.as_deref())
                        })
                        .unwrap_or_else(|| self.identity_return_lambda());
                    let else_fun = else_info
                        .return_clause
                        .as_ref()
                        .map(|ret| {
                            self.build_return_lambda(ret, else_info.source_module.as_deref())
                        })
                        .unwrap_or_else(|| self.identity_return_lambda());
                    let param = self.fresh();
                    let then_call =
                        CExpr::Apply(Box::new(then_fun), vec![CExpr::Var(param.clone())]);
                    let else_call =
                        CExpr::Apply(Box::new(else_fun), vec![CExpr::Var(param.clone())]);
                    let body = CExpr::Case(
                        Box::new(CExpr::Var(cond_var.clone())),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: then_call,
                            },
                            CArm {
                                pat: CPat::Var("_".to_string()),
                                guard: None,
                                body: else_call,
                            },
                        ],
                    );
                    Some(CExpr::Fun(vec![param], Box::new(body)))
                } else {
                    None
                }
            }
            NamedHandlerItem::Dynamic {
                tuple_var,
                effects,
                has_return,
            } => {
                if *has_return {
                    Some(
                        self.dynamic_return_lambda(
                            tuple_var,
                            self.effect_handler_ops(effects).len(),
                        ),
                    )
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn is_beam_native_handler_canonical(&self, canonical: &str) -> bool {
        self.handler_defs
            .get(canonical)
            .and_then(|info| info.source_module.as_deref())
            .is_some_and(|module| {
                crate::codegen::lower::beam_interop::is_beam_native_handler(module, canonical)
            })
    }

    /// Find a BEAM-native handler that covers the given effect, if any.
    /// Used to satisfy callback-parameter absorbed effects without threading
    /// an explicit handler param: BEAM-native ops are installed as `direct_ops`
    /// so any use inside the lambda body lowers to a direct erlang call.
    pub(crate) fn beam_native_handler_for_effect(&self, effect: &str) -> Option<String> {
        for (canonical, info) in &self.handler_defs {
            let family = crate::typechecker::applied_effect_family(effect);
            if !info
                .effects
                .iter()
                .any(|candidate| crate::typechecker::applied_effect_family(candidate) == family)
            {
                continue;
            }
            if let Some(module) = info.source_module.as_deref()
                && crate::codegen::lower::beam_interop::is_beam_native_handler(module, canonical)
            {
                return Some(canonical.clone());
            }
        }
        None
    }

    pub(crate) fn use_direct_native_fast_path(&self, _canonical: &str) -> bool {
        false
    }
}
