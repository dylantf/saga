//! Tagged-closure representation for function values (decision D2b in
//! `docs/planning/sound-function-representation.md`).
//!
//! A function value whose own type is effectful is `{'$saga_cps', Fun}`,
//! where `Fun` takes the user arguments followed by evidence and a
//! continuation. A function value whose own type is pure is a bare fun. The
//! body of a tagged closure finds its handlers by tag (an open evidence frame
//! with no static prefix), so a caller passes its own frame unchanged. Named
//! functions keep their direct entry points and positional layout; using one
//! as a value wraps it in a closure that reframes into that layout.

use crate::ast::{Expr, ExprKind, NodeId};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi, ValueRepr, value_repr};
use crate::typechecker::Type;

use super::util::cerl_call;
use super::{EvidenceFrame, Lowerer};

/// Tag of a CPS closure. Must match `saga_runtime:apply_cps/4`.
const CPS_TAG: &str = "$saga_cps";
const RUNTIME_MODULE: &str = "saga_runtime";

/// The evidence ABI of a tagged closure's body: every handler is found by
/// its tag.
pub(crate) fn tag_only_abi() -> EvidenceAbi {
    EvidenceAbi::new(Vec::<String>::new(), true)
}

pub(crate) fn is_tag_only(abi: &EvidenceAbi) -> bool {
    abi.is_open() && abi.static_slots().is_empty()
}

/// `{'$saga_cps', Fun}`.
pub(super) fn tag_cps(fun: CExpr) -> CExpr {
    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(CPS_TAG.to_string())), fun])
}

/// Whether any of the first `supplied` arrows of `ty` carries effects or an
/// open row. Such a call needs evidence and a continuation.
pub(crate) fn consumed_arrows_effectful(ty: &Type, supplied: usize) -> bool {
    let mut current = ty;
    for _ in 0..supplied {
        let Type::Fun(_, ret, row) = current else {
            return false;
        };
        if !row.effects.is_empty() || !row.tails.is_empty() {
            return true;
        }
        current = ret;
    }
    false
}

fn identity_fun(param: String) -> CExpr {
    CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)))
}

/// A named function used as a value, awaiting the direct call it wraps. See
/// [`Lowerer::named_function_value`].
pub(super) struct NamedFunctionValue {
    params: Vec<String>,
    /// Arguments of the direct call to the named function.
    pub(super) call_args: Vec<CExpr>,
    evidence_binding: Option<(String, CExpr)>,
    tagged: bool,
}

impl NamedFunctionValue {
    pub(super) fn finish(self, call: CExpr) -> CExpr {
        let body = match self.evidence_binding {
            Some((var, value)) => CExpr::Let(var, Box::new(value), Box::new(call)),
            None => call,
        };
        let fun = CExpr::Fun(self.params, Box::new(body));
        if self.tagged { tag_cps(fun) } else { fun }
    }
}

fn list_of_vars(vars: &[String]) -> CExpr {
    vars.iter().rev().fold(CExpr::Nil, |tail, var| {
        CExpr::Cons(Box::new(CExpr::Var(var.clone())), Box::new(tail))
    })
}

impl<'a> Lowerer<'a> {
    /// The expression's own type from the complete per-expression table,
    /// against the module whose code is being lowered.
    pub(super) fn value_type(&self, node_id: NodeId) -> Option<Type> {
        let module_name = self.current_semantic_module_name();
        if module_name == self.current_source_module {
            self.check_result
                .expr_types
                .get(&node_id)
                .or_else(|| self.check_result.type_at_node.get(&node_id))
                .cloned()
        } else {
            self.ctx
                .module_semantics(module_name)
                .and_then(|semantics| {
                    semantics
                        .expr_types
                        .get(&node_id)
                        .or_else(|| semantics.type_at_node.get(&node_id))
                        .cloned()
                })
        }
    }

    pub(super) fn value_repr_of(&self, node_id: NodeId) -> Option<ValueRepr> {
        self.value_type(node_id).map(|ty| value_repr(&ty))
    }

    /// Whether a lambda taking `param_count` parameters (after flattening)
    /// is a tagged CPS closure: decided by its own type, never by the type
    /// its context expects. It is tagged when an arrow its own parameters
    /// consume carries effects. A lambda whose parameters only consume pure
    /// arrows is a bare fun even if it returns an effectful function
    /// (`fun n -> { let g = fun x -> op! x; g }`): calling it performs
    /// nothing, and a pure call site could not run a tagged closure. Nodes
    /// synthesized after typechecking have no entry; those fall back to the
    /// classifier's inferred view.
    pub(super) fn lambda_is_tagged(&self, expr: &Expr, param_count: usize) -> bool {
        match self.value_type(expr.id) {
            Some(ty) => consumed_arrows_effectful(&ty, param_count),
            None => {
                // An elaboration-made wrapper such as `fun dict x -> dict.m x`
                // has no type of its own; it is effectful when the call it
                // wraps is.
                let mut body = expr;
                while let ExprKind::Lambda { body: inner, .. } = &body.kind {
                    body = inner.as_ref();
                }
                self.expr_is_effectful_call(body)
                    || super::util::collect_effect_call(body).is_some()
                    || self
                        .planned_function_value(expr.id)
                        .and_then(|plan| plan.inferred())
                        .is_some_and(|abi| abi.evidence.is_some())
            }
        }
    }

    /// A fresh binding of the caller's current evidence frame, passed
    /// unchanged to a tagged closure. Pure code has no frame and passes an
    /// empty one.
    pub(super) fn current_frame_binding(&mut self) -> (String, CExpr) {
        let var = self.fresh();
        let value = match &self.current_evidence {
            Some(frame) => CExpr::Var(frame.var.clone()),
            None => CExpr::Tuple(Vec::new()),
        };
        (var, value)
    }

    /// Call the function value bound to `func_var` at an effectful type:
    ///
    /// ```text
    /// case F of
    ///   <{'$saga_cps', G}> when call 'erlang':'is_function'(G, N + 2) ->
    ///       apply G(A1, ..., AN, Ev, K)
    ///   <_> when 'true' ->
    ///       call 'saga_runtime':'apply_cps'(F, [A1, ..., AN], Ev, K)
    /// end
    /// ```
    ///
    /// Everything referenced must already be bound to a variable.
    pub(super) fn tagged_cps_apply(
        &mut self,
        func_var: &str,
        arg_vars: &[String],
        ev_var: &str,
        k_var: &str,
    ) -> CExpr {
        let inner = self.fresh();
        let mut direct_args: Vec<CExpr> = arg_vars.iter().cloned().map(CExpr::Var).collect();
        direct_args.push(CExpr::Var(ev_var.to_string()));
        direct_args.push(CExpr::Var(k_var.to_string()));
        let direct = CExpr::Apply(Box::new(CExpr::Var(inner.clone())), direct_args);
        let slow = cerl_call(
            RUNTIME_MODULE,
            "apply_cps",
            vec![
                CExpr::Var(func_var.to_string()),
                list_of_vars(arg_vars),
                CExpr::Var(ev_var.to_string()),
                CExpr::Var(k_var.to_string()),
            ],
        );
        CExpr::Case(
            Box::new(CExpr::Var(func_var.to_string())),
            vec![
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Lit(CLit::Atom(CPS_TAG.to_string())),
                        CPat::Var(inner.clone()),
                    ]),
                    guard: Some(cerl_call(
                        "erlang",
                        "is_function",
                        vec![
                            CExpr::Var(inner),
                            CExpr::Lit(CLit::Int(arg_vars.len() as i64 + 2)),
                        ],
                    )),
                    body: direct,
                },
                CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: slow,
                },
            ],
        )
    }

    /// Call a function value of effectful type from code that is itself not
    /// in CPS (a compiler-native bridge such as `spawn` or `catch_panic`):
    /// the given evidence and an identity continuation.
    pub(super) fn tagged_cps_apply_value(
        &mut self,
        func: CExpr,
        args: Vec<CExpr>,
        evidence: CExpr,
    ) -> CExpr {
        let func_var = self.fresh();
        let ev_var = self.fresh();
        let k_var = self.fresh();
        let k_param = self.fresh();
        let mut bindings = vec![(func_var.clone(), func)];
        let mut arg_vars = Vec::with_capacity(args.len());
        for arg in args {
            let var = self.fresh();
            bindings.push((var.clone(), arg));
            arg_vars.push(var);
        }
        bindings.push((ev_var.clone(), evidence));
        bindings.push((k_var.clone(), identity_fun(k_param)));
        let call = self.tagged_cps_apply(&func_var, &arg_vars, &ev_var, &k_var);
        self.wrap_let_bindings(bindings, call)
    }

    /// Plan a named function (or a partial application of one) as a function
    /// value. `abi` is the callee's declared convention and `remaining` the
    /// number of user arguments the value still takes. The caller emits the
    /// direct call from `NamedFunctionValue::call_args` (the remaining user
    /// arguments, plus evidence and continuation for an effectful callee)
    /// and passes it to `NamedFunctionValue::finish`.
    ///
    /// A pure callee stays a bare fun. An effectful one becomes a tagged
    /// closure whose evidence parameter is reframed from the tag-only frame
    /// into the callee's declared layout. When the occurrence's own type is
    /// pure (an open-row callee instantiated at the empty row), the value is
    /// a bare fun that supplies empty evidence, so it can be called at a pure
    /// type like any other pure value.
    pub(super) fn named_function_value(
        &mut self,
        abi: &CallableAbi,
        remaining: usize,
        own_repr: Option<ValueRepr>,
    ) -> NamedFunctionValue {
        let mut params: Vec<String> = Vec::with_capacity(remaining + 2);
        for _ in 0..remaining {
            params.push(self.fresh());
        }
        let mut call_args: Vec<CExpr> = params.iter().cloned().map(CExpr::Var).collect();
        let Some(target) = abi.evidence.as_ref() else {
            return NamedFunctionValue {
                params,
                call_args,
                evidence_binding: None,
                tagged: false,
            };
        };
        if own_repr == Some(ValueRepr::Bare) && target.static_slots().is_empty() {
            let k_param = self.fresh();
            call_args.push(CExpr::Tuple(Vec::new()));
            call_args.push(identity_fun(k_param));
            return NamedFunctionValue {
                params,
                call_args,
                evidence_binding: None,
                tagged: false,
            };
        }
        let saved_evidence = self.current_evidence.take();
        self.current_evidence = Some(EvidenceFrame::new("_Evidence", tag_only_abi()));
        let (ev_var, ev_ce) = self.build_call_evidence_with(target);
        self.current_evidence = saved_evidence;
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());
        call_args.push(CExpr::Var(ev_var.clone()));
        call_args.push(CExpr::Var("_ReturnK".to_string()));
        NamedFunctionValue {
            params,
            call_args,
            evidence_binding: Some((ev_var, ev_ce)),
            tagged: true,
        }
    }

    /// A dictionary method with an open-row-only trait signature (so its slot
    /// holds a tagged closure) taken from a statically known impl whose
    /// method has no effects of its own. The row variable is instantiated to
    /// that impl's effects, so the occurrence's type is pure and the value
    /// must be a bare fun. Returns the number of arguments it takes.
    ///
    /// Elaboration gives `DictMethodAccess` nodes fresh ids, so the
    /// occurrence has no entry in the type table; the impl's recorded method
    /// effects stand in for it.
    pub(super) fn pure_view_of_effectful_method(
        &self,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
    ) -> Option<usize> {
        let method = self.trait_info(trait_name)?.methods.get(method_index)?;
        if !method.effect_sig.effects.is_empty() || !method.effect_sig.is_open_row {
            return None;
        }
        let mut head = dict;
        while let ExprKind::App { func, .. } = &head.kind {
            head = func;
        }
        let ExprKind::DictRef { name, .. } = &head.kind else {
            return None;
        };
        let impl_effects = self
            .impl_method_effects_by_dict
            .get(&(name.clone(), method_index))?;
        impl_effects
            .is_empty()
            .then_some(method.param_types.len())
            .filter(|arity| *arity > 0)
    }

    /// A bare fun of `arity` arguments over a function value that may be a
    /// tagged closure but is used at a pure type. It performs nothing at
    /// that type, so it runs with empty evidence and an identity
    /// continuation.
    pub(super) fn bare_view_of_function_value(&mut self, value: CExpr, arity: usize) -> CExpr {
        let func_var = self.fresh();
        let params: Vec<String> = (0..arity).map(|_| self.fresh()).collect();
        let k_param = self.fresh();
        let call = cerl_call(
            RUNTIME_MODULE,
            "apply_cps",
            vec![
                CExpr::Var(func_var.clone()),
                list_of_vars(&params),
                CExpr::Tuple(Vec::new()),
                identity_fun(k_param),
            ],
        );
        CExpr::Let(
            func_var,
            Box::new(value),
            Box::new(CExpr::Fun(params, Box::new(call))),
        )
    }

    /// A constructor used as a function value: one bare fun taking every
    /// field. Constructors are always pure.
    pub(super) fn constructor_function_value(&mut self, name: &str, arity: usize) -> CExpr {
        let params: Vec<String> = (0..arity).map(|_| self.fresh()).collect();
        let bare = name.rsplit('.').next().unwrap_or(name);
        let value = if bare == "Cons" && arity == 2 {
            CExpr::Cons(
                Box::new(CExpr::Var(params[0].clone())),
                Box::new(CExpr::Var(params[1].clone())),
            )
        } else {
            let atom = super::util::mangle_ctor_atom(
                name,
                &self.constructor_atoms,
                self.handler_origin_module(),
            );
            let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
            elems.extend(params.iter().cloned().map(CExpr::Var));
            CExpr::Tuple(elems)
        };
        CExpr::Fun(params, Box::new(value))
    }

    /// The user arity and convention of `head` when it names a function the
    /// compiler calls directly (a top-level, imported or block-local
    /// function). `None` for everything that is a function *value*.
    pub(super) fn known_named_callee(&self, head: &Expr) -> Option<CallableAbi> {
        if !self.resolved.contains_key(&head.id) {
            return None;
        }
        let info = match &head.kind {
            ExprKind::Var { name, .. } => self.resolved_fun_info(head.id, name)?,
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{module}.{name}");
                self.resolved_fun_info(head.id, &qualified)?
            }
            _ => return None,
        };
        (info.abi.user_arity > 0).then(|| info.abi.clone())
    }
}
