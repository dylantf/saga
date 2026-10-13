use crate::ast::{BinOp, Expr, Lit, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::ir::{CtorRef, FnRef, FnRepr, Val};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;
use crate::token::Span;

impl<'a> Lowerer<'a> {
    /// Lower a value. A child still in AST form goes back through
    /// `lower_expr`, which hands the value forms to the builder.
    pub(crate) fn lower_val(&mut self, val: &Val<'_>) -> CExpr {
        match val {
            Val::Ast(expr) => self.lower_expr(expr),
            Val::Lit(Lit::String(s, kind)) if kind.is_multiline() => {
                lower_string_to_binary(&process_string_escapes(s))
            }
            Val::Lit(Lit::String(s, _)) => lower_string_to_binary(s),
            Val::Lit(lit) => CExpr::Lit(lower_lit(lit)),
            Val::Local(var) | Val::DictParam(var) => CExpr::Var(var.clone()),
            Val::Intrinsic { name, arity } => CExpr::FunRef(name.clone(), *arity),
            Val::Const(target) | Val::Dict(target) => Self::call_fn(target, Vec::new()),
            Val::Fn { target, repr } | Val::LocalFn { target, repr } => {
                self.lower_fn_value(target, *repr)
            }
            Val::HandlerRef(name) => self
                .lower_handler_def_to_tuple(name)
                .expect("a handler reference names a handler definition"),
            Val::Ctor { ctor, args } => match ctor {
                CtorRef::Nil => CExpr::Nil,
                CtorRef::Bool(value) => CExpr::Lit(CLit::Atom(value.to_string())),
                CtorRef::Atom(atom) => CExpr::Lit(CLit::Atom(atom.to_string())),
                CtorRef::Cons => {
                    let head_var = self.fresh();
                    let tail_var = self.fresh();
                    let head_ce = self.lower_val(&args[0]);
                    let tail_ce = self.lower_val(&args[1]);
                    let cons = CExpr::Cons(
                        Box::new(CExpr::Var(head_var.clone())),
                        Box::new(CExpr::Var(tail_var.clone())),
                    );
                    self.wrap_let_bindings(vec![(head_var, head_ce), (tail_var, tail_ce)], cons)
                }
                CtorRef::Tagged(atom) => self.lower_tuple_elems(Some(atom), args),
            },
            Val::CtorFn { ctor, arity } => {
                let params: Vec<String> = (0..*arity).map(|_| self.fresh()).collect();
                let mut fields = params.iter().cloned().map(CExpr::Var);
                let value = match ctor {
                    CtorRef::Cons => CExpr::Cons(
                        Box::new(fields.next().expect("cons head")),
                        Box::new(fields.next().expect("cons tail")),
                    ),
                    CtorRef::Tagged(atom) => CExpr::Tuple(
                        std::iter::once(CExpr::Lit(CLit::Atom(atom.clone())))
                            .chain(fields)
                            .collect(),
                    ),
                    nullary => unreachable!("{nullary:?} takes no fields"),
                };
                CExpr::Fun(params, Box::new(value))
            }
            Val::Tuple(elems) => self.lower_tuple_elems(None, elems),
            Val::Record { tag, arity, fields } => {
                let mut slots: Vec<Option<String>> = vec![None; *arity];
                let mut bindings = Vec::with_capacity(fields.len());
                for (slot, value) in fields {
                    let var = self.fresh();
                    let ce = self.lower_val(value);
                    slots[*slot] = Some(var.clone());
                    bindings.push((var, ce));
                }
                let filled = (slots.into_iter())
                    .map(|var| CExpr::Var(var.expect("a record literal fills every slot")));
                let tuple = std::iter::once(CExpr::Lit(CLit::Atom(tag.clone()))).chain(filled);
                self.wrap_let_bindings(bindings, CExpr::Tuple(tuple.collect()))
            }
            Val::Field { base, slot } => self.lower_element(base, *slot + 2, |_, field| field),
            Val::DictSuper { dict, slot } => self.lower_element(dict, *slot, |_, dict| dict),
            Val::DictMethod {
                dict,
                slot,
                nullary,
                pure_view,
            } => self.lower_element(dict, *slot, |this, method| match pure_view {
                // A method that takes no parameters is stored as a thunk
                // and is never the head of a call: force it here.
                _ if *nullary => CExpr::Apply(Box::new(method), vec![]),
                Some(arity) => this.bare_view_of_function_value(method, *arity),
                None => method,
            }),
        }
    }

    /// `let V = <tuple> in <then>(element(index, V))`, `index` 1-based.
    fn lower_element(
        &mut self,
        tuple: &Val<'_>,
        index: usize,
        then: impl FnOnce(&mut Self, CExpr) -> CExpr,
    ) -> CExpr {
        let var = self.fresh();
        let tuple_ce = self.lower_val(tuple);
        let element = cerl_call(
            "erlang",
            "element",
            vec![CExpr::Lit(CLit::Int(index as i64)), CExpr::Var(var.clone())],
        );
        let body = then(self, element);
        CExpr::Let(var, Box::new(tuple_ce), Box::new(body))
    }

    /// Bind each element to a fresh variable, then build the tuple, tagged
    /// with `tag` when there is one.
    fn lower_tuple_elems(&mut self, tag: Option<&String>, elems: &[Val<'_>]) -> CExpr {
        let mut vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for elem in elems {
            let var = self.fresh();
            let val = self.lower_val(elem);
            vars.push(var.clone());
            bindings.push((var, val));
        }
        let tag = tag.map(|atom| CExpr::Lit(CLit::Atom(atom.clone())));
        let tuple = CExpr::Tuple(
            tag.into_iter()
                .chain(vars.into_iter().map(CExpr::Var))
                .collect(),
        );
        self.wrap_let_bindings(bindings, tuple)
    }

    /// A direct call of a known function.
    pub(crate) fn call_fn(target: &FnRef, args: Vec<CExpr>) -> CExpr {
        match &target.module {
            Some(module) => CExpr::Call(module.clone(), target.name.clone(), args),
            None => {
                let fun = CExpr::FunRef(target.name.clone(), target.abi.expanded_arity());
                CExpr::Apply(Box::new(fun), args)
            }
        }
    }

    /// A known function used as a value: a bare reference when it is pure,
    /// otherwise a closure over the direct call (`named_function_value`).
    fn lower_fn_value(&mut self, target: &FnRef, repr: FnRepr) -> CExpr {
        if repr == FnRepr::Bare {
            let arity = target.abi.expanded_arity();
            return match &target.module {
                Some(module) => cerl_call(
                    "erlang",
                    "make_fun",
                    vec![
                        CExpr::Lit(CLit::Atom(module.clone())),
                        CExpr::Lit(CLit::Atom(target.name.clone())),
                        CExpr::Lit(CLit::Int(arity as i64)),
                    ],
                ),
                None => CExpr::FunRef(target.name.clone(), arity),
            };
        }
        let value = self.named_function_value(&target.abi, target.abi.user_arity, repr);
        let call = Self::call_fn(target, value.call_args.clone());
        value.finish(call)
    }

    /// Build `case rec_var of <{TagVar, ...field pats...}> when 'true' -> body`,
    /// binding the record's tag and its untouched fields so subsequent reads use
    /// `get_tuple_element` (arity proven locally) rather than `erlang:element/2`.
    /// `pat_vars[pos]` is `Some(var)` to bind that field (untouched) or `None`
    /// (a wildcard) when the field is being overwritten and its old value unused.
    pub(crate) fn record_destructure_case(
        rec_var: &str,
        tag_var: &str,
        pat_vars: &[Option<String>],
        body: CExpr,
    ) -> CExpr {
        let mut pats: Vec<CPat> = Vec::with_capacity(pat_vars.len() + 1);
        pats.push(CPat::Var(tag_var.to_string()));
        for pv in pat_vars {
            pats.push(match pv {
                Some(v) => CPat::Var(v.clone()),
                None => CPat::Wildcard,
            });
        }
        CExpr::Case(
            Box::new(CExpr::Var(rec_var.to_string())),
            vec![CArm {
                pat: CPat::Tuple(pats),
                guard: None,
                body,
            }],
        )
    }

    pub(crate) fn lower_binop(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        span: Option<&crate::token::Span>,
    ) -> CExpr {
        match op {
            BinOp::And => return self.lower_short_circuit(left, right, true),
            BinOp::Or => return self.lower_short_circuit(left, right, false),
            _ => {}
        }

        let left_var = self.fresh();
        let right_var = self.fresh();
        let left_ce = self.lower_operand(left, "a binary operator");
        let right_ce = self.lower_operand(right, "a binary operator");
        let call = self.annotate(binop_call(op, &left_var, &right_var), span);

        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Let(
                right_var.clone(),
                Box::new(right_ce),
                Box::new(call),
            )),
        )
    }

    /// `a && b` -> `case a of true -> b; false -> false end`
    /// `a || b` -> `case a of true -> true; false -> b end`
    pub(crate) fn lower_short_circuit(&mut self, left: &Expr, right: &Expr, and: bool) -> CExpr {
        let left_var = self.fresh();
        let left_ce = self.lower_operand(left, "`&&`/`||`");
        let right_ce = self.lower_operand(right, "`&&`/`||`");
        let short_val = CExpr::Lit(CLit::Atom(if and { "false" } else { "true" }.to_string()));
        let (true_arm, false_arm) = if and {
            (right_ce, short_val)
        } else {
            (short_val, right_ce)
        };
        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(left_var)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: true_arm,
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: false_arm,
                    },
                ],
            )),
        )
    }

    /// Apply an optional return continuation to a final value.
    pub(crate) fn apply_return_k_with(&mut self, return_k: Option<CExpr>, val: CExpr) -> CExpr {
        if let Some(k) = return_k {
            let v = self.fresh();
            CExpr::Let(
                v.clone(),
                Box::new(val),
                Box::new(CExpr::Apply(Box::new(k), vec![CExpr::Var(v)])),
            )
        } else {
            val
        }
    }

    /// Bind a pattern to a single variable name, wrapping the body in a
    /// destructuring `case` if the pattern is non-trivial (tuple, constructor, etc.).
    /// Returns `(var_name, body)` where `var_name` is safe to use in a `Let` or `Fun` param.
    pub(crate) fn destructure_pat(&mut self, pat: &Pat, body: CExpr) -> (String, CExpr) {
        self.destructure_pat_inner(pat, body, false, None)
    }

    pub(crate) fn destructure_pat_assert(
        &mut self,
        pat: &Pat,
        body: CExpr,
        span: Span,
    ) -> (String, CExpr) {
        self.destructure_pat_inner(pat, body, true, Some(span))
    }

    pub(crate) fn destructure_pat_inner(
        &mut self,
        pat: &Pat,
        body: CExpr,
        is_assert: bool,
        span: Option<Span>,
    ) -> (String, CExpr) {
        if !is_assert && let Some(var) = pat_binding_var(pat) {
            return (var, body);
        }
        let tmp = self.fresh();
        let cpat = self.lower_pat(pat, &self.constructor_atoms, self.handler_origin_module());
        let mut arms = vec![CArm {
            pat: cpat,
            guard: None,
            body,
        }];
        if is_assert {
            // Add wildcard arm that panics with structured error info
            let msg = lower_string_to_binary("Assertion failed: pattern did not match");
            arms.push(CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: self.make_error(
                    crate::codegen::lower::errors::ErrorKind::AssertFail,
                    msg,
                    span.as_ref(),
                ),
            });
        }
        let wrapped = CExpr::Case(Box::new(CExpr::Var(tmp.clone())), arms);
        (tmp, wrapped)
    }
}
