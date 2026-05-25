//! Monadic-IR → Core Erlang expression lowering.
//!
//! Sub-step 7b: `Atom → CExpr` lowering for every variant of the `Atom`
//! enum from `monadic-ir-spec.md`. Structural `MExpr` variants are still
//! stubbed; they arrive in sub-step 7c.

use crate::ast::{NodeId, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::monadic::ir::{Atom, MArm, MExpr, MVar};
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};

use super::Lowerer;
use super::exprs_edge::binop_atoms;
use super::pats::lower_param_names;
use super::util::{core_var, lower_lit_atom, lower_string_to_binary, mangle_ctor_atom};

// Name of the function-entry return-continuation variable. Every emitted
// CFunDef binds this as its trailing parameter (after `_Evidence`); the body
// applies it to the function's final value. Kept in sync with `decls.rs`.
pub(super) const RETURN_K_VAR: &str = "_ReturnK";
/// Function-entry evidence-vector parameter name. Kept in sync with
/// `decls.rs`'s [`EVIDENCE_VAR`].
pub(super) const EVIDENCE_VAR: &str = "_Evidence";

impl<'ctx> Lowerer<'ctx> {
    // ---------------------------------------------------------------
    // MExpr lowering (sub-step 7c)
    // ---------------------------------------------------------------

    /// Lower an `MExpr` in tail position relative to the surrounding function/
    /// lambda's return continuation.
    ///
    /// The ambient continuation is read from `self.current_return_k`. Every
    /// computation either passes its result to that K (`Pure`, `App`,
    /// arms of `Case`/`If`) or rebinds K to a fresh continuation that
    /// performs the rest of the work (`Bind`).
    ///
    /// 7c scope: `Pure`, `Bind`, `Let`, `Case`, `If`, `App`. Everything
    /// else panics with a deferred-step message; effect machinery (`Yield`,
    /// `With`, `Resume`) lands in 7d; foreign / builtin ops in 7g.
    pub(super) fn lower_expr(&mut self, expr: &MExpr) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_pure(atom),
            MExpr::Bind { var, value, body } => self.lower_bind(var, value, body),
            MExpr::Let { var, value, body } => self.lower_let(var, value, body),
            MExpr::Case {
                scrutinee, arms, ..
            } => self.lower_case(scrutinee, arms),
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(cond, then_branch, else_branch),
            MExpr::App { head, args, .. } => self.lower_app(head, args),
            MExpr::Yield { op, args, .. } => self.lower_yield(op, args),
            MExpr::With { handler, body, .. } => self.lower_with(handler, body),
            MExpr::Resume { value, .. } => self.lower_resume(value),
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                ..
            } => self.lower_field_access(record, field, record_name.as_deref()),
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                ..
            } => self.lower_record_update(record, fields, record_name.as_deref()),
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => self.lower_dict_method_access(dict, *method_index),
            MExpr::ForeignCall {
                module, func, args, ..
            } => self.lower_foreign_call(module, func, args),
            MExpr::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right),
            MExpr::UnaryMinus { value, .. } => self.lower_unary_minus(value),
            MExpr::BitString { segments, .. } => self.lower_bitstring(segments),
            MExpr::Receive { arms, after, .. } => self.lower_receive(arms, after.as_ref()),
        }
    }

    /// `Resume(atom)` → `apply <current_K>(<atom>)`.
    ///
    /// Under uniform K-threading, `Resume` and `Pure` emit identical CEL
    /// inside a handler arm: in an arm body, `current_return_k` is the arm's
    /// captured `_K_arm{n}` (the continuation of the perform site), so both
    /// `Resume(v)` and `Pure(v)` at the arm's tail call that K with `v`.
    ///
    /// The distinction matters semantically (Resume = "continue at the perform
    /// site"; Pure = "this arm's result value, skipping the perform-site
    /// continuation"), but the slow uniform path collapses them by
    /// construction. Effect optimization (step 11) is where the two diverge:
    /// `TailResumptive` rewrites can fold `Resume(v)` into a direct call,
    /// while `Pure(v)` in arm tail position remains an abort-style return.
    fn lower_resume(&mut self, value: &Atom) -> CExpr {
        let v = self.lower_atom(value);
        self.apply_current_k(v)
    }

    /// `Pure(atom)` → `apply <current_K>(<atom>)`.
    fn lower_pure(&mut self, atom: &Atom) -> CExpr {
        let value = self.lower_atom(atom);
        self.apply_current_k(value)
    }

    /// Apply the in-scope return continuation to a single value.
    pub(super) fn apply_current_k(&self, value: CExpr) -> CExpr {
        CExpr::Apply(
            Box::new(CExpr::Var(self.current_return_k.clone())),
            vec![value],
        )
    }

    /// Lower `Bind { var, value, body }`:
    ///
    /// ```text
    /// let _K{n} = fun (Var) -> <body under outer K>
    /// in <value under _K{n}>
    /// ```
    ///
    /// The body is lowered first so it sees the *current* K. We then mint a
    /// fresh K name, build the continuation closure, swap it in as the
    /// ambient K, and lower the bound `value` under it. The result is a
    /// plain Core Erlang `let` binding the continuation — straightforward
    /// CPS reification.
    fn lower_bind(&mut self, var: &MVar, value: &MExpr, body: &MExpr) -> CExpr {
        let body_ce = self.lower_expr(body);
        let bound_var = core_var(&var.name);
        let k_name = self.fresh_k_name();
        let k_fun = CExpr::Fun(vec![bound_var], Box::new(body_ce));
        let value_ce = self.with_return_k(k_name.clone(), |this| this.lower_expr(value));
        CExpr::Let(k_name, Box::new(k_fun), Box::new(value_ce))
    }

    /// Lower `Let { var, value, body }` — a pure (non-yielding) binder
    /// produced by effect optimization's Bind→Let promotion rewrite.
    ///
    /// 7c restriction: `value` must be `Pure(atom)`. The translator never
    /// emits `Let`, so this restriction is reachable only via hand-built
    /// IR (tests). It is sound at this stage.
    ///
    /// **Deadline: step 10.** The effect-optimization spec's §2 purity
    /// predicate (see `effect-optimization-spec.md`) classifies a much
    /// richer subset as pure — pure `App`, `Case` with all-pure arms, `If`
    /// with both-pure branches, nested `Let`, etc. By the time step 10
    /// (Bind→Let promotion) lands, `Let.value` will routinely be one of
    /// those shapes, and this restriction breaks. The right shape then is
    /// a separate `lower_pure_expr(&self, &MExpr) -> CExpr` defined only
    /// on the pure subset — it returns a direct CExpr value with no
    /// `_ReturnK` threading. `lower_let` becomes
    /// `CExpr::Let(var, lower_pure_expr(value), lower_expr(body))`. That
    /// function is structurally different from `lower_expr` (no K
    /// threading), so it deserves to live separately rather than being
    /// merged in. Don't build it speculatively here — wait for step 10's
    /// optimizer output to drive the cases.
    fn lower_let(&mut self, var: &MVar, value: &MExpr, body: &MExpr) -> CExpr {
        let value_ce = match value {
            MExpr::Pure(atom) => self.lower_atom(atom),
            other => panic!(
                "lower_let: Let value must be Pure(atom) until step 10's Bind→Let promotion lands \
                 and brings a `lower_pure_expr` for the broader pure subset; got {:?}",
                std::mem::discriminant(other)
            ),
        };
        let body_ce = self.lower_expr(body);
        CExpr::Let(core_var(&var.name), Box::new(value_ce), Box::new(body_ce))
    }

    /// Lower `Case { scrutinee, arms }`. By ANF the scrutinee is atomic, so
    /// we lower it inline. Each arm body lowers under the *same* ambient K
    /// — branches share the enclosing continuation, exactly what makes
    /// `case` a tail form rather than a value form.
    ///
    /// Guard semantics, confirmed via typechecker (`infer.rs::check_guard`):
    /// effect calls are forbidden in guards, so a guard MExpr is structurally
    /// pure (no `Yield`, no `Bind`, no `With`, no `Resume`). Pure guards lower
    /// into a `CExpr` placed directly in `CArm.guard`; see
    /// [`lower_guard`](Self::lower_guard) for the supported shape.
    fn lower_case(&mut self, scrutinee: &Atom, arms: &[MArm]) -> CExpr {
        let scrut_ce = self.lower_atom(scrutinee);
        let mut carms: Vec<CArm> = arms.iter().map(|arm| self.lower_arm(arm)).collect();
        // erlc's `bs_start_match3` consistency check requires a wildcard
        // fallthrough on bitstring case-expressions even when the typechecker
        // already proved exhaustiveness. The old lowerer adds one
        // unconditionally when no Var/Wildcard arm is present (see
        // [`lower/exprs.rs:359-368`]); the new path mirrors that.
        let has_total_catchall = arms.iter().any(|arm| {
            arm.guard.is_none() && matches!(&arm.pattern, Pat::Wildcard { .. } | Pat::Var { .. })
        });
        if !has_total_catchall {
            carms.push(CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: self.case_clause_error(),
            });
        }
        CExpr::Case(Box::new(scrut_ce), carms)
    }

    /// Emit a Core Erlang expression that crashes with a `case_clause` error,
    /// used as the body of the synthetic wildcard fallthrough arm. The
    /// typechecker's exhaustiveness check makes this unreachable at runtime;
    /// the arm exists only to satisfy `erlc`'s bitstring-match invariant.
    fn case_clause_error(&self) -> CExpr {
        CExpr::Call(
            "erlang".to_string(),
            "error".to_string(),
            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
        )
    }

    /// Lower a single MArm into a `CArm`. Shared between `Case` and `Receive`.
    pub(super) fn lower_arm(&mut self, arm: &MArm) -> CArm {
        let pat = self.lower_pat(&arm.pattern);
        let guard = arm.guard.as_ref().map(|g| self.lower_guard(g));
        let body = self.lower_expr(&arm.body);
        CArm { pat, guard, body }
    }

    /// Lower a guard MExpr into a `CExpr` suitable for a Core Erlang
    /// `case`/`receive` arm guard position.
    ///
    /// Guards are statically guaranteed pure by the typechecker — see
    /// `src/typechecker/infer.rs::check_guard`, which forbids effect calls.
    /// The MExpr we receive is therefore structurally a subset: `Pure(atom)`,
    /// `BinOp` of atoms, `UnaryMinus` of atom, or `ForeignCall` of a
    /// guard-safe BIF over atoms. Other shapes (Case, If, App, FieldAccess,
    /// RecordUpdate, DictMethodAccess, BitString) are syntactically illegal
    /// in Core Erlang guards anyway — we panic with a clear message rather
    /// than emit invalid CEL.
    fn lower_guard(&mut self, guard: &MExpr) -> CExpr {
        match guard {
            MExpr::Pure(atom) => self.lower_atom(atom),
            MExpr::BinOp {
                op, left, right, ..
            } => {
                let l = self.lower_atom(left);
                let r = self.lower_atom(right);
                binop_atoms(op, l, r)
            }
            MExpr::UnaryMinus { value, .. } => {
                let v = self.lower_atom(value);
                CExpr::Call(
                    "erlang".to_string(),
                    "-".to_string(),
                    vec![CExpr::Lit(CLit::Int(0)), v],
                )
            }
            MExpr::ForeignCall {
                module, func, args, ..
            } => CExpr::Call(
                module.clone(),
                func.clone(),
                args.iter().map(|a| self.lower_atom(a)).collect(),
            ),
            // ANF atomizes sub-expressions in guards too (e.g. `n % 15 == 0`
            // becomes `let v0 = n % 15 in v0 == 0`), and the translator
            // emits a `Bind` for that let. Core Erlang permits `let` in
            // guard position as long as both the bound value and the body
            // are themselves guard expressions, so we recurse into both
            // sides under `lower_guard` and rebuild as a `CExpr::Let`.
            // `Let` (post-Bind→Let promotion) gets the same treatment.
            MExpr::Bind { var, value, body } | MExpr::Let { var, value, body } => {
                let val_ce = self.lower_guard(value);
                let body_ce = self.lower_guard(body);
                CExpr::Let(core_var(&var.name), Box::new(val_ce), Box::new(body_ce))
            }
            other => panic!(
                "lower_guard: guard MExpr variant not legal in Core Erlang guard position: {:?}",
                std::mem::discriminant(other)
            ),
        }
    }

    /// Lower `If { cond, then, else }` to a Core Erlang `case` over the
    /// boolean condition. Both arms lower under the same ambient K — same
    /// shape rule as `Case` arms.
    fn lower_if(&mut self, cond: &Atom, then_branch: &MExpr, else_branch: &MExpr) -> CExpr {
        let cond_ce = self.lower_atom(cond);
        let then_ce = self.lower_expr(then_branch);
        let else_ce = self.lower_expr(else_branch);
        CExpr::Case(
            Box::new(cond_ce),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("true".to_string())),
                    guard: None,
                    body: then_ce,
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("false".to_string())),
                    guard: None,
                    body: else_ce,
                },
            ],
        )
    }

    /// Lower `App { head, args }` under uniform calling convention.
    ///
    /// Every callable receives `(user_args..., _Evidence, _ReturnK)`. The
    /// head and every arg are atomic by ANF; we lower them in place and
    /// emit a saturated `apply`. The evidence comes from the enclosing
    /// scope (`_Evidence` is the current function's evidence param,
    /// available by name). The return continuation is the ambient K name
    /// — `_ReturnK` at function entry, or a `_K{n}` if we are inside a
    /// `Bind`'s value position.
    fn lower_app(&mut self, head: &Atom, args: &[Atom]) -> CExpr {
        // Compiler special forms `panic msg` / `todo msg`: emit a structured
        // error term via `erlang:error` directly, matching the old lowerer's
        // behavior ([lower/mod.rs:3261-3273]). These aren't real functions —
        // `panic` and `todo` have no callable binding anywhere — so the
        // standard `apply <head>(args…, _Evidence, _ReturnK)` shape produces
        // an unbound-variable error at link time. The head atom is an
        // unresolved `Var` ("panic"/"todo") with no entry in `ResolutionMap`.
        if let Atom::Var { name, source } = head
            && self.resolution.get(source).is_none()
            && args.len() == 1
            && (name.name == "panic" || name.name == "todo")
        {
            return self.lower_panic_or_todo(&name.name, &args[0]);
        }

        // Partial application: if the head resolves to a known-arity callable
        // and the call site supplies fewer user/dict args than expected,
        // eta-expand into a closure that captures the supplied args and
        // takes the remaining user/dict args plus the uniform `_Evidence` /
        // `_ReturnK` pair. Under uniform CPS you can't just `Apply` with
        // too few args — `erlc` rejects it as an arity mismatch.
        if let Some(expected) = self.head_atom_expected_user_args(head)
            && args.len() < expected
        {
            return self.eta_expand_partial_app(head, args, expected);
        }

        let head_ce = self.lower_atom(head);
        let mut call_args: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a)).collect();
        call_args.push(CExpr::Var(self.current_evidence.clone()));
        call_args.push(CExpr::Var(self.current_return_k.clone()));
        CExpr::Apply(Box::new(head_ce), call_args)
    }

    /// Number of user/dict args the head atom's callable expects (i.e. the
    /// uniform arity minus the trailing `_Evidence` + `_ReturnK` slots),
    /// when statically known. Returns `None` for opaque heads (local
    /// `Var` binders, `DictRef` to a runtime tuple, etc.) — those skip
    /// partial-app detection and fall through to the saturated path.
    fn head_atom_expected_user_args(&self, head: &Atom) -> Option<usize> {
        let node = match head {
            Atom::Var { source, .. } => *source,
            Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&node)?;
        let (arity, effects): (usize, &[String]) = match &resolved.kind {
            ResolvedCodegenKind::BeamFunction { arity, effects, .. }
            | ResolvedCodegenKind::ExternalFunction { arity, effects, .. } => (*arity, effects),
            ResolvedCodegenKind::Intrinsic { arity, .. } => (*arity, &[]),
            ResolvedCodegenKind::InlineVal => return None,
        };
        let uniform = uniform_value_arity(arity, effects, &resolved.name);
        // Vals (uniform == 0) aren't callables; skip them.
        uniform.checked_sub(2).filter(|&n| n > 0)
    }

    /// Eta-expand a partial application `head(args…)` into a lambda that
    /// closes over `args` and takes the remaining user/dict params plus the
    /// uniform `_Evidence` / `_ReturnK` pair, then forwards everything to
    /// `head` at full arity. The resulting lambda value is yielded through
    /// the ambient return continuation.
    fn eta_expand_partial_app(&mut self, head: &Atom, args: &[Atom], expected: usize) -> CExpr {
        let missing = expected - args.len();
        let lowered_supplied: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a)).collect();
        let eta_names: Vec<String> = (0..missing).map(|i| format!("_Eta{}", i)).collect();
        let inner_ev = "_Evidence".to_string();
        let inner_k = "_ReturnK".to_string();
        let head_ce = self.lower_atom(head);

        let mut full_args: Vec<CExpr> = lowered_supplied;
        full_args.extend(eta_names.iter().map(|n| CExpr::Var(n.clone())));
        full_args.push(CExpr::Var(inner_ev.clone()));
        full_args.push(CExpr::Var(inner_k.clone()));

        let mut lambda_params = eta_names;
        lambda_params.push(inner_ev);
        lambda_params.push(inner_k);

        let inner_apply = CExpr::Apply(Box::new(head_ce), full_args);
        let lambda = CExpr::Fun(lambda_params, Box::new(inner_apply));
        // Yield the lambda value through the current K.
        CExpr::Apply(
            Box::new(CExpr::Var(self.current_return_k.clone())),
            vec![lambda],
        )
    }

    /// Emit `call 'erlang':'error'({saga_error, <kind>, Msg, …})` for the
    /// `panic` / `todo` compiler special forms. The old lowerer carries
    /// source-info (module, function, file, line) here; the new path
    /// doesn't yet thread that, so we use empty placeholders — the kind
    /// atom + message string are enough to identify the failure at runtime.
    fn lower_panic_or_todo(&mut self, name: &str, msg_atom: &Atom) -> CExpr {
        let kind_atom = if name == "todo" { "todo" } else { "panic" };
        let msg = if name == "todo" {
            super::util::lower_string_to_binary("not implemented")
        } else {
            self.lower_atom(msg_atom)
        };
        let msg_var = self.fresh_helper_name();
        let err_term = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("saga_error".to_string())),
            CExpr::Lit(CLit::Atom(kind_atom.to_string())),
            CExpr::Var(msg_var.clone()),
            super::util::lower_string_to_binary(""),
            super::util::lower_string_to_binary(""),
            super::util::lower_string_to_binary(""),
            CExpr::Lit(CLit::Int(0)),
        ]);
        let err_call = CExpr::Call("erlang".to_string(), "error".to_string(), vec![err_term]);
        CExpr::Let(msg_var, Box::new(msg), Box::new(err_call))
    }

    // ---------------------------------------------------------------
    // Atom lowering (sub-step 7b)
    // ---------------------------------------------------------------

    /// Lower an `Atom` to its value-producing `CExpr`. By the ANF/monadic
    /// invariants, an `Atom` is non-effectful and produces a value directly —
    /// no continuation involved. Recursive `Atom` positions (constructor
    /// args, tuple elements, record fields) are lowered in place; there is
    /// no "lift to let" path because those positions are themselves atomic.
    pub(super) fn lower_atom(&mut self, atom: &Atom) -> CExpr {
        match atom {
            Atom::Var { name, source } => self.lower_var_atom(name, *source),
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Ctor { name, args, .. } => self.lower_ctor_atom(name, args),
            Atom::Tuple { elements, .. } => {
                CExpr::Tuple(elements.iter().map(|e| self.lower_atom(e)).collect())
            }
            Atom::AnonRecord { fields, .. } => self.lower_anon_record_atom(fields),
            Atom::Record { name, fields, .. } => self.lower_record_atom(name, fields),
            Atom::Lambda { params, body, .. } => self.lower_lambda_atom(params, body),
            Atom::DictRef { name, source } => self.lower_dict_ref_atom(name, *source),
            Atom::QualifiedRef {
                module,
                name,
                source,
            } => self.lower_qualified_ref_atom(module, name, *source),
            Atom::Symbol { symbol, .. } => lower_string_to_binary(symbol),
        }
    }

    /// Lower an `Atom::Var` reference.
    ///
    /// A bare (unqualified) `Var` in the source AST can refer to either:
    ///   1. A local binding (function param, let binding, lambda param,
    ///      case binding, etc.) — lowered to `core_var(name)`.
    ///   2. A top-level function or imported symbol — must be lowered as
    ///      a function value (`FunRef` / `make_fun`), not a bare Erlang
    ///      variable, or `erlc` rejects with "unbound variable".
    ///
    /// The resolution map is authoritative: if `MVar.source` (the original
    /// AST NodeId of the reference) has a `ResolvedSymbol` entry, this is
    /// case 2 — dispatch through [`lower_resolved_value_ref`] exactly like
    /// the old lowerer's `ExprKind::Var` branch ([lower/mod.rs:3334-3351]).
    /// Otherwise fall back to a bare var.
    fn lower_var_atom(&mut self, mvar: &MVar, source: NodeId) -> CExpr {
        if let Some(resolved) = self.resolution.get(&source).cloned() {
            return self.lower_resolved_value_ref(resolved);
        }
        // Handler-as-value references (`let logger = if dev then console_log
        // else silent_log`) need a real op-tuple value. The new path doesn't
        // yet synthesize one for arbitrary handler names — emit a placeholder
        // `'unit'` atom so `erlc` accepts the module. Any subsequent `with
        // logger body` site then takes the empty-effects Dynamic branch
        // (warning + body-only), making this a clean runtime failure rather
        // than a compile-time block. TODO: synthesize the proper op-tuple
        // (see `lower_handler_def_to_tuple` in the old lowerer for the
        // shape).
        if self.handler_names.contains(&mvar.name) {
            return CExpr::Lit(CLit::Atom("unit".to_string()));
        }
        CExpr::Var(core_var(&mvar.name))
    }

    /// Lower an `Atom::Ctor` — a recursively-atomic constructor application.
    ///
    /// Saga's runtime encoding:
    ///   - `Nil` → `[]`
    ///   - `Cons(h, t)` → `[h | t]`
    ///   - `True` / `False` → bare `'true'` / `'false'` atoms (Erlang native)
    ///   - other nullary BEAM-interop atoms (exit reasons) → bare atoms
    ///     (skipped here — 7b sticks to the common path; sub-step 7g revisits)
    ///   - everything else → `{tag_atom, arg_0, arg_1, ...}` tagged tuple
    fn lower_ctor_atom(&mut self, name: &str, args: &[Atom]) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            let head = self.lower_atom(&args[0]);
            let tail = self.lower_atom(&args[1]);
            return CExpr::Cons(Box::new(head), Box::new(tail));
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems: Vec<CExpr> = Vec::with_capacity(args.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for arg in args {
            elems.push(self.lower_atom(arg));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::AnonRecord` — a structural record with no nominal type.
    ///
    /// Encoding (matches the old lowerer):
    ///   `{tag_atom, field_v_0, field_v_1, ...}` where `tag_atom =
    ///   anon_record_tag(field_names)` and fields are ordered by sorted
    ///   name. Sorting yields a stable representation regardless of source
    ///   field order, which is what makes two anon records with the same
    ///   fields structurally equal at the BEAM level.
    fn lower_anon_record_atom(&mut self, fields: &[(String, Atom)]) -> CExpr {
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let mut elems: Vec<CExpr> = Vec::with_capacity(fields.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for (_, value) in sorted {
            elems.push(self.lower_atom(value));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::Record` — a named record value.
    ///
    /// Encoding (matches the old lowerer):
    ///   `{record_tag, field_v_0, field_v_1, ...}` where the tag is the
    ///   mangled constructor atom (same table used for ADT ctors), and the
    ///   fields are ordered by the record's declared field order.
    ///
    /// **7b limitation.** The old lowerer reads declared field order from
    /// `resolved_record_fields(node_id, name)`, which threads the
    /// `ResolutionMap` + `CheckResult.records`. The new path doesn't yet
    /// have a `CheckResult` borrow on the `Lowerer` (the spec narrows to
    /// `EffectInfo` only). For 7b we honor the source-supplied field
    /// order — the translator preserved the source order — which works
    /// when records are constructed with declaration-order fields. A later
    /// sub-step (likely 7d's record-update work) is the right place to
    /// add a declared-order lookup. Flagged in the step report.
    fn lower_record_atom(&mut self, name: &str, fields: &[(String, Atom)]) -> CExpr {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems: Vec<CExpr> = Vec::with_capacity(fields.len() + 1);
        elems.push(CExpr::Lit(CLit::Atom(tag)));
        for (_, value) in fields {
            elems.push(self.lower_atom(value));
        }
        CExpr::Tuple(elems)
    }

    /// Lower an `Atom::Lambda` — closure value at construction.
    ///
    /// Uniform calling convention: every lambda receives `_Evidence` and
    /// `_ReturnK` after its user params, regardless of whether the body
    /// performs effects. The body is STUBBED in 7b (delegates to
    /// `lower_body_stub`); sub-step 7c replaces the body with real MExpr
    /// lowering.
    ///
    /// Lambda body lowers under a fresh K context: the lambda's `_ReturnK`
    /// param shadows whatever the outer scope's ambient K was. We save the
    /// outer state, reset to the entry-fn defaults (current K = `_ReturnK`,
    /// fresh K counter starts back at zero so nested lambdas get stable
    /// names), lower the body, then restore.
    fn lower_lambda_atom(&mut self, params: &[Pat], body: &MExpr) -> CExpr {
        // Non-Var patterns in lambda params (e.g. `fun (Currency a) -> show a`)
        // need a case-on-tuple-of-args destructure inside the body — same
        // shape as multi-clause fun bindings. `lower_param_names` collapses
        // every non-Var pattern to a fresh `_Arg{i}`, so without this wrap
        // the body's references to the pattern's sub-vars (`a` here) would
        // be unbound at runtime.
        let has_non_var_pat = params.iter().any(|p| !matches!(p, Pat::Var { .. }));
        let mut param_vars: Vec<String> = if has_non_var_pat {
            (0..params.len()).map(|i| format!("_Arg{}", i)).collect()
        } else {
            lower_param_names(params)
        };
        param_vars.push(EVIDENCE_VAR.to_string());
        param_vars.push(RETURN_K_VAR.to_string());
        let saved_k = std::mem::replace(&mut self.current_return_k, RETURN_K_VAR.to_string());
        let saved_counter = std::mem::replace(&mut self.k_counter, 0);
        let saved_ev = std::mem::replace(&mut self.current_evidence, EVIDENCE_VAR.to_string());
        let saved_ev_counter = std::mem::replace(&mut self.ev_counter, 0);
        let saved_arm_k = std::mem::replace(&mut self.arm_k_counter, 0);
        let saved_ret_k = std::mem::replace(&mut self.ret_k_counter, 0);
        let saved_helper = std::mem::replace(&mut self.helper_counter, 0);
        let body_ce_inner = self.lower_expr(body);
        let body_ce = if has_non_var_pat {
            let scrut = CExpr::Tuple(
                (0..params.len())
                    .map(|i| CExpr::Var(format!("_Arg{}", i)))
                    .collect(),
            );
            let pat = CPat::Tuple(params.iter().map(|p| self.lower_pat(p)).collect());
            CExpr::Case(
                Box::new(scrut),
                vec![CArm {
                    pat,
                    guard: None,
                    body: body_ce_inner,
                }],
            )
        } else {
            body_ce_inner
        };
        self.current_return_k = saved_k;
        self.k_counter = saved_counter;
        self.current_evidence = saved_ev;
        self.ev_counter = saved_ev_counter;
        self.arm_k_counter = saved_arm_k;
        self.ret_k_counter = saved_ret_k;
        self.helper_counter = saved_helper;
        CExpr::Fun(param_vars, Box::new(body_ce))
    }

    /// Lower an `Atom::DictRef` — a reference to a trait dictionary value.
    ///
    /// Tries the `ResolutionMap` first (the resolver tags inter-module dict
    /// references with a `BeamFunction`/`ExternalFunction` codegen kind);
    /// otherwise falls back to a local `CExpr::Var`. The fallback covers
    /// dict-parameter variables passed in as function arguments (e.g. the
    /// `sub_a` parameter on a conditional impl like
    /// `Show for List a where {a: Show}`).
    fn lower_dict_ref_atom(&mut self, name: &str, source: NodeId) -> CExpr {
        if let Some(resolved) = self.resolution.get(&source).cloned() {
            // Dict constructors are uniform-shape callables like everything
            // else; `lower_resolved_value_ref` adds the `+2` for
            // `_Evidence`/`_ReturnK` via `uniform_value_arity`.
            return self.lower_resolved_value_ref(resolved);
        }
        CExpr::Var(core_var(name))
    }

    /// Lower an `Atom::QualifiedRef` — a `Module.name` reference used as a
    /// value (not under a call).
    ///
    /// The resolver tags qualified references with the target Erlang module
    /// / function / arity. We dispatch through `lower_resolved_value_ref`
    /// the same way the dict case does. When the resolution map has no
    /// entry, fall back to a bare `core_var(name)`; this preserves the
    /// behavior of the old lowerer's last-resort branch.
    fn lower_qualified_ref_atom(&mut self, _module: &str, name: &str, source: NodeId) -> CExpr {
        if let Some(resolved) = self.resolution.get(&source).cloned() {
            return self.lower_resolved_value_ref(resolved);
        }
        CExpr::Var(core_var(name))
    }

    /// Translate a `ResolvedSymbol` into its value-position `CExpr`.
    ///
    /// Copied from the old lowerer (`lower/mod.rs::lower_resolved_value_ref`)
    /// and stripped to the value-only path the new lowerer needs:
    ///   - `InlineVal` — old-path-only perf optimization; the new path
    ///     gets equivalent perf from effect-optimization (bind-collapse +
    ///     Bind→Let). Hard panic if encountered (see arm body).
    ///   - `Intrinsic` becomes a `FunRef` at its declared arity. Intrinsics
    ///     are direct BIFs / compiler primitives with no Saga wrapper, so the
    ///     uniform-shape +2 expansion does NOT apply to them.
    ///   - `BeamFunction` / `ExternalFunction` references point at a Saga
    ///     function (or its `@external` wrapper) compiled under the uniform
    ///     calling convention: `(user_args..., _Evidence, _ReturnK)`. The
    ///     resolved `arity` is the **source** arity (user-visible parameter
    ///     count) — we add `+2` for evidence + return-K so callers using the
    ///     resulting fun value invoke it with the right number of arguments.
    ///     Arity-0 entries (vals, niladic constants) stay arity-0: those are
    ///     not wrapped in the uniform shape; calling them just yields the
    ///     constant value.
    fn lower_resolved_value_ref(&mut self, resolved: ResolvedSymbol) -> CExpr {
        match resolved.kind {
            ResolvedCodegenKind::InlineVal => {
                panic!(
                    "InlineVal resolution not used in new path — vals are uniformly emitted as \
                     arity-0 constants; this resolution kind should not appear post-translation. \
                     If it does, the translator or backend-resolve is producing stale resolution \
                     info. (canonical_name={})",
                    resolved.canonical_name
                )
            }
            ResolvedCodegenKind::Intrinsic { arity, .. } => {
                // `@builtin` decls are wrapped at their defining module under
                // the uniform calling convention by
                // `lower_builtin_wrapper` (in `decls.rs`). Reference the
                // wrapper at its uniform arity: `make_fun(erlang_mod, name,
                // arity + 2)`. The intrinsic name itself doubles as the
                // wrapper's function name.
                //
                // For intrinsics without a wrapper yet, this still emits a
                // cross-module `make_fun` reference — which will fail at
                // link time. That mirrors the existing behavior (the old
                // `FunRef(name, arity)` failed the same way) and surfaces
                // missing wrappers loudly.
                if let Some(src_mod) = &resolved.source_module {
                    let erlang_mod: String = src_mod.to_lowercase().replace('.', "_");
                    // Intrinsics have no effect annotation; treat them as
                    // pure for the uniform-arity calculation.
                    let uniform = uniform_value_arity(arity, &[], &resolved.name);
                    fun_value_of(erlang_mod, resolved.name, uniform)
                } else {
                    CExpr::FunRef(resolved.name, arity)
                }
            }
            ResolvedCodegenKind::ExternalFunction {
                erlang_mod,
                name,
                arity,
                effects,
                ..
            } => {
                let uniform = uniform_value_arity(arity, &effects, &name);
                // Same-module refs use FunRef — `erlang:make_fun/3` requires
                // the target to be exported, but local @external wrappers
                // for private decls aren't exported. The old lowerer's
                // [`lower_local_fun_ref`] makes the same choice.
                if erlang_mod == self.current_erlang_module {
                    CExpr::FunRef(name, uniform)
                } else {
                    fun_value_of(erlang_mod, name, uniform)
                }
            }
            ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(erlang_mod),
                name,
                arity,
                effects,
                ..
            } => {
                let uniform = uniform_value_arity(arity, &effects, &name);
                if erlang_mod == self.current_erlang_module {
                    CExpr::FunRef(name, uniform)
                } else {
                    fun_value_of(erlang_mod, name, uniform)
                }
            }
            ResolvedCodegenKind::BeamFunction {
                name,
                arity,
                effects,
                ..
            } => CExpr::FunRef(name.clone(), uniform_value_arity(arity, &effects, &name)),
        }
    }
}

/// Map a resolved BEAM/external function reference's arity to the
/// uniform-shape arity at which it is callable.
///
/// The resolver's `arity` field already includes dict-passing params (and,
/// for effectful functions registered by the old-path's
/// `build_imported_fun_scoped`, the `_Evidence` + `_ReturnK` slots — i.e.
/// `+2` is already baked in). For pure functions, the resolver's arity is
/// the source + dict count only; we add `+2` here to reach the uniform
/// shape every Saga-defined callable is emitted under.
///
/// Arity-0 with no effects denotes a top-level val (a constant), which is
/// the only kind of Saga-emitted callable that stays at arity 0. Dict
/// constructors with no where-clause params also resolve with `arity == 0`
/// but emit at arity 2 (uniform `(_Evidence, _ReturnK)`); we detect them
/// by the `__dict_` name prefix used everywhere in elaboration and force
/// the `+2` regardless.
fn uniform_value_arity(arity: usize, effects: &[String], name: &str) -> usize {
    let is_dict_ctor = name.starts_with("__dict_");
    if !effects.is_empty() {
        // Old-path resolution already added `+2` for effectful imports.
        arity
    } else if arity == 0 && !is_dict_ctor {
        // Val constant — stays arity-0.
        0
    } else {
        // Pure function — resolution carries source + dict count only;
        // add `+2` for uniform `(_Evidence, _ReturnK)`.
        arity + 2
    }
}
/// Emit a function value (as an Erlang term) for a known module/function/arity.
///
/// Arity-0 functions reduce to a direct call returning the value; higher
/// arities become an `erlang:make_fun/3` to construct a fun term. Matches
/// the old lowerer's convention.
fn fun_value_of(erlang_mod: String, name: String, arity: usize) -> CExpr {
    if arity == 0 {
        CExpr::Call(erlang_mod, name, vec![])
    } else {
        CExpr::Call(
            "erlang".to_string(),
            "make_fun".to_string(),
            vec![
                CExpr::Lit(CLit::Atom(erlang_mod)),
                CExpr::Lit(CLit::Atom(name)),
                CExpr::Lit(CLit::Int(arity as i64)),
            ],
        )
    }
}
