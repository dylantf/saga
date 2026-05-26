//! `App` lowering for the monadic-IR → Core Erlang pipeline.

use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::monadic::ir::Atom;
use crate::codegen::resolve::ResolvedCodegenKind;

use super::atom::uniform_value_arity;
use super::{LowerCtx, Lowerer};

impl<'ctx> Lowerer<'ctx> {
    /// Lower `App { head, args }` under uniform calling convention.
    ///
    /// Every callable receives `(user_args..., _Evidence, _ReturnK)`. The
    /// head and every arg are atomic by ANF; we lower them in place and
    /// emit a saturated `apply`. The evidence comes from the enclosing
    /// scope (`_Evidence` is the current function's evidence param,
    /// available by name). The return continuation is the ambient K name
    /// — `_ReturnK` at function entry, or a `_K{n}` if we are inside a
    /// `Bind`'s value position.
    pub(super) fn lower_app(&mut self, head: &Atom, args: &[Atom], ctx: &LowerCtx) -> CExpr {
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
            return self.lower_panic_or_todo(&name.name, &args[0], ctx);
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
            return self.eta_expand_partial_app(head, args, expected, ctx);
        }

        let head_ce = self.lower_atom(head, ctx);
        let mut call_args: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a, ctx)).collect();
        call_args.push(CExpr::Var(ctx.evidence.clone()));
        call_args.push(CExpr::Var(ctx.return_k.clone()));
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
    fn eta_expand_partial_app(
        &mut self,
        head: &Atom,
        args: &[Atom],
        expected: usize,
        ctx: &LowerCtx,
    ) -> CExpr {
        let missing = expected - args.len();
        let lowered_supplied: Vec<CExpr> = args.iter().map(|a| self.lower_atom(a, ctx)).collect();
        let eta_names: Vec<String> = (0..missing).map(|i| format!("_Eta{}", i)).collect();
        let inner_ev = "_Evidence".to_string();
        let inner_k = "_ReturnK".to_string();
        let head_ce = self.lower_atom(head, ctx);

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
        CExpr::Apply(Box::new(CExpr::Var(ctx.return_k.clone())), vec![lambda])
    }

    /// Emit `call 'erlang':'error'({saga_error, <kind>, Msg, …})` for the
    /// `panic` / `todo` compiler special forms. The old lowerer carries
    /// source-info (module, function, file, line) here; the new path
    /// doesn't yet thread that, so we use empty placeholders — the kind
    /// atom + message string are enough to identify the failure at runtime.
    fn lower_panic_or_todo(&mut self, name: &str, msg_atom: &Atom, ctx: &LowerCtx) -> CExpr {
        let kind_atom = if name == "todo" { "todo" } else { "panic" };
        let msg = if name == "todo" {
            super::util::lower_string_to_binary("not implemented")
        } else {
            self.lower_atom(msg_atom, ctx)
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
}
