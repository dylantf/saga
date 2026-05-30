// effect_opt/ — monadic IR optimization stage.
//
// Currently implements steps 9-11:
//   - bind collapse — Bind(Pure(a), x, B) → B[x := a]
//   - Bind→Let promotion — pure binders become direct lets
//   - step 11: direct_call.rs     — tail-resumptive Yield → inlined arm body
//
// See docs/planning/uniform-effect-translation/effect-optimization-spec.md
// for rewrite specifications, soundness conditions, and fixpoint strategy.

use crate::ast::{
    ComprehensionQualifier, Expr, ExprKind, Handler, HandlerItem, Pat, Stmt, StringPart,
};
use crate::codegen::handler_analysis::{HandlerAnalysis, ResumptionKind};
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, MArm, MDecl, MDictConstructor, MExpr, MFunBinding, MHandler, MHandlerArm,
    MProgram, MVal, MVar,
};
use crate::typechecker;
use std::collections::HashSet;

/// Run the effect-optimization stage with default options.
pub fn run(m: MProgram, h: &HandlerAnalysis, e: &EffectInfo) -> MProgram {
    run_with_options(m, h, e, RunOptions::default())
}

/// Run the effect-optimization stage with caller-supplied options.
///
/// With `skip`, this returns the monadic program unchanged. Otherwise it runs
/// the currently-enabled optimizer rewrites.
pub fn run_with_options(
    m: MProgram,
    h: &HandlerAnalysis,
    e: &EffectInfo,
    opts: RunOptions,
) -> MProgram {
    if opts.skip {
        return m;
    }

    let mut optimizer = Optimizer::new(opts, h, e);
    optimizer.optimize_program(m)
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RunOptions {
    /// Emit no-op even after rewrites land. Useful for benchmarking and
    /// bisecting miscompiles between the translator and the optimizer.
    pub skip: bool,
}

struct Optimizer<'info, 'data> {
    opts: RunOptions,
    handler_analysis: &'info HandlerAnalysis,
    effect_info: &'info EffectInfo<'data>,
    handler_stack: Vec<HandlerFrame>,
}

#[derive(Debug, Clone)]
enum HandlerFrame {
    Static {
        effects: Vec<String>,
        arms: Vec<MHandlerArm>,
    },
    Blocking {
        effects: Vec<String>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Change {
    Unchanged,
    Changed,
}

impl Change {
    fn mark_if(&mut self, other: Change) {
        if other == Change::Changed {
            *self = Change::Changed;
        }
    }
}

#[derive(Debug)]
struct SubstOutcome<T> {
    value: T,
    changed: bool,
    blocked: bool,
}

impl<T> SubstOutcome<T> {
    fn unchanged(value: T) -> Self {
        Self {
            value,
            changed: false,
            blocked: false,
        }
    }

    fn changed(value: T) -> Self {
        Self {
            value,
            changed: true,
            blocked: false,
        }
    }

    fn blocked(value: T) -> Self {
        Self {
            value,
            changed: false,
            blocked: true,
        }
    }
}

impl<'info, 'data> Optimizer<'info, 'data> {
    fn new(
        opts: RunOptions,
        handler_analysis: &'info HandlerAnalysis,
        effect_info: &'info EffectInfo<'data>,
    ) -> Self {
        Self {
            opts,
            handler_analysis,
            effect_info,
            handler_stack: Vec::new(),
        }
    }

    fn optimize_program(&mut self, mut program: MProgram) -> MProgram {
        let mut changed = true;
        while changed {
            changed = false;
            program = program
                .into_iter()
                .map(|decl| {
                    let (decl, ch) = self.optimize_decl(decl);
                    changed |= ch == Change::Changed;
                    decl
                })
                .collect();
        }
        program
    }

    fn optimize_decl(&mut self, decl: MDecl) -> (MDecl, Change) {
        match decl {
            MDecl::FunBinding(f) => {
                let (guard, guard_change) = optimize_optional_expr_with(self, f.guard);
                let (body, body_change) = self.optimize_expr(f.body);
                let mut change = guard_change;
                change.mark_if(body_change);
                (MDecl::FunBinding(MFunBinding { guard, body, ..f }), change)
            }
            MDecl::Val(v) => {
                let (value, change) = self.optimize_expr(v.value);
                (MDecl::Val(MVal { value, ..v }), change)
            }
            MDecl::DictConstructor(d) => {
                let mut change = Change::Unchanged;
                let methods = d
                    .methods
                    .into_iter()
                    .map(|method| {
                        let (method, ch) = self.optimize_expr(method);
                        change.mark_if(ch);
                        method
                    })
                    .collect();
                (
                    MDecl::DictConstructor(MDictConstructor { methods, ..d }),
                    change,
                )
            }
            MDecl::Passthrough(_) => (decl, Change::Unchanged),
        }
    }

    fn optimize_expr(&mut self, expr: MExpr) -> (MExpr, Change) {
        let (expr, child_change) = self.optimize_children(expr);
        let (expr, direct_change) = self.try_direct_call(expr);
        let (expr, collapse_change) = self.try_bind_collapse(expr);
        let (expr, let_change) = self.try_bind_to_let(expr);
        let mut change = child_change;
        change.mark_if(direct_change);
        change.mark_if(collapse_change);
        change.mark_if(let_change);
        (expr, change)
    }

    fn optimize_children(&mut self, expr: MExpr) -> (MExpr, Change) {
        match expr {
            MExpr::Pure(atom) => {
                let (atom, change) = self.optimize_atom(atom);
                (MExpr::Pure(atom), change)
            }
            MExpr::Yield { op, args, source } => {
                let (args, change) = self.optimize_atoms(args);
                (MExpr::Yield { op, args, source }, change)
            }
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => {
                let (value, value_change) = self.optimize_expr(*value);
                let (body, body_change) = self.optimize_expr(*body);
                let mut change = value_change;
                change.mark_if(body_change);
                (
                    MExpr::Bind {
                        var,
                        value: Box::new(value),
                        body: Box::new(body),
                        mode,
                    },
                    change,
                )
            }
            MExpr::Let { var, value, body } => {
                let (value, value_change) = self.optimize_expr(*value);
                let (body, body_change) = self.optimize_expr(*body);
                let mut change = value_change;
                change.mark_if(body_change);
                (
                    MExpr::Let {
                        var,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    change,
                )
            }
            MExpr::Case {
                scrutinee,
                arms,
                source,
            } => {
                let (scrutinee, mut change) = self.optimize_atom(scrutinee);
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                (
                    MExpr::Case {
                        scrutinee,
                        arms,
                        source,
                    },
                    change,
                )
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                source,
            } => {
                let (cond, cond_change) = self.optimize_atom(cond);
                let (then_branch, then_change) = self.optimize_expr(*then_branch);
                let (else_branch, else_change) = self.optimize_expr(*else_branch);
                let mut change = cond_change;
                change.mark_if(then_change);
                change.mark_if(else_change);
                (
                    MExpr::If {
                        cond,
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                        source,
                    },
                    change,
                )
            }
            MExpr::App { head, args, source } => {
                let (head, head_change) = self.optimize_atom(head);
                let (args, args_change) = self.optimize_atoms(args);
                let mut change = head_change;
                change.mark_if(args_change);
                (MExpr::App { head, args, source }, change)
            }
            MExpr::With {
                handler,
                body,
                source,
            } => {
                let (handler, handler_change) = self.optimize_handler_with_cleared_stack(handler);
                let frame = handler_frame(&handler);
                let (body, body_change) = if let Some(frame) = frame {
                    self.optimize_expr_with_frame(*body, frame)
                } else {
                    self.optimize_expr(*body)
                };
                let mut change = handler_change;
                change.mark_if(body_change);
                (
                    MExpr::With {
                        handler,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            MExpr::Resume { value, source } => {
                let (value, change) = self.optimize_atom(value);
                (MExpr::Resume { value, source }, change)
            }
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                source,
            } => {
                let (record, change) = self.optimize_atom(record);
                (
                    MExpr::FieldAccess {
                        record,
                        field,
                        record_name,
                        anon_fields,
                        source,
                    },
                    change,
                )
            }
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                anon_fields,
                source,
            } => {
                let (record, record_change) = self.optimize_atom(record);
                let (fields, fields_change) = self.optimize_field_atoms(fields);
                let mut change = record_change;
                change.mark_if(fields_change);
                (
                    MExpr::RecordUpdate {
                        record,
                        fields,
                        record_name,
                        anon_fields,
                        source,
                    },
                    change,
                )
            }
            MExpr::DictMethodAccess {
                dict,
                trait_name,
                method_index,
                source,
            } => {
                let (dict, change) = self.optimize_atom(dict);
                (
                    MExpr::DictMethodAccess {
                        dict,
                        trait_name,
                        method_index,
                        source,
                    },
                    change,
                )
            }
            MExpr::ForeignCall {
                module,
                func,
                args,
                source,
            } => {
                let (args, change) = self.optimize_atoms(args);
                (
                    MExpr::ForeignCall {
                        module,
                        func,
                        args,
                        source,
                    },
                    change,
                )
            }
            MExpr::BinOp {
                op,
                left,
                right,
                source,
            } => {
                let (left, left_change) = self.optimize_atom(left);
                let (right, right_change) = self.optimize_atom(right);
                let mut change = left_change;
                change.mark_if(right_change);
                (
                    MExpr::BinOp {
                        op,
                        left,
                        right,
                        source,
                    },
                    change,
                )
            }
            MExpr::UnaryMinus { value, source } => {
                let (value, change) = self.optimize_atom(value);
                (MExpr::UnaryMinus { value, source }, change)
            }
            MExpr::BitString { segments, source } => {
                let mut change = Change::Unchanged;
                let segments = segments
                    .into_iter()
                    .map(|mut seg| {
                        let (value, value_change) = self.optimize_atom(seg.value);
                        seg.value = value;
                        change.mark_if(value_change);
                        if let Some(size) = seg.size {
                            let (size, size_change) = self.optimize_atom(size);
                            seg.size = Some(size);
                            change.mark_if(size_change);
                        }
                        seg
                    })
                    .collect();
                (MExpr::BitString { segments, source }, change)
            }
            MExpr::Receive {
                arms,
                after,
                source,
            } => {
                let mut change = Change::Unchanged;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                let after = after.map(|(timeout, body)| {
                    let (timeout, timeout_change) = self.optimize_atom(timeout);
                    let (body, body_change) = self.optimize_expr(*body);
                    change.mark_if(timeout_change);
                    change.mark_if(body_change);
                    (timeout, Box::new(body))
                });
                (
                    MExpr::Receive {
                        arms,
                        after,
                        source,
                    },
                    change,
                )
            }
            MExpr::LetFun {
                name,
                params,
                body,
                rest,
                source,
            } => {
                let (body, body_change) = self.optimize_expr_with_cleared_stack(*body);
                let (rest, rest_change) = self.optimize_expr(*rest);
                let mut change = body_change;
                change.mark_if(rest_change);
                (
                    MExpr::LetFun {
                        name,
                        params,
                        body: Box::new(body),
                        rest: Box::new(rest),
                        source,
                    },
                    change,
                )
            }
            MExpr::HandlerValue {
                effects,
                arms,
                return_clause,
                source,
            } => {
                let mut change = Change::Unchanged;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_handler_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                let return_clause = return_clause.map(|arm| {
                    let (arm, ch) = self.optimize_handler_arm(*arm);
                    change.mark_if(ch);
                    Box::new(arm)
                });
                (
                    MExpr::HandlerValue {
                        effects,
                        arms,
                        return_clause,
                        source,
                    },
                    change,
                )
            }
        }
    }

    fn try_bind_collapse(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.bind_collapse() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Bind {
            var,
            value,
            body,
            mode,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        let MExpr::Pure(atom) = *value else {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        };

        let free_names = free_atom_names(&atom);
        let substituted = subst_expr(*body, &var, &atom, &free_names);
        if substituted.blocked {
            (
                MExpr::Bind {
                    var,
                    value: Box::new(MExpr::Pure(atom)),
                    body: Box::new(substituted.value),
                    mode,
                },
                Change::Unchanged,
            )
        } else {
            (substituted.value, Change::Changed)
        }
    }

    fn try_bind_to_let(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.bind_to_let() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Bind {
            var,
            value,
            body,
            mode,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        if self.expr_is_pure(&value) {
            (MExpr::Let { var, value, body }, Change::Changed)
        } else {
            (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            )
        }
    }

    fn expr_is_pure(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(_) => true,
            MExpr::Let { value, body, .. } => self.expr_is_pure(value) && self.expr_is_pure(body),
            MExpr::Case { arms, .. } => arms.iter().all(|arm| {
                arm.guard.as_ref().is_none_or(|g| self.expr_is_pure(g))
                    && self.expr_is_pure(&arm.body)
            }),
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => self.expr_is_pure(then_branch) && self.expr_is_pure(else_branch),
            MExpr::App { head, .. } => self.app_is_pure(head),
            MExpr::FieldAccess { .. }
            | MExpr::RecordUpdate { .. }
            | MExpr::DictMethodAccess { .. }
            | MExpr::BinOp { .. }
            | MExpr::UnaryMinus { .. }
            | MExpr::BitString { .. } => true,
            MExpr::Yield { .. }
            | MExpr::Bind { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::ForeignCall { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
        }
    }

    fn app_is_pure(&self, head: &Atom) -> bool {
        match head {
            Atom::Var { name, source } => {
                if let Some(effects) = self.effect_info.let_effect_bindings.get(&name.name) {
                    return effects.is_empty();
                }
                self.effect_info
                    .type_at_node
                    .get(source)
                    .is_some_and(fun_type_effects_are_empty)
            }
            Atom::QualifiedRef {
                module,
                name,
                source,
            } => {
                let canonical = format!("{module}.{name}");
                self.effect_info
                    .fun_effects
                    .get(&canonical)
                    .or_else(|| self.effect_info.fun_effects.get(name))
                    .is_some_and(|effects| effects.is_empty())
                    || self
                        .effect_info
                        .type_at_node
                        .get(source)
                        .is_some_and(fun_type_effects_are_empty)
            }
            Atom::Lambda { source, .. } => self
                .effect_info
                .type_at_node
                .get(source)
                .is_some_and(fun_type_effects_are_empty),
            _ => false,
        }
    }

    fn optimize_arm(&mut self, arm: MArm) -> (MArm, Change) {
        let (guard, guard_change) = optimize_optional_expr_with(self, arm.guard);
        let (body, body_change) = self.optimize_expr(arm.body);
        let mut change = guard_change;
        change.mark_if(body_change);
        (MArm { guard, body, ..arm }, change)
    }

    fn optimize_handler(&mut self, handler: MHandler) -> (MHandler, Change) {
        match handler {
            MHandler::Static {
                effects,
                arms,
                return_clause,
                source,
            } => {
                let mut change = Change::Unchanged;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_handler_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                let return_clause = return_clause.map(|arm| {
                    let (arm, ch) = self.optimize_handler_arm(arm);
                    change.mark_if(ch);
                    arm
                });
                (
                    MHandler::Static {
                        effects,
                        arms,
                        return_clause,
                        source,
                    },
                    change,
                )
            }
            MHandler::Native { .. } => (handler, Change::Unchanged),
            MHandler::Composite { handlers, source } => {
                let mut change = Change::Unchanged;
                let handlers = handlers
                    .into_iter()
                    .map(|handler| {
                        let (handler, ch) = self.optimize_handler(handler);
                        change.mark_if(ch);
                        handler
                    })
                    .collect();
                (MHandler::Composite { handlers, source }, change)
            }
            MHandler::Dynamic {
                effects,
                op_tuple,
                return_lambda,
                source,
            } => {
                let (op_tuple, op_change) = self.optimize_atom(op_tuple);
                let (return_lambda, return_change) =
                    optimize_optional_atom_with(self, return_lambda);
                let mut change = op_change;
                change.mark_if(return_change);
                (
                    MHandler::Dynamic {
                        effects,
                        op_tuple,
                        return_lambda,
                        source,
                    },
                    change,
                )
            }
        }
    }

    fn optimize_handler_arm(&mut self, arm: MHandlerArm) -> (MHandlerArm, Change) {
        let (body, body_change) = self.optimize_expr(*arm.body);
        let (finally_block, finally_change) =
            optimize_optional_boxed_expr_with(self, arm.finally_block);
        let mut change = body_change;
        change.mark_if(finally_change);
        (
            MHandlerArm {
                body: Box::new(body),
                finally_block,
                ..arm
            },
            change,
        )
    }

    fn optimize_atom(&mut self, atom: Atom) -> (Atom, Change) {
        match atom {
            Atom::Ctor { name, args, source } => {
                let (args, change) = self.optimize_atoms(args);
                (Atom::Ctor { name, args, source }, change)
            }
            Atom::Tuple { elements, source } => {
                let (elements, change) = self.optimize_atoms(elements);
                (Atom::Tuple { elements, source }, change)
            }
            Atom::AnonRecord { fields, source } => {
                let (fields, change) = self.optimize_field_atoms(fields);
                (Atom::AnonRecord { fields, source }, change)
            }
            Atom::Record {
                name,
                fields,
                source,
            } => {
                let (fields, change) = self.optimize_field_atoms(fields);
                (
                    Atom::Record {
                        name,
                        fields,
                        source,
                    },
                    change,
                )
            }
            Atom::Lambda {
                params,
                body,
                source,
            } => {
                let (body, change) = self.optimize_expr_with_cleared_stack(*body);
                (
                    Atom::Lambda {
                        params,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. } => (atom, Change::Unchanged),
        }
    }

    fn optimize_atoms(&mut self, atoms: Vec<Atom>) -> (Vec<Atom>, Change) {
        let mut change = Change::Unchanged;
        let atoms = atoms
            .into_iter()
            .map(|atom| {
                let (atom, ch) = self.optimize_atom(atom);
                change.mark_if(ch);
                atom
            })
            .collect();
        (atoms, change)
    }

    fn optimize_field_atoms(
        &mut self,
        fields: Vec<(String, Atom)>,
    ) -> (Vec<(String, Atom)>, Change) {
        let mut change = Change::Unchanged;
        let fields = fields
            .into_iter()
            .map(|(name, atom)| {
                let (atom, ch) = self.optimize_atom(atom);
                change.mark_if(ch);
                (name, atom)
            })
            .collect();
        (fields, change)
    }

    fn optimize_handler_with_cleared_stack(&mut self, handler: MHandler) -> (MHandler, Change) {
        let saved = std::mem::take(&mut self.handler_stack);
        let out = self.optimize_handler(handler);
        self.handler_stack = saved;
        out
    }

    fn optimize_expr_with_cleared_stack(&mut self, expr: MExpr) -> (MExpr, Change) {
        let saved = std::mem::take(&mut self.handler_stack);
        let out = self.optimize_expr(expr);
        self.handler_stack = saved;
        out
    }

    fn optimize_expr_with_frame(&mut self, expr: MExpr, frame: HandlerFrame) -> (MExpr, Change) {
        self.handler_stack.push(frame);
        let out = self.optimize_expr(expr);
        self.handler_stack.pop();
        out
    }

    fn try_direct_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.direct_call() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Yield { op, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some(arm) = self.resolve_direct_call_arm(&op) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        let Some(inlined) = inline_tail_resumptive_arm(arm, &args) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        (rewrite_resumes_to_pure(inlined), Change::Changed)
    }

    fn resolve_direct_call_arm(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&MHandlerArm> {
        for frame in self.handler_stack.iter().rev() {
            match frame {
                HandlerFrame::Static { effects, arms }
                    if effects.iter().any(|e| e == &op.effect) =>
                {
                    let mut matching = arms
                        .iter()
                        .filter(|arm| arm.op.effect == op.effect && arm.op.op == op.op);
                    let arm = matching.next()?;
                    if matching.next().is_some() {
                        return None;
                    }
                    if arm.finally_block.is_some() {
                        return None;
                    }
                    if expr_contains_yield(&arm.body) {
                        return None;
                    }
                    if self.handler_analysis.resumption.get(&arm.id)
                        != Some(&ResumptionKind::TailResumptive)
                    {
                        return None;
                    }
                    return Some(arm);
                }
                HandlerFrame::Static { effects, .. } if effects.iter().any(|e| e == &op.effect) => {
                    return None;
                }
                HandlerFrame::Blocking { effects } if effects.iter().any(|e| e == &op.effect) => {
                    return None;
                }
                _ => {}
            }
        }
        None
    }
}

impl RunOptions {
    fn bind_collapse(self) -> bool {
        !self.skip
    }

    fn bind_to_let(self) -> bool {
        !self.skip
    }

    fn direct_call(self) -> bool {
        !self.skip
    }
}

fn optimize_optional_expr_with(
    optimizer: &mut Optimizer,
    expr: Option<MExpr>,
) -> (Option<MExpr>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr(expr);
            (Some(expr), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn optimize_optional_boxed_expr_with(
    optimizer: &mut Optimizer,
    expr: Option<Box<MExpr>>,
) -> (Option<Box<MExpr>>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr(*expr);
            (Some(Box::new(expr)), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn optimize_optional_atom_with(
    optimizer: &mut Optimizer,
    atom: Option<Atom>,
) -> (Option<Atom>, Change) {
    match atom {
        Some(atom) => {
            let (atom, change) = optimizer.optimize_atom(atom);
            (Some(atom), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn fun_type_effects_are_empty(ty: &typechecker::Type) -> bool {
    match ty {
        typechecker::Type::Fun(_, ret, row) => {
            row.is_empty()
                && (!matches!(ret.as_ref(), typechecker::Type::Fun(_, _, _))
                    || fun_type_effects_are_empty(ret))
        }
        _ => false,
    }
}

fn handler_frame(handler: &MHandler) -> Option<HandlerFrame> {
    match handler {
        MHandler::Static { effects, arms, .. } => {
            let effects = static_frame_effects(effects, arms);
            if effects.is_empty() {
                None
            } else {
                Some(HandlerFrame::Static {
                    effects,
                    arms: arms.clone(),
                })
            }
        }
        MHandler::Dynamic { effects, .. } | MHandler::Native { effects, .. } => {
            blocking_frame(effects.clone())
        }
        MHandler::Composite { handlers, .. } => {
            let mut effects = Vec::new();
            for handler in handlers {
                collect_handler_effects(handler, &mut effects);
            }
            blocking_frame(effects)
        }
    }
}

fn static_frame_effects(effects: &[String], arms: &[MHandlerArm]) -> Vec<String> {
    let mut out = Vec::new();
    for effect in effects {
        push_unique_effect(&mut out, effect);
    }
    for arm in arms {
        push_unique_effect(&mut out, &arm.op.effect);
    }
    out
}

fn collect_handler_effects(handler: &MHandler, out: &mut Vec<String>) {
    match handler {
        MHandler::Static { effects, arms, .. } => {
            for effect in static_frame_effects(effects, arms) {
                push_unique_effect(out, &effect);
            }
        }
        MHandler::Dynamic { effects, .. } | MHandler::Native { effects, .. } => {
            for effect in effects {
                push_unique_effect(out, effect);
            }
        }
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_effects(handler, out);
            }
        }
    }
}

fn blocking_frame(effects: Vec<String>) -> Option<HandlerFrame> {
    if effects.is_empty() {
        None
    } else {
        Some(HandlerFrame::Blocking { effects })
    }
}

fn push_unique_effect(out: &mut Vec<String>, effect: &str) {
    if !out.iter().any(|e| e == effect) {
        out.push(effect.to_string());
    }
}

fn expr_contains_yield(expr: &MExpr) -> bool {
    match expr {
        MExpr::Yield { .. } => true,
        MExpr::Pure(atom) => atom_contains_yield(atom),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_yield(value) || expr_contains_yield(body)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_yield(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(expr_contains_yield)
                        || expr_contains_yield(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_yield(cond)
                || expr_contains_yield(then_branch)
                || expr_contains_yield(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_yield(head) || args.iter().any(atom_contains_yield)
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_yield(handler) || expr_contains_yield(body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_yield(value),
        MExpr::ForeignCall { args, .. } => args.iter().any(atom_contains_yield),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_yield(record) || fields.iter().any(|(_, atom)| atom_contains_yield(atom))
        }
        MExpr::BinOp { left, right, .. } => atom_contains_yield(left) || atom_contains_yield(right),
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_yield(&seg.value) || seg.size.as_ref().is_some_and(atom_contains_yield)
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard.as_ref().is_some_and(expr_contains_yield)
                    || expr_contains_yield(&arm.body)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_yield(timeout) || expr_contains_yield(body)
            })
        }
        MExpr::LetFun { body, rest, .. } => expr_contains_yield(body) || expr_contains_yield(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_yield)
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_yield(arm))
        }
    }
}

fn atom_contains_yield(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } => args.iter().any(atom_contains_yield),
        Atom::Tuple { elements, .. } => elements.iter().any(atom_contains_yield),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, atom)| atom_contains_yield(atom))
        }
        Atom::Lambda { body, .. } => expr_contains_yield(body),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => false,
    }
}

fn handler_contains_yield(handler: &MHandler) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_yield)
                || return_clause
                    .as_ref()
                    .is_some_and(handler_arm_contains_yield)
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => handlers.iter().any(handler_contains_yield),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_yield(op_tuple) || return_lambda.as_ref().is_some_and(atom_contains_yield)
        }
    }
}

fn handler_arm_contains_yield(arm: &MHandlerArm) -> bool {
    expr_contains_yield(&arm.body)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|finally_block| expr_contains_yield(finally_block))
}

fn inline_tail_resumptive_arm(arm: &MHandlerArm, args: &[Atom]) -> Option<MExpr> {
    if args.len() != arm.params.len() {
        return None;
    }

    let mut body = (*arm.body).clone();
    for (param, arg) in arm.params.iter().zip(args) {
        match param {
            Pat::Var { name, id, .. } => {
                let target = MVar {
                    name: name.clone(),
                    id: id.0,
                };
                let free_names = free_atom_names(arg);
                let substituted = subst_expr(body, &target, arg, &free_names);
                if substituted.blocked {
                    return None;
                }
                body = substituted.value;
            }
            Pat::Wildcard { .. }
            | Pat::Lit {
                value: crate::ast::Lit::Unit,
                ..
            } => {}
            _ => return None,
        }
    }
    Some(body)
}

fn rewrite_resumes_to_pure(expr: MExpr) -> MExpr {
    match expr {
        MExpr::Resume { value, .. } => MExpr::Pure(value),
        MExpr::Pure(atom) => MExpr::Pure(rewrite_resumes_in_atom(atom)),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op,
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => MExpr::Bind {
            var,
            value: Box::new(rewrite_resumes_to_pure(*value)),
            body: Box::new(rewrite_resumes_to_pure(*body)),
            mode,
        },
        MExpr::Let { var, value, body } => MExpr::Let {
            var,
            value: Box::new(rewrite_resumes_to_pure(*value)),
            body: Box::new(rewrite_resumes_to_pure(*body)),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => MExpr::Case {
            scrutinee: rewrite_resumes_in_atom(scrutinee),
            arms: arms
                .into_iter()
                .map(|arm| MArm {
                    guard: arm.guard.map(rewrite_resumes_to_pure),
                    body: rewrite_resumes_to_pure(arm.body),
                    ..arm
                })
                .collect(),
            source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => MExpr::If {
            cond: rewrite_resumes_in_atom(cond),
            then_branch: Box::new(rewrite_resumes_to_pure(*then_branch)),
            else_branch: Box::new(rewrite_resumes_to_pure(*else_branch)),
            source,
        },
        MExpr::App { head, args, source } => MExpr::App {
            head: rewrite_resumes_in_atom(head),
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        MExpr::With {
            handler,
            body,
            source,
        } => MExpr::With {
            handler,
            body: Box::new(rewrite_resumes_to_pure(*body)),
            source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => MExpr::FieldAccess {
            record: rewrite_resumes_in_atom(record),
            field,
            record_name,
            anon_fields,
            source,
        },
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source,
        } => MExpr::RecordUpdate {
            record: rewrite_resumes_in_atom(record),
            fields: fields
                .into_iter()
                .map(|(name, atom)| (name, rewrite_resumes_in_atom(atom)))
                .collect(),
            record_name,
            anon_fields,
            source,
        },
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => MExpr::DictMethodAccess {
            dict: rewrite_resumes_in_atom(dict),
            trait_name,
            method_index,
            source,
        },
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => MExpr::ForeignCall {
            module,
            func,
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => MExpr::BinOp {
            op,
            left: rewrite_resumes_in_atom(left),
            right: rewrite_resumes_in_atom(right),
            source,
        },
        MExpr::UnaryMinus { value, source } => MExpr::UnaryMinus {
            value: rewrite_resumes_in_atom(value),
            source,
        },
        MExpr::BitString { segments, source } => MExpr::BitString {
            segments: segments
                .into_iter()
                .map(|mut seg| {
                    seg.value = rewrite_resumes_in_atom(seg.value);
                    seg.size = seg.size.map(rewrite_resumes_in_atom);
                    seg
                })
                .collect(),
            source,
        },
        MExpr::Receive {
            arms,
            after,
            source,
        } => MExpr::Receive {
            arms: arms
                .into_iter()
                .map(|arm| MArm {
                    guard: arm.guard.map(rewrite_resumes_to_pure),
                    body: rewrite_resumes_to_pure(arm.body),
                    ..arm
                })
                .collect(),
            after: after.map(|(timeout, body)| {
                (
                    rewrite_resumes_in_atom(timeout),
                    Box::new(rewrite_resumes_to_pure(*body)),
                )
            }),
            source,
        },
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source,
        } => MExpr::LetFun {
            name,
            params,
            // A nested local function has its own resume context; only the
            // surrounding continuation remains part of the inlined arm body.
            body,
            rest: Box::new(rewrite_resumes_to_pure(*rest)),
            source,
        },
        MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source,
        } => MExpr::HandlerValue {
            effects,
            // Handler-value arms introduce their own resume context.
            arms,
            return_clause,
            source,
        },
    }
}

fn rewrite_resumes_in_atom(atom: Atom) -> Atom {
    match atom {
        Atom::Ctor { name, args, source } => Atom::Ctor {
            name,
            args: args.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        Atom::Tuple { elements, source } => Atom::Tuple {
            elements: elements.into_iter().map(rewrite_resumes_in_atom).collect(),
            source,
        },
        Atom::AnonRecord { fields, source } => Atom::AnonRecord {
            fields: fields
                .into_iter()
                .map(|(name, atom)| (name, rewrite_resumes_in_atom(atom)))
                .collect(),
            source,
        },
        Atom::Record {
            name,
            fields,
            source,
        } => Atom::Record {
            name,
            fields: fields
                .into_iter()
                .map(|(name, atom)| (name, rewrite_resumes_in_atom(atom)))
                .collect(),
            source,
        },
        Atom::Lambda { .. } => atom,
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => atom,
    }
}

fn map_subst<T, U>(out: SubstOutcome<T>, f: impl FnOnce(T) -> U) -> SubstOutcome<U> {
    SubstOutcome {
        value: f(out.value),
        changed: out.changed,
        blocked: out.blocked,
    }
}

fn combine_pair<A, B, U>(
    a: SubstOutcome<A>,
    b: SubstOutcome<B>,
    f: impl FnOnce(A, B) -> U,
) -> SubstOutcome<U> {
    SubstOutcome {
        value: f(a.value, b.value),
        changed: a.changed || b.changed,
        blocked: a.blocked || b.blocked,
    }
}

fn combine_triple<A, B, C, U>(
    a: SubstOutcome<A>,
    b: SubstOutcome<B>,
    c: SubstOutcome<C>,
    f: impl FnOnce(A, B, C) -> U,
) -> SubstOutcome<U> {
    SubstOutcome {
        value: f(a.value, b.value, c.value),
        changed: a.changed || b.changed || c.changed,
        blocked: a.blocked || b.blocked || c.blocked,
    }
}

fn subst_expr(
    expr: MExpr,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MExpr> {
    match expr {
        MExpr::Pure(atom) => {
            let out = subst_atom(atom, target, replacement, replacement_free_names);
            map_subst(out, MExpr::Pure)
        }
        MExpr::Yield { op, args, source } => {
            let out = subst_atoms(args, target, replacement, replacement_free_names);
            map_subst(out, |args| MExpr::Yield { op, args, source })
        }
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let value_out = subst_expr(*value, target, replacement, replacement_free_names);
            if var == *target || var.name == target.name {
                return SubstOutcome {
                    value: MExpr::Bind {
                        var,
                        value: Box::new(value_out.value),
                        body,
                        mode,
                    },
                    changed: value_out.changed,
                    blocked: value_out.blocked,
                };
            }
            if replacement_free_names.contains(&var.name) && expr_contains_target(&body, target) {
                return SubstOutcome::blocked(MExpr::Bind {
                    var,
                    value: Box::new(value_out.value),
                    body,
                    mode,
                });
            }
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            combine_pair(value_out, body_out, |value, body| MExpr::Bind {
                var,
                value: Box::new(value),
                body: Box::new(body),
                mode,
            })
        }
        MExpr::Let { var, value, body } => {
            let value_out = subst_expr(*value, target, replacement, replacement_free_names);
            if var == *target || var.name == target.name {
                return SubstOutcome {
                    value: MExpr::Let {
                        var,
                        value: Box::new(value_out.value),
                        body,
                    },
                    changed: value_out.changed,
                    blocked: value_out.blocked,
                };
            }
            if replacement_free_names.contains(&var.name) && expr_contains_target(&body, target) {
                return SubstOutcome::blocked(MExpr::Let {
                    var,
                    value: Box::new(value_out.value),
                    body,
                });
            }
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            combine_pair(value_out, body_out, |value, body| MExpr::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            })
        }
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => {
            let scrutinee_out = subst_atom(scrutinee, target, replacement, replacement_free_names);
            let arms_out = subst_arms(arms, target, replacement, replacement_free_names);
            combine_pair(scrutinee_out, arms_out, |scrutinee, arms| MExpr::Case {
                scrutinee,
                arms,
                source,
            })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => {
            let cond_out = subst_atom(cond, target, replacement, replacement_free_names);
            let then_out = subst_expr(*then_branch, target, replacement, replacement_free_names);
            let else_out = subst_expr(*else_branch, target, replacement, replacement_free_names);
            combine_triple(
                cond_out,
                then_out,
                else_out,
                |cond, then_branch, else_branch| MExpr::If {
                    cond,
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                    source,
                },
            )
        }
        MExpr::App { head, args, source } => {
            let head_out = subst_atom(head, target, replacement, replacement_free_names);
            let args_out = subst_atoms(args, target, replacement, replacement_free_names);
            combine_pair(head_out, args_out, |head, args| MExpr::App {
                head,
                args,
                source,
            })
        }
        MExpr::With {
            handler,
            body,
            source,
        } => {
            let handler_out = subst_handler(handler, target, replacement, replacement_free_names);
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            combine_pair(handler_out, body_out, |handler, body| MExpr::With {
                handler,
                body: Box::new(body),
                source,
            })
        }
        MExpr::Resume { value, source } => {
            let out = subst_atom(value, target, replacement, replacement_free_names);
            map_subst(out, |value| MExpr::Resume { value, source })
        }
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => {
            let out = subst_atom(record, target, replacement, replacement_free_names);
            map_subst(out, |record| MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                source,
            })
        }
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            anon_fields,
            source,
        } => {
            let record_out = subst_atom(record, target, replacement, replacement_free_names);
            let fields_out = subst_field_atoms(fields, target, replacement, replacement_free_names);
            combine_pair(record_out, fields_out, |record, fields| {
                MExpr::RecordUpdate {
                    record,
                    fields,
                    record_name,
                    anon_fields,
                    source,
                }
            })
        }
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => {
            let out = subst_atom(dict, target, replacement, replacement_free_names);
            map_subst(out, |dict| MExpr::DictMethodAccess {
                dict,
                trait_name,
                method_index,
                source,
            })
        }
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => {
            let out = subst_atoms(args, target, replacement, replacement_free_names);
            map_subst(out, |args| MExpr::ForeignCall {
                module,
                func,
                args,
                source,
            })
        }
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => {
            let left_out = subst_atom(left, target, replacement, replacement_free_names);
            let right_out = subst_atom(right, target, replacement, replacement_free_names);
            combine_pair(left_out, right_out, |left, right| MExpr::BinOp {
                op,
                left,
                right,
                source,
            })
        }
        MExpr::UnaryMinus { value, source } => {
            let out = subst_atom(value, target, replacement, replacement_free_names);
            map_subst(out, |value| MExpr::UnaryMinus { value, source })
        }
        MExpr::BitString { segments, source } => {
            let mut changed = false;
            let mut blocked = false;
            let segments = segments
                .into_iter()
                .map(|mut seg| {
                    let value_out =
                        subst_atom(seg.value, target, replacement, replacement_free_names);
                    changed |= value_out.changed;
                    blocked |= value_out.blocked;
                    seg.value = value_out.value;
                    if let Some(size) = seg.size {
                        let size_out =
                            subst_atom(size, target, replacement, replacement_free_names);
                        changed |= size_out.changed;
                        blocked |= size_out.blocked;
                        seg.size = Some(size_out.value);
                    }
                    seg
                })
                .collect();
            SubstOutcome {
                value: MExpr::BitString { segments, source },
                changed,
                blocked,
            }
        }
        MExpr::Receive {
            arms,
            after,
            source,
        } => {
            let arms_out = subst_arms(arms, target, replacement, replacement_free_names);
            let after_out = match after {
                Some((timeout, body)) => {
                    let timeout_out =
                        subst_atom(timeout, target, replacement, replacement_free_names);
                    let body_out = subst_expr(*body, target, replacement, replacement_free_names);
                    let combined = combine_pair(timeout_out, body_out, |timeout, body| {
                        (timeout, Box::new(body))
                    });
                    SubstOutcome {
                        value: Some(combined.value),
                        changed: combined.changed,
                        blocked: combined.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(arms_out, after_out, |arms, after| MExpr::Receive {
                arms,
                after,
                source,
            })
        }
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            source,
        } => {
            let body_out = if pats_bind_name(&params, &target.name)
                || (pats_capture_replacement(&params, replacement_free_names)
                    && expr_contains_target(&body, target))
            {
                if pats_bind_name(&params, &target.name) {
                    SubstOutcome::unchanged(*body)
                } else {
                    SubstOutcome::blocked(*body)
                }
            } else {
                subst_expr(*body, target, replacement, replacement_free_names)
            };
            let rest_out = subst_expr(*rest, target, replacement, replacement_free_names);
            combine_pair(body_out, rest_out, |body, rest| MExpr::LetFun {
                name,
                params,
                body: Box::new(body),
                rest: Box::new(rest),
                source,
            })
        }
        MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source,
        } => {
            let arms_out = subst_handler_arms(arms, target, replacement, replacement_free_names);
            let return_out = match return_clause {
                Some(arm) => {
                    let out = subst_handler_arm(*arm, target, replacement, replacement_free_names);
                    SubstOutcome {
                        value: Some(Box::new(out.value)),
                        changed: out.changed,
                        blocked: out.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(arms_out, return_out, |arms, return_clause| {
                MExpr::HandlerValue {
                    effects,
                    arms,
                    return_clause,
                    source,
                }
            })
        }
    }
}

fn subst_atom(
    atom: Atom,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Atom> {
    match atom {
        Atom::Var { name, .. } if var_matches(&name, target) => {
            SubstOutcome::changed(replacement.clone())
        }
        Atom::Ctor { name, args, source } => {
            let out = subst_atoms(args, target, replacement, replacement_free_names);
            map_subst(out, |args| Atom::Ctor { name, args, source })
        }
        Atom::Tuple { elements, source } => {
            let out = subst_atoms(elements, target, replacement, replacement_free_names);
            map_subst(out, |elements| Atom::Tuple { elements, source })
        }
        Atom::AnonRecord { fields, source } => {
            let out = subst_field_atoms(fields, target, replacement, replacement_free_names);
            map_subst(out, |fields| Atom::AnonRecord { fields, source })
        }
        Atom::Record {
            name,
            fields,
            source,
        } => {
            let out = subst_field_atoms(fields, target, replacement, replacement_free_names);
            map_subst(out, |fields| Atom::Record {
                name,
                fields,
                source,
            })
        }
        Atom::Lambda {
            params,
            body,
            source,
        } => {
            if pats_bind_name(&params, &target.name) {
                return SubstOutcome::unchanged(Atom::Lambda {
                    params,
                    body,
                    source,
                });
            }
            if pats_capture_replacement(&params, replacement_free_names)
                && expr_contains_target(&body, target)
            {
                return SubstOutcome::blocked(Atom::Lambda {
                    params,
                    body,
                    source,
                });
            }
            let out = subst_expr(*body, target, replacement, replacement_free_names);
            map_subst(out, |body| Atom::Lambda {
                params,
                body: Box::new(body),
                source,
            })
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => SubstOutcome::unchanged(atom),
    }
}

fn subst_atoms(
    atoms: Vec<Atom>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<Atom>> {
    let mut changed = false;
    let mut blocked = false;
    let atoms = atoms
        .into_iter()
        .map(|atom| {
            let out = subst_atom(atom, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            out.value
        })
        .collect();
    SubstOutcome {
        value: atoms,
        changed,
        blocked,
    }
}

fn subst_field_atoms(
    fields: Vec<(String, Atom)>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<(String, Atom)>> {
    let mut changed = false;
    let mut blocked = false;
    let fields = fields
        .into_iter()
        .map(|(name, atom)| {
            let out = subst_atom(atom, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            (name, out.value)
        })
        .collect();
    SubstOutcome {
        value: fields,
        changed,
        blocked,
    }
}

fn subst_arms(
    arms: Vec<MArm>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<MArm>> {
    let mut changed = false;
    let mut blocked = false;
    let arms = arms
        .into_iter()
        .map(|arm| {
            let out = subst_arm(arm, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            out.value
        })
        .collect();
    SubstOutcome {
        value: arms,
        changed,
        blocked,
    }
}

fn subst_arm(
    arm: MArm,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MArm> {
    if pat_has_nonbinding_ref(&arm.pattern, &target.name) {
        return SubstOutcome::blocked(arm);
    }
    if pat_binds_name(&arm.pattern, &target.name) {
        return SubstOutcome::unchanged(arm);
    }
    let target_in_arm = arm
        .guard
        .as_ref()
        .is_some_and(|g| expr_contains_target(g, target))
        || expr_contains_target(&arm.body, target);
    if pat_captures_replacement(&arm.pattern, replacement_free_names) && target_in_arm {
        return SubstOutcome::blocked(arm);
    }

    let guard_out = match arm.guard {
        Some(guard) => {
            let out = subst_expr(guard, target, replacement, replacement_free_names);
            SubstOutcome {
                value: Some(out.value),
                changed: out.changed,
                blocked: out.blocked,
            }
        }
        None => SubstOutcome::unchanged(None),
    };
    let body_out = subst_expr(arm.body, target, replacement, replacement_free_names);
    combine_pair(guard_out, body_out, |guard, body| MArm {
        guard,
        body,
        ..arm
    })
}

fn subst_handler(
    handler: MHandler,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MHandler> {
    match handler {
        MHandler::Static {
            effects,
            arms,
            return_clause,
            source,
        } => {
            let arms_out = subst_handler_arms(arms, target, replacement, replacement_free_names);
            let return_out = match return_clause {
                Some(arm) => {
                    let out = subst_handler_arm(arm, target, replacement, replacement_free_names);
                    SubstOutcome {
                        value: Some(out.value),
                        changed: out.changed,
                        blocked: out.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(arms_out, return_out, |arms, return_clause| {
                MHandler::Static {
                    effects,
                    arms,
                    return_clause,
                    source,
                }
            })
        }
        MHandler::Native { .. } => SubstOutcome::unchanged(handler),
        MHandler::Composite { handlers, source } => {
            let mut changed = false;
            let mut blocked = false;
            let handlers = handlers
                .into_iter()
                .map(|handler| {
                    let out = subst_handler(handler, target, replacement, replacement_free_names);
                    changed |= out.changed;
                    blocked |= out.blocked;
                    out.value
                })
                .collect();
            SubstOutcome {
                value: MHandler::Composite { handlers, source },
                changed,
                blocked,
            }
        }
        MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } => {
            let op_out = subst_atom(op_tuple, target, replacement, replacement_free_names);
            let return_out = match return_lambda {
                Some(atom) => {
                    let out = subst_atom(atom, target, replacement, replacement_free_names);
                    SubstOutcome {
                        value: Some(out.value),
                        changed: out.changed,
                        blocked: out.blocked,
                    }
                }
                None => SubstOutcome::unchanged(None),
            };
            combine_pair(op_out, return_out, |op_tuple, return_lambda| {
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                }
            })
        }
    }
}

fn subst_handler_arms(
    arms: Vec<MHandlerArm>,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<Vec<MHandlerArm>> {
    let mut changed = false;
    let mut blocked = false;
    let arms = arms
        .into_iter()
        .map(|arm| {
            let out = subst_handler_arm(arm, target, replacement, replacement_free_names);
            changed |= out.changed;
            blocked |= out.blocked;
            out.value
        })
        .collect();
    SubstOutcome {
        value: arms,
        changed,
        blocked,
    }
}

fn subst_handler_arm(
    arm: MHandlerArm,
    target: &MVar,
    replacement: &Atom,
    replacement_free_names: &HashSet<String>,
) -> SubstOutcome<MHandlerArm> {
    if pats_bind_name(&arm.params, &target.name) {
        return SubstOutcome::unchanged(arm);
    }
    let target_in_arm = expr_contains_target(&arm.body, target)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|f| expr_contains_target(f, target));
    if pats_capture_replacement(&arm.params, replacement_free_names) && target_in_arm {
        return SubstOutcome::blocked(arm);
    }

    let body_out = subst_expr(*arm.body, target, replacement, replacement_free_names);
    let finally_out = match arm.finally_block {
        Some(finally_block) => {
            let out = subst_expr(*finally_block, target, replacement, replacement_free_names);
            SubstOutcome {
                value: Some(Box::new(out.value)),
                changed: out.changed,
                blocked: out.blocked,
            }
        }
        None => SubstOutcome::unchanged(None),
    };
    combine_pair(body_out, finally_out, |body, finally_block| MHandlerArm {
        body: Box::new(body),
        finally_block,
        ..arm
    })
}

fn free_atom_names(atom: &Atom) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_atom_var_names(atom, &mut out);
    out
}

fn var_matches(actual: &MVar, target: &MVar) -> bool {
    actual == target || actual.name == target.name
}

fn collect_atom_var_names(atom: &Atom, out: &mut HashSet<String>) {
    match atom {
        Atom::Var { name, .. } => {
            out.insert(name.name.clone());
        }
        Atom::Ctor { args, .. } => collect_atom_list_names(args, out),
        Atom::Tuple { elements, .. } => collect_atom_list_names(elements, out),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_var_names(atom, out);
            }
        }
        Atom::Lambda { body, .. } => collect_expr_var_names(body, out),
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => {}
    }
}

fn collect_atom_list_names(atoms: &[Atom], out: &mut HashSet<String>) {
    for atom in atoms {
        collect_atom_var_names(atom, out);
    }
}

fn expr_contains_target(expr: &MExpr, target: &MVar) -> bool {
    match expr {
        MExpr::Pure(atom) => atom_contains_target(atom, target),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(|a| atom_contains_target(a, target))
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            expr_contains_target(value, target)
                || ((!var_matches(var, target)) && expr_contains_target(body, target))
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_target(scrutinee, target)
                || arms.iter().any(|arm| {
                    !pat_binds_name(&arm.pattern, &target.name)
                        && (arm
                            .guard
                            .as_ref()
                            .is_some_and(|g| expr_contains_target(g, target))
                            || expr_contains_target(&arm.body, target))
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_target(cond, target)
                || expr_contains_target(then_branch, target)
                || expr_contains_target(else_branch, target)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_target(head, target)
                || args.iter().any(|a| atom_contains_target(a, target))
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_target(handler, target) || expr_contains_target(body, target)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_target(value, target),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_target(record, target)
                || fields.iter().any(|(_, a)| atom_contains_target(a, target))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_target(left, target) || atom_contains_target(right, target)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_target(&seg.value, target)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| atom_contains_target(size, target))
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                !pat_binds_name(&arm.pattern, &target.name)
                    && (arm
                        .guard
                        .as_ref()
                        .is_some_and(|g| expr_contains_target(g, target))
                        || expr_contains_target(&arm.body, target))
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_target(timeout, target) || expr_contains_target(body, target)
            })
        }
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            ..
        } => {
            if name == &target.name {
                false
            } else {
                (!pats_bind_name(params, &target.name) && expr_contains_target(body, target))
                    || expr_contains_target(rest, target)
            }
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_contains_target(arm, target))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_target(arm, target))
        }
    }
}

fn atom_contains_target(atom: &Atom, target: &MVar) -> bool {
    match atom {
        Atom::Var { name, .. } => var_matches(name, target),
        Atom::Ctor { args, .. } => args.iter().any(|a| atom_contains_target(a, target)),
        Atom::Tuple { elements, .. } => elements.iter().any(|a| atom_contains_target(a, target)),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, a)| atom_contains_target(a, target))
        }
        Atom::Lambda { params, body, .. } => {
            !pats_bind_name(params, &target.name) && expr_contains_target(body, target)
        }
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => false,
    }
}

fn handler_contains_target(handler: &MHandler, target: &MVar) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_contains_target(arm, target))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_target(arm, target))
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => handlers
            .iter()
            .any(|handler| handler_contains_target(handler, target)),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_target(op_tuple, target)
                || return_lambda
                    .as_ref()
                    .is_some_and(|atom| atom_contains_target(atom, target))
        }
    }
}

fn handler_arm_contains_target(arm: &MHandlerArm, target: &MVar) -> bool {
    !pats_bind_name(&arm.params, &target.name)
        && (expr_contains_target(&arm.body, target)
            || arm
                .finally_block
                .as_ref()
                .is_some_and(|f| expr_contains_target(f, target)))
}

fn collect_expr_var_names(expr: &MExpr, out: &mut HashSet<String>) {
    match expr {
        MExpr::Pure(atom) => collect_atom_var_names(atom, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_names(args, out)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_expr_var_names(value, out);
            collect_expr_var_names(body, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_var_names(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_var_names(guard, out);
                }
                collect_expr_var_names(&arm.body, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_var_names(cond, out);
            collect_expr_var_names(then_branch, out);
            collect_expr_var_names(else_branch, out);
        }
        MExpr::App { head, args, .. } => {
            collect_atom_var_names(head, out);
            collect_atom_list_names(args, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_var_names(handler, out);
            collect_expr_var_names(body, out);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_var_names(value, out),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_var_names(record, out);
            for (_, atom) in fields {
                collect_atom_var_names(atom, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_var_names(left, out);
            collect_atom_var_names(right, out);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_var_names(&seg.value, out);
                if let Some(size) = &seg.size {
                    collect_atom_var_names(size, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_var_names(guard, out);
                }
                collect_expr_var_names(&arm.body, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_var_names(timeout, out);
                collect_expr_var_names(body, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_expr_var_names(body, out);
            collect_expr_var_names(rest, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_var_names(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_var_names(arm, out);
            }
        }
    }
}

fn collect_handler_var_names(handler: &MHandler, out: &mut HashSet<String>) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_var_names(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_var_names(arm, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_var_names(handler, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_var_names(op_tuple, out);
            if let Some(atom) = return_lambda {
                collect_atom_var_names(atom, out);
            }
        }
    }
}

fn collect_handler_arm_var_names(arm: &MHandlerArm, out: &mut HashSet<String>) {
    collect_expr_var_names(&arm.body, out);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_var_names(finally_block, out);
    }
}

fn pats_bind_name(params: &[Pat], name: &str) -> bool {
    params.iter().any(|pat| pat_binds_name(pat, name))
}

fn pats_capture_replacement(params: &[Pat], replacement_free_names: &HashSet<String>) -> bool {
    params
        .iter()
        .any(|pat| pat_captures_replacement(pat, replacement_free_names))
}

fn pat_captures_replacement(pat: &Pat, replacement_free_names: &HashSet<String>) -> bool {
    pat_bound_names(pat)
        .iter()
        .any(|name| replacement_free_names.contains(name))
}

fn pat_binds_name(pat: &Pat, name: &str) -> bool {
    pat_bound_names(pat).iter().any(|bound| bound == name)
}

fn pat_bound_names(pat: &Pat) -> Vec<String> {
    let mut out = Vec::new();
    collect_pat_bound_names(pat, &mut out);
    out
}

fn collect_pat_bound_names(pat: &Pat, out: &mut Vec<String>) {
    match pat {
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Constructor { args, .. } => {
            for arg in args {
                collect_pat_bound_names(arg, out);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            for (field_name, alias) in fields {
                match alias {
                    Some(p) => collect_pat_bound_names(p, out),
                    None => out.push(field_name.clone()),
                }
            }
            if let Some(name) = as_name {
                out.push(name.clone());
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (field_name, alias) in fields {
                match alias {
                    Some(p) => collect_pat_bound_names(p, out),
                    None => out.push(field_name.clone()),
                }
            }
        }
        Pat::Tuple { elements, .. } => {
            for element in elements {
                collect_pat_bound_names(element, out);
            }
        }
        Pat::StringPrefix { rest, .. } => collect_pat_bound_names(rest, out),
        Pat::BitStringPat { segments, .. } => {
            for seg in segments {
                collect_pat_bound_names(&seg.value, out);
            }
        }
        Pat::ListPat { elements, .. } => {
            for element in elements {
                collect_pat_bound_names(element, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_bound_names(head, out);
            collect_pat_bound_names(tail, out);
        }
        Pat::Or { patterns, .. } => {
            for pat in patterns {
                collect_pat_bound_names(pat, out);
            }
        }
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
    }
}

fn pat_has_nonbinding_ref(pat: &Pat, name: &str) -> bool {
    match pat {
        Pat::Constructor { args, .. } => args.iter().any(|p| pat_has_nonbinding_ref(p, name)),
        Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
            fields.iter().any(|(_, alias)| {
                alias
                    .as_ref()
                    .is_some_and(|p| pat_has_nonbinding_ref(p, name))
            })
        }
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            elements.iter().any(|p| pat_has_nonbinding_ref(p, name))
        }
        Pat::StringPrefix { rest, .. } => pat_has_nonbinding_ref(rest, name),
        Pat::BitStringPat { segments, .. } => segments.iter().any(|seg| {
            pat_has_nonbinding_ref(&seg.value, name)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| expr_mentions_name(size, name))
        }),
        Pat::ConsPat { head, tail, .. } => {
            pat_has_nonbinding_ref(head, name) || pat_has_nonbinding_ref(tail, name)
        }
        Pat::Or { patterns, .. } => patterns.iter().any(|p| pat_has_nonbinding_ref(p, name)),
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => false,
    }
}

fn expr_mentions_name(expr: &Expr, name: &str) -> bool {
    match &expr.kind {
        ExprKind::Var { name: var } => var == name,
        ExprKind::App { func, arg, .. } => {
            expr_mentions_name(func, name) || expr_mentions_name(arg, name)
        }
        ExprKind::BinOp { left, right, .. } => {
            expr_mentions_name(left, name) || expr_mentions_name(right, name)
        }
        ExprKind::UnaryMinus { expr } | ExprKind::Ascription { expr, .. } => {
            expr_mentions_name(expr, name)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_mentions_name(cond, name)
                || expr_mentions_name(then_branch, name)
                || expr_mentions_name(else_branch, name)
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            expr_mentions_name(scrutinee, name)
                || arms.iter().any(|arm| {
                    pat_has_nonbinding_ref(&arm.node.pattern, name)
                        || (!pat_binds_name(&arm.node.pattern, name)
                            && arm
                                .node
                                .guard
                                .as_ref()
                                .is_some_and(|g| expr_mentions_name(g, name)))
                        || (!pat_binds_name(&arm.node.pattern, name)
                            && expr_mentions_name(&arm.node.body, name))
                })
        }
        ExprKind::Block { stmts, .. } => stmts
            .iter()
            .any(|stmt| stmt_mentions_name(&stmt.node, name)),
        ExprKind::Lambda { params, body } => {
            params.iter().any(|p| pat_has_nonbinding_ref(p, name))
                || (!pats_bind_name(params, name) && expr_mentions_name(body, name))
        }
        ExprKind::FieldAccess { expr, .. } => expr_mentions_name(expr, name),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
            fields.iter().any(|(_, _, e)| expr_mentions_name(e, name))
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            expr_mentions_name(record, name)
                || fields.iter().any(|(_, _, e)| expr_mentions_name(e, name))
        }
        ExprKind::EffectCall { args, .. } | ExprKind::ForeignCall { args, .. } => {
            args.iter().any(|e| expr_mentions_name(e, name))
        }
        ExprKind::With { expr, handler } => {
            expr_mentions_name(expr, name) || handler_mentions_name(handler, name)
        }
        ExprKind::Resume { value } => expr_mentions_name(value, name),
        ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
            elements.iter().any(|e| expr_mentions_name(e, name))
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            bindings
                .iter()
                .any(|(p, e)| pat_has_nonbinding_ref(p, name) || expr_mentions_name(e, name))
                || expr_mentions_name(success, name)
                || else_arms.iter().any(|arm| {
                    pat_has_nonbinding_ref(&arm.node.pattern, name)
                        || (!pat_binds_name(&arm.node.pattern, name)
                            && expr_mentions_name(&arm.node.body, name))
                })
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            arms.iter().any(|arm| {
                pat_has_nonbinding_ref(&arm.node.pattern, name)
                    || (!pat_binds_name(&arm.node.pattern, name)
                        && arm
                            .node
                            .guard
                            .as_ref()
                            .is_some_and(|g| expr_mentions_name(g, name)))
                    || (!pat_binds_name(&arm.node.pattern, name)
                        && expr_mentions_name(&arm.node.body, name))
            }) || after_clause.as_ref().is_some_and(|(timeout, body)| {
                expr_mentions_name(timeout, name) || expr_mentions_name(body, name)
            })
        }
        ExprKind::BitString { segments } => segments.iter().any(|seg| {
            expr_mentions_name(&seg.value, name)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| expr_mentions_name(size, name))
        }),
        ExprKind::HandlerExpr { body } => {
            body.arms.iter().any(|arm| {
                pat_has_nonbinding_ref_in_handler_arm(&arm.node.params, name)
                    || (!pats_bind_name(&arm.node.params, name)
                        && expr_mentions_name(&arm.node.body, name))
            }) || body.return_clause.as_ref().is_some_and(|arm| {
                pat_has_nonbinding_ref_in_handler_arm(&arm.params, name)
                    || (!pats_bind_name(&arm.params, name) && expr_mentions_name(&arm.body, name))
            })
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            segments.iter().any(|s| expr_mentions_name(&s.node, name))
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            segments.iter().any(|s| expr_mentions_name(&s.node, name))
        }
        ExprKind::Cons { head, tail } => {
            expr_mentions_name(head, name) || expr_mentions_name(tail, name)
        }
        ExprKind::StringInterp { parts, .. } => parts.iter().any(|part| match part {
            StringPart::Expr(e) => expr_mentions_name(e, name),
            StringPart::Lit(_) => false,
        }),
        ExprKind::ListComprehension { body, qualifiers } => {
            expr_mentions_name(body, name)
                || qualifiers.iter().any(|q| match q {
                    ComprehensionQualifier::Generator(p, e) | ComprehensionQualifier::Let(p, e) => {
                        pat_has_nonbinding_ref(p, name) || expr_mentions_name(e, name)
                    }
                    ComprehensionQualifier::Guard(e) => expr_mentions_name(e, name),
                })
        }
        ExprKind::DictMethodAccess { dict, .. } => expr_mentions_name(dict, name),
        ExprKind::Lit { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => false,
    }
}

fn stmt_mentions_name(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::Let { pattern, value, .. } => {
            pat_has_nonbinding_ref(pattern, name) || expr_mentions_name(value, name)
        }
        Stmt::LetFun {
            name: fun_name,
            params,
            body,
            guard,
            ..
        } => {
            fun_name == name
                || params.iter().any(|p| pat_has_nonbinding_ref(p, name))
                || (!pats_bind_name(params, name)
                    && (expr_mentions_name(body, name)
                        || guard.as_ref().is_some_and(|g| expr_mentions_name(g, name))))
        }
        Stmt::Expr(e) => expr_mentions_name(e, name),
    }
}

fn handler_mentions_name(handler: &Handler, name: &str) -> bool {
    match handler {
        Handler::Named(n) => n.name == name,
        Handler::Inline { items, .. } => items.iter().any(|item| match &item.node {
            HandlerItem::Named(n) => n.name == name,
            HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                pat_has_nonbinding_ref_in_handler_arm(&arm.params, name)
                    || (!pats_bind_name(&arm.params, name) && expr_mentions_name(&arm.body, name))
                    || arm
                        .finally_block
                        .as_ref()
                        .is_some_and(|f| expr_mentions_name(f, name))
            }
        }),
    }
}

fn pat_has_nonbinding_ref_in_handler_arm(params: &[Pat], name: &str) -> bool {
    params.iter().any(|p| pat_has_nonbinding_ref(p, name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::monadic::ir::{EffectOpRef, MProgram};
    use crate::typechecker::ResolvedEffectOp;
    use std::collections::{HashMap, HashSet};

    struct Fixture {
        h: HandlerAnalysis,
        effect_calls: HashMap<crate::ast::NodeId, ResolvedEffectOp>,
        handler_arms: HashMap<crate::ast::NodeId, ResolvedEffectOp>,
        constructors: HashMap<crate::ast::NodeId, String>,
        fun_effects: HashMap<String, HashSet<String>>,
        let_effect_bindings: HashMap<String, Vec<String>>,
        type_at_node: HashMap<crate::ast::NodeId, crate::typechecker::Type>,
        effect_ops: HashMap<String, Vec<String>>,
        handler_effects: HashMap<String, Vec<String>>,
        handler_refs: HashMap<crate::ast::NodeId, crate::typechecker::ResolvedValue>,
        let_handler_effects: HashMap<crate::ast::NodeId, Vec<String>>,
    }

    impl Fixture {
        fn new() -> Self {
            Self {
                h: HandlerAnalysis::default(),
                effect_calls: HashMap::new(),
                handler_arms: HashMap::new(),
                constructors: HashMap::new(),
                fun_effects: HashMap::new(),
                let_effect_bindings: HashMap::new(),
                type_at_node: HashMap::new(),
                effect_ops: HashMap::new(),
                handler_effects: HashMap::new(),
                handler_refs: HashMap::new(),
                let_handler_effects: HashMap::new(),
            }
        }

        fn info(&self) -> EffectInfo<'_> {
            EffectInfo {
                effect_calls: &self.effect_calls,
                handler_arms: &self.handler_arms,
                constructors: &self.constructors,
                fun_effects: &self.fun_effects,
                let_effect_bindings: &self.let_effect_bindings,
                type_at_node: &self.type_at_node,
                effect_ops: &self.effect_ops,
                handler_effects: &self.handler_effects,
                handler_refs: &self.handler_refs,
                let_handler_effects: &self.let_handler_effects,
            }
        }
    }

    #[test]
    fn run_empty_program_is_identity() {
        let f = Fixture::new();
        let info = f.info();
        let prog: MProgram = vec![];
        assert_eq!(run(prog.clone(), &f.h, &info), prog);
    }

    #[test]
    fn run_with_skip_preserves_bind_pure() {
        let f = Fixture::new();
        let info = f.info();
        let prog = val_program(bind_pure(
            mv("x", 1),
            lit_int("1", 1),
            MExpr::Pure(var("x", 1)),
        ));
        assert_eq!(
            run_with_options(prog.clone(), &f.h, &info, RunOptions { skip: true }),
            prog
        );
    }

    #[test]
    fn mprogram_default_smoke() {
        let prog: MProgram = MProgram::default();
        assert!(prog.is_empty());
    }

    #[test]
    fn bind_collapse_substitutes_pure_atom() {
        let f = Fixture::new();
        let info = f.info();
        let prog = val_program(bind_pure(
            mv("x", 1),
            lit_int("1", 1),
            MExpr::Pure(var("x", 1)),
        ));

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(MExpr::Pure(lit_int("1", 1))));
    }

    #[test]
    fn bind_collapse_reaches_fixpoint() {
        let f = Fixture::new();
        let info = f.info();
        let prog = val_program(bind_pure(
            mv("x", 1),
            lit_int("1", 1),
            bind_pure(mv("y", 2), var("x", 1), MExpr::Pure(var("y", 2))),
        ));

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(MExpr::Pure(lit_int("1", 1))));
    }

    #[test]
    fn bind_collapse_respects_shadowing_binder() {
        let f = Fixture::new();
        let info = f.info();
        let prog = val_program(bind_pure(
            mv("x", 1),
            lit_int("1", 1),
            bind_pure(mv("x", 2), lit_int("2", 2), MExpr::Pure(var("x", 2))),
        ));

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(MExpr::Pure(lit_int("2", 2))));
    }

    #[test]
    fn bind_collapse_blocks_pattern_capture_but_promotes_to_let() {
        let f = Fixture::new();
        let info = f.info();
        let x = mv("x", 1);
        let replacement = var("y", 2);
        let body = MExpr::Case {
            scrutinee: var("scrut", 3),
            arms: vec![MArm {
                pattern: pat_var("y", 4),
                guard: None,
                body: MExpr::Pure(var("x", 1)),
                span: span(),
            }],
            source: crate::ast::NodeId(30),
        };
        let prog = val_program(bind_pure(x, replacement, body));

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(MExpr::Let {
                var: mv("x", 1),
                value: Box::new(MExpr::Pure(var("y", 2))),
                body: Box::new(MExpr::Case {
                    scrutinee: var("scrut", 3),
                    arms: vec![MArm {
                        pattern: pat_var("y", 4),
                        guard: None,
                        body: MExpr::Pure(var("x", 1)),
                        span: span(),
                    }],
                    source: crate::ast::NodeId(30),
                }),
            })
        );
    }

    #[test]
    fn bind_to_let_promotes_structurally_pure_expression() {
        let f = Fixture::new();
        let info = f.info();
        let value = MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: lit_int("1", 1),
            right: lit_int("2", 2),
            source: crate::ast::NodeId(40),
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value.clone(), body.clone()));

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(MExpr::Let {
                var: mv("x", 1),
                value: Box::new(value),
                body: Box::new(body),
            })
        );
    }

    #[test]
    fn bind_to_let_keeps_yield_monadic() {
        let f = Fixture::new();
        let info = f.info();
        let value = MExpr::Yield {
            op: EffectOpRef {
                effect: "Log".to_string(),
                op: "log".to_string(),
                op_index: 1,
            },
            args: vec![lit_int("1", 1)],
            source: crate::ast::NodeId(50),
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value, body));

        let out = run(prog.clone(), &f.h, &info);

        assert_eq!(out, prog);
    }

    #[test]
    fn bind_to_let_keeps_foreign_call_conservative() {
        let f = Fixture::new();
        let info = f.info();
        let value = MExpr::ForeignCall {
            module: "erlang".to_string(),
            func: "monotonic_time".to_string(),
            args: vec![],
            source: crate::ast::NodeId(60),
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value, body));

        let out = run(prog.clone(), &f.h, &info);

        assert_eq!(out, prog);
    }

    #[test]
    fn bind_to_let_keeps_with_conservative() {
        let f = Fixture::new();
        let info = f.info();
        let value = MExpr::With {
            handler: MHandler::Static {
                effects: vec!["Log".to_string()],
                arms: vec![],
                return_clause: None,
                source: crate::ast::NodeId(65),
            },
            body: Box::new(MExpr::Pure(lit_int("1", 1))),
            source: crate::ast::NodeId(66),
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value, body));

        let out = run(prog.clone(), &f.h, &info);

        assert_eq!(out, prog);
    }

    #[test]
    fn bind_to_let_promotes_app_with_closed_empty_effect_row() {
        let mut f = Fixture::new();
        let source = crate::ast::NodeId(70);
        let head_source = crate::ast::NodeId(71);
        f.type_at_node.insert(head_source, pure_fun_type());
        let info = f.info();
        let value = MExpr::App {
            head: var("pure_fun", 71),
            args: vec![lit_int("1", 1)],
            source,
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value.clone(), body.clone()));

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(MExpr::Let {
                var: mv("x", 1),
                value: Box::new(value),
                body: Box::new(body),
            })
        );
    }

    #[test]
    fn bind_to_let_keeps_app_with_effect_row() {
        let mut f = Fixture::new();
        let source = crate::ast::NodeId(80);
        let head_source = crate::ast::NodeId(81);
        f.type_at_node
            .insert(head_source, effectful_fun_type("Log"));
        let info = f.info();
        let value = MExpr::App {
            head: var("log_fun", 81),
            args: vec![lit_int("1", 1)],
            source,
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value, body));

        let out = run(prog.clone(), &f.h, &info);

        assert_eq!(out, prog);
    }

    #[test]
    fn bind_to_let_does_not_treat_app_result_type_as_purity_evidence() {
        let mut f = Fixture::new();
        let source = crate::ast::NodeId(90);
        f.type_at_node.insert(
            source,
            crate::typechecker::Type::Con("Int".to_string(), vec![]),
        );
        let info = f.info();
        let value = MExpr::App {
            head: var("unknown_fun", 91),
            args: vec![lit_int("1", 1)],
            source,
        };
        let body = MExpr::Pure(var("x", 1));
        let prog = val_program(bind_expr(mv("x", 1), value, body));

        let out = run(prog.clone(), &f.h, &info);

        assert_eq!(out, prog);
    }

    #[test]
    fn direct_call_inlines_static_tail_resumptive_yield() {
        let mut f = Fixture::new();
        let arm = tail_arm(100, vec![pat_unit(101)], resume(lit_int("42", 42)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(100), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let prog = val_program(with_expr(
            handler.clone(),
            yield_log(vec![unit_atom()], crate::ast::NodeId(102)),
        ));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(handler, MExpr::Pure(lit_int("42", 42))))
        );
    }

    #[test]
    fn direct_call_exposes_bind_pure_collapse_in_same_fixpoint() {
        let mut f = Fixture::new();
        let arm = tail_arm(110, vec![pat_unit(111)], resume(lit_int("42", 42)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(110), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let body = bind_expr(
            mv("x", 1),
            yield_log(vec![unit_atom()], crate::ast::NodeId(112)),
            MExpr::Pure(var("x", 1)),
        );
        let prog = val_program(with_expr(handler.clone(), body));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(handler, MExpr::Pure(lit_int("42", 42))))
        );
    }

    #[test]
    fn direct_call_substitutes_supported_var_params() {
        let mut f = Fixture::new();
        let arm = tail_arm(
            120,
            vec![pat_var("msg", 121)],
            resume(var("msg", 121)),
            None,
        );
        f.h.resumption
            .insert(crate::ast::NodeId(120), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let prog = val_program(with_expr(
            handler.clone(),
            yield_log(vec![lit_int("7", 7)], crate::ast::NodeId(122)),
        ));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(handler, MExpr::Pure(lit_int("7", 7))))
        );
    }

    #[test]
    fn direct_call_keeps_oneshot_and_multishot_monadic() {
        for (id, kind) in [
            (130, ResumptionKind::OneShot),
            (131, ResumptionKind::Multishot),
        ] {
            let mut f = Fixture::new();
            let arm = tail_arm(id, vec![pat_unit(id + 10)], resume(lit_int("1", 1)), None);
            f.h.resumption.insert(crate::ast::NodeId(id), kind);
            let handler = static_log_handler(vec![arm]);
            let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(id + 20));
            let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
            let info = f.info();

            let out = run(prog, &f.h, &info);

            assert_eq!(out, val_program(with_expr(handler, yield_expr)));
        }
    }

    #[test]
    fn direct_call_skips_arm_with_finally() {
        let mut f = Fixture::new();
        let arm = tail_arm(
            140,
            vec![pat_unit(141)],
            resume(lit_int("1", 1)),
            Some(MExpr::Pure(unit_atom())),
        );
        f.h.resumption
            .insert(crate::ast::NodeId(140), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(142));
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }

    #[test]
    fn direct_call_skips_multi_arm_same_op_dispatch() {
        let mut f = Fixture::new();
        let arm_a = tail_arm(145, vec![pat_unit(146)], resume(lit_int("1", 1)), None);
        let arm_b = tail_arm(147, vec![pat_unit(148)], resume(lit_int("2", 2)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(145), ResumptionKind::TailResumptive);
        f.h.resumption
            .insert(crate::ast::NodeId(147), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm_a, arm_b]);
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(149));
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }

    #[test]
    fn direct_call_skips_arm_body_with_yield_to_avoid_recursive_expansion() {
        let mut f = Fixture::new();
        let recursive_body = MExpr::Bind {
            var: mv("_", 151),
            value: Box::new(yield_log(vec![unit_atom()], crate::ast::NodeId(152))),
            body: Box::new(resume(unit_atom())),
            mode: crate::codegen::monadic::ir::BindMode::Sequence,
        };
        let arm = tail_arm(153, vec![pat_unit(154)], recursive_body, None);
        f.h.resumption
            .insert(crate::ast::NodeId(153), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(155));
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }

    #[test]
    fn direct_call_dynamic_same_effect_blocks_outer_static_handler() {
        let mut f = Fixture::new();
        let outer_arm = tail_arm(150, vec![pat_unit(151)], resume(lit_int("1", 1)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(150), ResumptionKind::TailResumptive);
        let outer = static_log_handler(vec![outer_arm]);
        let inner = MHandler::Dynamic {
            effects: vec!["Log".to_string()],
            op_tuple: var("dynamic_ops", 152),
            return_lambda: None,
            source: crate::ast::NodeId(153),
        };
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(154));
        let prog = val_program(with_expr(
            outer.clone(),
            with_expr(inner.clone(), yield_expr.clone()),
        ));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(outer, with_expr(inner, yield_expr)))
        );
    }

    #[test]
    fn direct_call_native_same_effect_blocks_outer_static_handler() {
        let mut f = Fixture::new();
        let outer_arm = tail_arm(160, vec![pat_unit(161)], resume(lit_int("1", 1)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(160), ResumptionKind::TailResumptive);
        let outer = static_log_handler(vec![outer_arm]);
        let inner = MHandler::Native {
            effects: vec!["Log".to_string()],
            handler: "native_log".to_string(),
            source: crate::ast::NodeId(162),
        };
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(163));
        let prog = val_program(with_expr(
            outer.clone(),
            with_expr(inner.clone(), yield_expr.clone()),
        ));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(outer, with_expr(inner, yield_expr)))
        );
    }

    #[test]
    fn direct_call_composite_same_effect_is_blocking_not_decomposed() {
        let mut f = Fixture::new();
        let inner_arm = tail_arm(170, vec![pat_unit(171)], resume(lit_int("1", 1)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(170), ResumptionKind::TailResumptive);
        let inner_static = static_log_handler(vec![inner_arm]);
        let composite = MHandler::Composite {
            handlers: vec![inner_static],
            source: crate::ast::NodeId(172),
        };
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(173));
        let prog = val_program(with_expr(composite.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(composite, yield_expr)));
    }

    #[test]
    fn direct_call_does_not_inherit_handler_stack_into_lambda_body() {
        let mut f = Fixture::new();
        let arm = tail_arm(180, vec![pat_unit(181)], resume(lit_int("1", 1)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(180), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let lambda = Atom::Lambda {
            params: vec![pat_unit(182)],
            body: Box::new(yield_log(vec![unit_atom()], crate::ast::NodeId(183))),
            source: crate::ast::NodeId(184),
        };
        let prog = val_program(with_expr(handler.clone(), MExpr::Pure(lambda.clone())));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, MExpr::Pure(lambda))));
    }

    #[test]
    fn direct_call_skips_unsupported_param_patterns() {
        let mut f = Fixture::new();
        let arm = tail_arm(
            190,
            vec![Pat::Tuple {
                id: crate::ast::NodeId(191),
                elements: vec![pat_var("x", 192)],
                span: span(),
            }],
            resume(var("x", 192)),
            None,
        );
        f.h.resumption
            .insert(crate::ast::NodeId(190), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let yield_expr = yield_log(
            vec![Atom::Tuple {
                elements: vec![lit_int("1", 1)],
                source: crate::ast::NodeId(193),
            }],
            crate::ast::NodeId(194),
        );
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }

    fn val_program(value: MExpr) -> MProgram {
        vec![MDecl::Val(MVal {
            id: crate::ast::NodeId(1),
            public: false,
            name: "test_val".to_string(),
            value,
            span: span(),
        })]
    }

    fn bind_pure(var: MVar, value: Atom, body: MExpr) -> MExpr {
        bind_expr(var, MExpr::Pure(value), body)
    }

    fn bind_expr(var: MVar, value: MExpr, body: MExpr) -> MExpr {
        MExpr::Bind {
            var,
            value: Box::new(value),
            body: Box::new(body),
            mode: crate::codegen::monadic::ir::BindMode::Sequence,
        }
    }

    fn mv(name: &str, id: u32) -> MVar {
        MVar {
            name: name.to_string(),
            id,
        }
    }

    fn var(name: &str, id: u32) -> Atom {
        Atom::Var {
            name: mv(name, id),
            source: crate::ast::NodeId(id),
        }
    }

    fn lit_int(raw: &str, value: i64) -> Atom {
        Atom::Lit {
            value: crate::ast::Lit::Int(raw.to_string(), value),
            source: crate::ast::NodeId(value as u32),
        }
    }

    fn unit_atom() -> Atom {
        Atom::Lit {
            value: crate::ast::Lit::Unit,
            source: crate::ast::NodeId(0),
        }
    }

    fn pat_var(name: &str, id: u32) -> Pat {
        Pat::Var {
            name: name.to_string(),
            id: crate::ast::NodeId(id),
            span: span(),
        }
    }

    fn pat_unit(id: u32) -> Pat {
        Pat::Lit {
            id: crate::ast::NodeId(id),
            value: crate::ast::Lit::Unit,
            span: span(),
        }
    }

    fn resume(value: Atom) -> MExpr {
        MExpr::Resume {
            value,
            source: crate::ast::NodeId(999),
        }
    }

    fn yield_log(args: Vec<Atom>, source: crate::ast::NodeId) -> MExpr {
        MExpr::Yield {
            op: log_op(),
            args,
            source,
        }
    }

    fn with_expr(handler: MHandler, body: MExpr) -> MExpr {
        MExpr::With {
            handler,
            body: Box::new(body),
            source: crate::ast::NodeId(998),
        }
    }

    fn static_log_handler(arms: Vec<MHandlerArm>) -> MHandler {
        MHandler::Static {
            effects: vec!["Log".to_string()],
            arms,
            return_clause: None,
            source: crate::ast::NodeId(997),
        }
    }

    fn tail_arm(
        id: u32,
        params: Vec<Pat>,
        body: MExpr,
        finally_block: Option<MExpr>,
    ) -> MHandlerArm {
        MHandlerArm {
            id: crate::ast::NodeId(id),
            op: log_op(),
            params,
            body: Box::new(body),
            finally_block: finally_block.map(Box::new),
            span: span(),
        }
    }

    fn log_op() -> EffectOpRef {
        EffectOpRef {
            effect: "Log".to_string(),
            op: "log".to_string(),
            op_index: 1,
        }
    }

    fn pure_fun_type() -> crate::typechecker::Type {
        crate::typechecker::Type::Fun(
            Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
            Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
            crate::typechecker::EffectRow::empty(),
        )
    }

    fn effectful_fun_type(effect: &str) -> crate::typechecker::Type {
        crate::typechecker::Type::Fun(
            Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
            Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
            crate::typechecker::EffectRow::closed(vec![crate::typechecker::EffectEntry::unnamed(
                effect.to_string(),
                vec![],
            )]),
        )
    }

    fn span() -> crate::token::Span {
        crate::token::Span { start: 0, end: 0 }
    }
}
