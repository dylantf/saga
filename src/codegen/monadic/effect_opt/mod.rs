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
use crate::codegen::native_effects::{NativeArgTransform, native_op};
use crate::typechecker;
use std::collections::{HashMap, HashSet};

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
    inline_candidates: HashMap<String, InlineCandidate>,
    inline_blocked_names: Vec<String>,
}

#[derive(Debug, Clone)]
enum HandlerFrame {
    Static {
        effects: Vec<String>,
        arms: Vec<MHandlerArm>,
    },
    Native {
        effects: Vec<String>,
        handler: String,
    },
    Blocking {
        effects: Vec<String>,
    },
}

#[derive(Debug, Clone)]
struct InlineCandidate {
    params: Vec<Pat>,
    body: MExpr,
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
            inline_candidates: HashMap::new(),
            inline_blocked_names: Vec::new(),
        }
    }

    fn optimize_program(&mut self, mut program: MProgram) -> MProgram {
        let mut changed = true;
        while changed {
            self.inline_candidates = collect_inline_candidates(&program);
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
                let param_names = bound_names_in_pats(&f.params);
                let (body, body_change) =
                    self.optimize_expr_with_blocked_names(param_names, f.body);
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
        let (expr, inline_change) = self.try_inline_helper_call(expr);
        let (expr, native_change) = self.try_native_direct_call(expr);
        let (expr, finally_direct_change) = self.try_finally_direct_call(expr);
        let (expr, direct_change) = self.try_direct_call(expr);
        let (expr, collapse_change) = self.try_bind_collapse(expr);
        let (expr, let_change) = self.try_bind_to_let(expr);
        let mut change = child_change;
        change.mark_if(inline_change);
        change.mark_if(native_change);
        change.mark_if(finally_direct_change);
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
                let (body, body_change) =
                    self.optimize_expr_with_blocked_names(vec![var.name.clone()], *body);
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
                let (body, body_change) =
                    self.optimize_expr_with_blocked_names(vec![var.name.clone()], *body);
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
            MExpr::Ensure { body, cleanup } => {
                let (body, body_change) = self.optimize_expr(*body);
                let (cleanup, cleanup_change) = self.optimize_expr(*cleanup);
                let mut change = body_change;
                change.mark_if(cleanup_change);
                (
                    MExpr::Ensure {
                        body: Box::new(body),
                        cleanup: Box::new(cleanup),
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
                let body_blocked_names = {
                    let mut names = vec![name.clone()];
                    names.extend(bound_names_in_pats(&params));
                    names
                };
                let saved = std::mem::take(&mut self.handler_stack);
                let (body, body_change) =
                    self.optimize_expr_with_blocked_names(body_blocked_names, *body);
                self.handler_stack = saved;
                let (rest, rest_change) =
                    self.optimize_expr_with_blocked_names(vec![name.clone()], *rest);
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
            MExpr::Ensure { .. } => false,
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
        let blocked_names = bound_names_in_pat(&arm.pattern);
        let (guard, guard_change) =
            optimize_optional_expr_with_blocked_names(self, arm.guard, blocked_names.clone());
        let (body, body_change) = self.optimize_expr_with_blocked_names(blocked_names, arm.body);
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
        let blocked_names = bound_names_in_pats(&arm.params);
        let (body, body_change) =
            self.optimize_expr_with_blocked_names(blocked_names.clone(), *arm.body);
        let (finally_block, finally_change) =
            optimize_optional_boxed_expr_with_blocked_names(self, arm.finally_block, blocked_names);
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

    fn optimize_expr_with_blocked_names(
        &mut self,
        names: Vec<String>,
        expr: MExpr,
    ) -> (MExpr, Change) {
        let old_len = self.inline_blocked_names.len();
        self.inline_blocked_names.extend(names);
        let out = self.optimize_expr(expr);
        self.inline_blocked_names.truncate(old_len);
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

    fn try_inline_helper_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.helper_inline() || self.handler_stack.is_empty() {
            return (expr, Change::Unchanged);
        }

        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Atom::Var { name, .. } = &head else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if self.inline_blocked_names.iter().any(|n| n == &name.name) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.inline_candidates.get(&name.name) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        let Some(inlined) = inline_helper_candidate(candidate, &args) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !self.expr_has_direct_call_opportunity(&inlined) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        (inlined, Change::Changed)
    }

    fn expr_has_direct_call_opportunity(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { op, args, .. } => {
                self.resolve_direct_call_arm(op)
                    .is_some_and(|arm| inline_tail_resumptive_arm(arm, args).is_some())
                    || self
                        .resolve_native_direct_call_handler(op)
                        .and_then(|handler| {
                            native_direct_call_expr(handler, op, args, crate::ast::NodeId(0))
                        })
                        .is_some()
            }
            MExpr::Bind { value, body, .. } => {
                if let MExpr::Yield { op, args, .. } = value.as_ref()
                    && (self
                        .resolve_direct_call_arm(op)
                        .is_some_and(|arm| inline_tail_resumptive_arm(arm, args).is_some())
                        || self.resolve_finally_direct_call_arm(op).is_some_and(|arm| {
                            inline_tail_resumptive_arm(arm, args)
                                .and_then(|inlined| inlined.finally_block)
                                .is_some_and(|cleanup| {
                                    cleanup_vars_are_available_at_perform_site(&cleanup, args)
                                })
                        }))
                {
                    return true;
                }
                self.expr_has_direct_call_opportunity(value)
                    || self.expr_has_direct_call_opportunity(body)
            }
            MExpr::Let { value, body, .. } => {
                self.expr_has_direct_call_opportunity(value)
                    || self.expr_has_direct_call_opportunity(body)
            }
            MExpr::Ensure { body, cleanup } => {
                self.expr_has_direct_call_opportunity(body)
                    || self.expr_has_direct_call_opportunity(cleanup)
            }
            MExpr::Pure(atom) => self.atom_has_direct_call_opportunity(atom),
            MExpr::Case { arms, .. } => arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(|guard| self.expr_has_direct_call_opportunity(guard))
                    || self.expr_has_direct_call_opportunity(&arm.body)
            }),
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.expr_has_direct_call_opportunity(then_branch)
                    || self.expr_has_direct_call_opportunity(else_branch)
            }
            MExpr::App { head, args, .. } => {
                self.atom_has_direct_call_opportunity(head)
                    || args
                        .iter()
                        .any(|arg| self.atom_has_direct_call_opportunity(arg))
            }
            MExpr::With { body, .. } => self.expr_has_direct_call_opportunity(body),
            MExpr::Resume { value, .. }
            | MExpr::FieldAccess { record: value, .. }
            | MExpr::DictMethodAccess { dict: value, .. }
            | MExpr::UnaryMinus { value, .. } => self.atom_has_direct_call_opportunity(value),
            MExpr::RecordUpdate { record, fields, .. } => {
                self.atom_has_direct_call_opportunity(record)
                    || fields
                        .iter()
                        .any(|(_, atom)| self.atom_has_direct_call_opportunity(atom))
            }
            MExpr::ForeignCall { args, .. } => args
                .iter()
                .any(|arg| self.atom_has_direct_call_opportunity(arg)),
            MExpr::BinOp { left, right, .. } => {
                self.atom_has_direct_call_opportunity(left)
                    || self.atom_has_direct_call_opportunity(right)
            }
            MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
                self.atom_has_direct_call_opportunity(&seg.value)
                    || seg
                        .size
                        .as_ref()
                        .is_some_and(|size| self.atom_has_direct_call_opportunity(size))
            }),
            MExpr::Receive { arms, after, .. } => {
                arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| self.expr_has_direct_call_opportunity(guard))
                        || self.expr_has_direct_call_opportunity(&arm.body)
                }) || after
                    .as_ref()
                    .is_some_and(|(_, body)| self.expr_has_direct_call_opportunity(body))
            }
            MExpr::LetFun { body, rest, .. } => {
                self.expr_has_direct_call_opportunity(body)
                    || self.expr_has_direct_call_opportunity(rest)
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                arms.iter()
                    .any(|arm| self.handler_arm_has_direct_call_opportunity(arm))
                    || return_clause
                        .as_ref()
                        .is_some_and(|arm| self.handler_arm_has_direct_call_opportunity(arm))
            }
        }
    }

    fn atom_has_direct_call_opportunity(&self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { body, .. } => self.expr_has_direct_call_opportunity(body),
            Atom::Ctor { args, .. } => args
                .iter()
                .any(|arg| self.atom_has_direct_call_opportunity(arg)),
            Atom::Tuple { elements, .. } => elements
                .iter()
                .any(|arg| self.atom_has_direct_call_opportunity(arg)),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .any(|(_, atom)| self.atom_has_direct_call_opportunity(atom)),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. } => false,
        }
    }

    fn handler_arm_has_direct_call_opportunity(&self, arm: &MHandlerArm) -> bool {
        self.expr_has_direct_call_opportunity(&arm.body)
            || arm
                .finally_block
                .as_ref()
                .is_some_and(|cleanup| self.expr_has_direct_call_opportunity(cleanup))
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

        (rewrite_resumes_to_pure(inlined.body), Change::Changed)
    }

    fn try_finally_direct_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.direct_call() {
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

        let MExpr::Yield { op, args, .. } = &*value else {
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

        let Some(arm) = self.resolve_finally_direct_call_arm(op) else {
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

        let Some(inlined) = inline_tail_resumptive_arm(arm, args) else {
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
        let Some(cleanup) = inlined.finally_block else {
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
        if !cleanup_vars_are_available_at_perform_site(&cleanup, args) {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        }

        let continued = MExpr::Bind {
            var,
            value: Box::new(rewrite_resumes_to_pure(inlined.body)),
            body,
            mode,
        };
        (
            MExpr::Ensure {
                body: Box::new(continued),
                cleanup: Box::new(cleanup),
            },
            Change::Changed,
        )
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
                HandlerFrame::Native { effects, .. } if effects.iter().any(|e| e == &op.effect) => {
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

    fn resolve_finally_direct_call_arm(
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
                    let cleanup = arm.finally_block.as_ref()?;
                    if cleanup.contains_resume() {
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
                HandlerFrame::Native { effects, .. } if effects.iter().any(|e| e == &op.effect) => {
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

    fn try_native_direct_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.native_direct_call() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Yield { op, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some(handler) = self.resolve_native_direct_call_handler(&op) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        let Some(direct_call) = native_direct_call_expr(handler, &op, &args, source) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        (direct_call, Change::Changed)
    }

    fn resolve_native_direct_call_handler(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&str> {
        for frame in self.handler_stack.iter().rev() {
            match frame {
                HandlerFrame::Native { effects, handler }
                    if effects.iter().any(|e| e == &op.effect) =>
                {
                    return Some(handler);
                }
                HandlerFrame::Static { effects, .. } | HandlerFrame::Blocking { effects }
                    if effects.iter().any(|e| e == &op.effect) =>
                {
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

    fn native_direct_call(self) -> bool {
        !self.skip
    }

    fn helper_inline(self) -> bool {
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

fn optimize_optional_expr_with_blocked_names(
    optimizer: &mut Optimizer,
    expr: Option<MExpr>,
    names: Vec<String>,
) -> (Option<MExpr>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr_with_blocked_names(names, expr);
            (Some(expr), change)
        }
        None => (None, Change::Unchanged),
    }
}

fn optimize_optional_boxed_expr_with_blocked_names(
    optimizer: &mut Optimizer,
    expr: Option<Box<MExpr>>,
    names: Vec<String>,
) -> (Option<Box<MExpr>>, Change) {
    match expr {
        Some(expr) => {
            let (expr, change) = optimizer.optimize_expr_with_blocked_names(names, *expr);
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

const INLINE_HELPER_BODY_BUDGET: usize = 30;

fn collect_inline_candidates(program: &MProgram) -> HashMap<String, InlineCandidate> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let mut same_module_names = HashSet::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl {
            *counts.entry(f.name.clone()).or_default() += 1;
            same_module_names.insert(f.name.clone());
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if counts.get(&f.name) != Some(&1) {
            continue;
        }
        if f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > INLINE_HELPER_BODY_BUDGET
            || expr_yield_count(&f.body) != 1
            || expr_contains_inline_forbidden_shape(&f.body)
            || expr_calls_any(&f.body, &same_module_names)
        {
            continue;
        }
        candidates.insert(
            f.name.clone(),
            InlineCandidate {
                params: f.params.clone(),
                body: f.body.clone(),
            },
        );
    }
    candidates
}

fn helper_params_are_supported(params: &[Pat]) -> bool {
    params.iter().all(supported_inline_param)
}

fn supported_inline_param(param: &Pat) -> bool {
    matches!(
        param,
        Pat::Var { .. }
            | Pat::Wildcard { .. }
            | Pat::Lit {
                value: crate::ast::Lit::Unit,
                ..
            }
    )
}

fn inline_helper_candidate(candidate: &InlineCandidate, args: &[Atom]) -> Option<MExpr> {
    if args.len() != candidate.params.len() {
        return None;
    }

    let mut body = candidate.body.clone();
    for (param, arg) in candidate.params.iter().zip(args) {
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

fn native_direct_call_expr(
    handler: &str,
    op: &crate::codegen::monadic::ir::EffectOpRef,
    args: &[Atom],
    source: crate::ast::NodeId,
) -> Option<MExpr> {
    let handler_name = handler.rsplit('.').next().unwrap_or(handler);
    if handler_name == "beam_ref" && op.effect == "Std.Ref.Ref" {
        return beam_ref_direct_call_expr(&op.op, args, source);
    }

    if !native_handler_allows_first_order_direct_call(handler, &op.effect) {
        return None;
    }
    let spec = native_op(&op.effect, &op.op)?;
    if spec.erl_module.is_empty() || args.len() != spec.param_count {
        return None;
    }

    let args = match spec.arg_transform {
        NativeArgTransform::Identity => args.to_vec(),
        NativeArgTransform::NoArgs => Vec::new(),
        NativeArgTransform::PrependAtom(_) => return None,
        NativeArgTransform::Reorder(indices) => {
            let mut out = Vec::with_capacity(indices.len());
            for &idx in indices {
                out.push(args.get(idx)?.clone());
            }
            out
        }
        NativeArgTransform::WrapThunk(_) => return None,
    };

    Some(MExpr::ForeignCall {
        module: spec.erl_module.to_string(),
        func: spec.erl_func.to_string(),
        args,
        source,
    })
}

fn native_handler_allows_first_order_direct_call(handler: &str, effect: &str) -> bool {
    let handler = handler.rsplit('.').next().unwrap_or(handler);
    handler == "beam_actor" && effect.starts_with("Std.Actor.")
}

fn beam_ref_direct_call_expr(op: &str, args: &[Atom], source: crate::ast::NodeId) -> Option<MExpr> {
    match op {
        "get" if args.len() == 1 => Some(MExpr::ForeignCall {
            module: "erlang".to_string(),
            func: "get".to_string(),
            args: args.to_vec(),
            source,
        }),
        "set" if args.len() == 2 => {
            let discard = generated_native_var("__native_ref_set", source, 0);
            Some(MExpr::Bind {
                var: discard,
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "put".to_string(),
                    args: args.to_vec(),
                    source,
                }),
                body: Box::new(MExpr::Pure(unit_atom_at(source))),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        "new" if args.len() == 1 => {
            let key = generated_native_var("__native_ref_key", source, 0);
            let discard = generated_native_var("__native_ref_put", source, 1);
            Some(MExpr::Bind {
                var: key.clone(),
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "make_ref".to_string(),
                    args: Vec::new(),
                    source,
                }),
                body: Box::new(MExpr::Bind {
                    var: discard,
                    value: Box::new(MExpr::ForeignCall {
                        module: "erlang".to_string(),
                        func: "put".to_string(),
                        args: vec![
                            Atom::Var {
                                name: key.clone(),
                                source,
                            },
                            args[0].clone(),
                        ],
                        source,
                    }),
                    body: Box::new(MExpr::Pure(Atom::Var { name: key, source })),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            })
        }
        _ => None,
    }
}

fn generated_native_var(prefix: &str, source: crate::ast::NodeId, salt: u32) -> MVar {
    MVar {
        name: format!("{prefix}_{}", source.0),
        id: source.0.saturating_add(salt),
    }
}

fn unit_atom_at(source: crate::ast::NodeId) -> Atom {
    Atom::Lit {
        value: crate::ast::Lit::Unit,
        source,
    }
}

fn expr_node_count(expr: &MExpr) -> usize {
    match expr {
        MExpr::Pure(atom) => 1 + atom_node_count(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => 1 + atoms_node_count(args),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            1 + expr_node_count(value) + expr_node_count(body)
        }
        MExpr::Ensure { body, cleanup } => 1 + expr_node_count(body) + expr_node_count(cleanup),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            1 + atom_node_count(scrutinee)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            1 + atom_node_count(cond) + expr_node_count(then_branch) + expr_node_count(else_branch)
        }
        MExpr::App { head, args, .. } => 1 + atom_node_count(head) + atoms_node_count(args),
        MExpr::With { handler, body, .. } => {
            1 + handler_node_count(handler) + expr_node_count(body)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => 1 + atom_node_count(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            1 + atom_node_count(record)
                + fields
                    .iter()
                    .map(|(_, atom)| atom_node_count(atom))
                    .sum::<usize>()
        }
        MExpr::BinOp { left, right, .. } => 1 + atom_node_count(left) + atom_node_count(right),
        MExpr::BitString { segments, .. } => {
            1 + segments
                .iter()
                .map(|seg| {
                    atom_node_count(&seg.value) + seg.size.as_ref().map_or(0, atom_node_count)
                })
                .sum::<usize>()
        }
        MExpr::Receive { arms, after, .. } => {
            1 + arms
                .iter()
                .map(|arm| {
                    arm.guard.as_ref().map_or(0, expr_node_count) + expr_node_count(&arm.body)
                })
                .sum::<usize>()
                + after.as_ref().map_or(0, |(timeout, body)| {
                    atom_node_count(timeout) + expr_node_count(body)
                })
        }
        MExpr::LetFun { body, rest, .. } => 1 + expr_node_count(body) + expr_node_count(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            1 + arms.iter().map(handler_arm_node_count).sum::<usize>()
                + return_clause
                    .as_ref()
                    .map_or(0, |arm| handler_arm_node_count(arm))
        }
    }
}

fn atom_node_count(atom: &Atom) -> usize {
    match atom {
        Atom::Ctor { args, .. } => 1 + atoms_node_count(args),
        Atom::Tuple { elements, .. } => 1 + atoms_node_count(elements),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            1 + fields
                .iter()
                .map(|(_, atom)| atom_node_count(atom))
                .sum::<usize>()
        }
        Atom::Lambda { body, .. } => 1 + expr_node_count(body),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => 1,
    }
}

fn atoms_node_count(atoms: &[Atom]) -> usize {
    atoms.iter().map(atom_node_count).sum()
}

fn handler_node_count(handler: &MHandler) -> usize {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            1 + arms.iter().map(handler_arm_node_count).sum::<usize>()
                + return_clause.as_ref().map_or(0, handler_arm_node_count)
        }
        MHandler::Native { .. } => 1,
        MHandler::Composite { handlers, .. } => {
            1 + handlers.iter().map(handler_node_count).sum::<usize>()
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => 1 + atom_node_count(op_tuple) + return_lambda.as_ref().map_or(0, atom_node_count),
    }
}

fn handler_arm_node_count(arm: &MHandlerArm) -> usize {
    expr_node_count(&arm.body)
        + arm
            .finally_block
            .as_ref()
            .map_or(0, |cleanup| expr_node_count(cleanup))
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
        MHandler::Native {
            effects, handler, ..
        } => {
            if effects.is_empty() {
                None
            } else {
                Some(HandlerFrame::Native {
                    effects: effects.clone(),
                    handler: handler.clone(),
                })
            }
        }
        MHandler::Dynamic { effects, .. } => blocking_frame(effects.clone()),
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

fn expr_yield_count(expr: &MExpr) -> usize {
    match expr {
        MExpr::Yield { args, .. } => 1 + atoms_yield_count(args),
        MExpr::Pure(atom) => atom_yield_count(atom),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_yield_count(value) + expr_yield_count(body)
        }
        MExpr::Ensure { body, cleanup } => expr_yield_count(body) + expr_yield_count(cleanup),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_yield_count(scrutinee)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard.as_ref().map_or(0, expr_yield_count) + expr_yield_count(&arm.body)
                    })
                    .sum::<usize>()
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => atom_yield_count(cond) + expr_yield_count(then_branch) + expr_yield_count(else_branch),
        MExpr::App { head, args, .. } => atom_yield_count(head) + atoms_yield_count(args),
        MExpr::With { handler, body, .. } => handler_yield_count(handler) + expr_yield_count(body),
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_yield_count(value),
        MExpr::ForeignCall { args, .. } => atoms_yield_count(args),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_yield_count(record)
                + fields
                    .iter()
                    .map(|(_, atom)| atom_yield_count(atom))
                    .sum::<usize>()
        }
        MExpr::BinOp { left, right, .. } => atom_yield_count(left) + atom_yield_count(right),
        MExpr::BitString { segments, .. } => segments
            .iter()
            .map(|seg| atom_yield_count(&seg.value) + seg.size.as_ref().map_or(0, atom_yield_count))
            .sum(),
        MExpr::Receive { arms, after, .. } => {
            arms.iter()
                .map(|arm| {
                    arm.guard.as_ref().map_or(0, expr_yield_count) + expr_yield_count(&arm.body)
                })
                .sum::<usize>()
                + after.as_ref().map_or(0, |(timeout, body)| {
                    atom_yield_count(timeout) + expr_yield_count(body)
                })
        }
        MExpr::LetFun { body, rest, .. } => expr_yield_count(body) + expr_yield_count(rest),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().map(handler_arm_yield_count).sum::<usize>()
                + return_clause
                    .as_ref()
                    .map_or(0, |arm| handler_arm_yield_count(arm))
        }
    }
}

fn atom_yield_count(atom: &Atom) -> usize {
    match atom {
        Atom::Ctor { args, .. } => atoms_yield_count(args),
        Atom::Tuple { elements, .. } => atoms_yield_count(elements),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().map(|(_, atom)| atom_yield_count(atom)).sum()
        }
        Atom::Lambda { body, .. } => expr_yield_count(body),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => 0,
    }
}

fn atoms_yield_count(atoms: &[Atom]) -> usize {
    atoms.iter().map(atom_yield_count).sum()
}

fn handler_yield_count(handler: &MHandler) -> usize {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().map(handler_arm_yield_count).sum::<usize>()
                + return_clause.as_ref().map_or(0, handler_arm_yield_count)
        }
        MHandler::Native { .. } => 0,
        MHandler::Composite { handlers, .. } => handlers.iter().map(handler_yield_count).sum(),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => atom_yield_count(op_tuple) + return_lambda.as_ref().map_or(0, atom_yield_count),
    }
}

fn handler_arm_yield_count(arm: &MHandlerArm) -> usize {
    expr_yield_count(&arm.body)
        + arm
            .finally_block
            .as_ref()
            .map_or(0, |finally_block| expr_yield_count(finally_block))
}

fn expr_contains_yield(expr: &MExpr) -> bool {
    match expr {
        MExpr::Yield { .. } => true,
        MExpr::Pure(atom) => atom_contains_yield(atom),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_yield(value) || expr_contains_yield(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_yield(body) || expr_contains_yield(cleanup)
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

fn expr_contains_inline_forbidden_shape(expr: &MExpr) -> bool {
    match expr {
        MExpr::With { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => true,
        MExpr::Pure(atom) => atom_contains_inline_forbidden_shape(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_inline_forbidden_shape)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_inline_forbidden_shape(value)
                || expr_contains_inline_forbidden_shape(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_inline_forbidden_shape(body)
                || expr_contains_inline_forbidden_shape(cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_inline_forbidden_shape(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_inline_forbidden_shape)
                        || expr_contains_inline_forbidden_shape(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_inline_forbidden_shape(cond)
                || expr_contains_inline_forbidden_shape(then_branch)
                || expr_contains_inline_forbidden_shape(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_inline_forbidden_shape(head)
                || args.iter().any(atom_contains_inline_forbidden_shape)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_inline_forbidden_shape(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_inline_forbidden_shape(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_inline_forbidden_shape(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_inline_forbidden_shape(left)
                || atom_contains_inline_forbidden_shape(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_inline_forbidden_shape(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_inline_forbidden_shape)
        }),
    }
}

fn atom_contains_inline_forbidden_shape(atom: &Atom) -> bool {
    match atom {
        Atom::Lambda { .. } => true,
        Atom::Ctor { args, .. } => args.iter().any(atom_contains_inline_forbidden_shape),
        Atom::Tuple { elements, .. } => elements.iter().any(atom_contains_inline_forbidden_shape),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_contains_inline_forbidden_shape(atom)),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => false,
    }
}

fn expr_calls_any(expr: &MExpr, names: &HashSet<String>) -> bool {
    match expr {
        MExpr::App { head, args, .. } => {
            atom_is_call_to_any(head, names) || args.iter().any(|arg| atom_calls_any(arg, names))
        }
        MExpr::Pure(atom) => atom_calls_any(atom, names),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(|arg| atom_calls_any(arg, names))
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_calls_any(value, names) || expr_calls_any(body, names)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_calls_any(body, names) || expr_calls_any(cleanup, names)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_calls_any(scrutinee, names)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|g| expr_calls_any(g, names))
                        || expr_calls_any(&arm.body, names)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_calls_any(cond, names)
                || expr_calls_any(then_branch, names)
                || expr_calls_any(else_branch, names)
        }
        MExpr::With { handler, body, .. } => {
            handler_calls_any(handler, names) || expr_calls_any(body, names)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_calls_any(value, names),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_calls_any(record, names)
                || fields.iter().any(|(_, atom)| atom_calls_any(atom, names))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_calls_any(left, names) || atom_calls_any(right, names)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_calls_any(&seg.value, names)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(|size| atom_calls_any(size, names))
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard.as_ref().is_some_and(|g| expr_calls_any(g, names))
                    || expr_calls_any(&arm.body, names)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_calls_any(timeout, names) || expr_calls_any(body, names)
            })
        }
        MExpr::LetFun { body, rest, .. } => {
            expr_calls_any(body, names) || expr_calls_any(rest, names)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(|arm| handler_arm_calls_any(arm, names))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_calls_any(arm, names))
        }
    }
}

fn atom_is_call_to_any(atom: &Atom, names: &HashSet<String>) -> bool {
    matches!(atom, Atom::Var { name, .. } if names.contains(&name.name))
}

fn atom_calls_any(atom: &Atom, names: &HashSet<String>) -> bool {
    match atom {
        Atom::Lambda { body, .. } => expr_calls_any(body, names),
        Atom::Ctor { args, .. } => args.iter().any(|arg| atom_calls_any(arg, names)),
        Atom::Tuple { elements, .. } => elements.iter().any(|arg| atom_calls_any(arg, names)),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, atom)| atom_calls_any(atom, names))
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. } => false,
    }
}

fn handler_calls_any(handler: &MHandler, names: &HashSet<String>) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(|arm| handler_arm_calls_any(arm, names))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_calls_any(arm, names))
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => handlers
            .iter()
            .any(|handler| handler_calls_any(handler, names)),
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_calls_any(op_tuple, names)
                || return_lambda
                    .as_ref()
                    .is_some_and(|atom| atom_calls_any(atom, names))
        }
    }
}

fn handler_arm_calls_any(arm: &MHandlerArm, names: &HashSet<String>) -> bool {
    expr_calls_any(&arm.body, names)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|cleanup| expr_calls_any(cleanup, names))
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

fn cleanup_vars_are_available_at_perform_site(cleanup: &MExpr, args: &[Atom]) -> bool {
    let mut available = HashSet::new();
    for arg in args {
        collect_atom_var_names(arg, &mut available);
    }

    let mut cleanup_names = HashSet::new();
    collect_expr_var_names(cleanup, &mut cleanup_names);
    cleanup_names.is_subset(&available)
}

struct InlinedArm {
    body: MExpr,
    finally_block: Option<MExpr>,
}

fn inline_tail_resumptive_arm(arm: &MHandlerArm, args: &[Atom]) -> Option<InlinedArm> {
    if args.len() != arm.params.len() {
        return None;
    }

    let mut body = (*arm.body).clone();
    let mut finally_block = arm.finally_block.as_deref().cloned();
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
                if let Some(cleanup) = finally_block {
                    let substituted = subst_expr(cleanup, &target, arg, &free_names);
                    if substituted.blocked {
                        return None;
                    }
                    finally_block = Some(substituted.value);
                }
            }
            Pat::Wildcard { .. }
            | Pat::Lit {
                value: crate::ast::Lit::Unit,
                ..
            } => {}
            _ => return None,
        }
    }
    Some(InlinedArm {
        body,
        finally_block,
    })
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
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(rewrite_resumes_to_pure(*body)),
            cleanup: Box::new(rewrite_resumes_to_pure(*cleanup)),
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
        MExpr::Ensure { body, cleanup } => {
            let body_out = subst_expr(*body, target, replacement, replacement_free_names);
            let cleanup_out = subst_expr(*cleanup, target, replacement, replacement_free_names);
            combine_pair(body_out, cleanup_out, |body, cleanup| MExpr::Ensure {
                body: Box::new(body),
                cleanup: Box::new(cleanup),
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
        MExpr::Ensure { body, cleanup } => {
            expr_contains_target(body, target) || expr_contains_target(cleanup, target)
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
        MExpr::Ensure { body, cleanup } => {
            collect_expr_var_names(body, out);
            collect_expr_var_names(cleanup, out);
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

fn bound_names_in_pat(pat: &Pat) -> Vec<String> {
    pat_bound_names(pat)
}

fn bound_names_in_pats(pats: &[Pat]) -> Vec<String> {
    pats.iter().flat_map(pat_bound_names).collect()
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
    fn direct_call_with_finally_wraps_resumed_continuation_in_ensure() {
        let mut f = Fixture::new();
        let arm = tail_arm(
            143,
            vec![pat_unit(144)],
            resume(lit_int("1", 1)),
            Some(MExpr::Pure(unit_atom())),
        );
        f.h.resumption
            .insert(crate::ast::NodeId(143), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let body = bind_expr(
            mv("x", 145),
            yield_log(vec![unit_atom()], crate::ast::NodeId(146)),
            MExpr::Pure(var("x", 145)),
        );
        let prog = val_program(with_expr(handler.clone(), body));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::Ensure {
                    body: Box::new(MExpr::Pure(lit_int("1", 1))),
                    cleanup: Box::new(MExpr::Pure(unit_atom())),
                }
            ))
        );
    }

    #[test]
    fn direct_call_with_finally_skips_cleanup_that_uses_arm_local() {
        let mut f = Fixture::new();
        let arm_body = bind_expr(
            mv("resource", 148),
            MExpr::Pure(lit_int("1", 1)),
            resume(var("resource", 148)),
        );
        let arm = tail_arm(
            149,
            vec![pat_unit(150)],
            arm_body,
            Some(MExpr::Pure(var("resource", 148))),
        );
        f.h.resumption
            .insert(crate::ast::NodeId(149), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let body = bind_expr(
            mv("x", 151),
            yield_log(vec![unit_atom()], crate::ast::NodeId(152)),
            MExpr::Pure(var("x", 151)),
        );
        let prog = val_program(with_expr(handler.clone(), body.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        let MDecl::Val(MVal {
            value: MExpr::With { body, .. },
            ..
        }) = &out[0]
        else {
            panic!("expected val with with-expression");
        };
        assert!(matches!(
            &**body,
            MExpr::Bind {
                value,
                ..
            } if matches!(&**value, MExpr::Yield { .. })
        ));
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

    #[test]
    fn native_direct_call_rewrites_identity_op() {
        let f = Fixture::new();
        let handler = native_handler("Std.Actor.Timer", "beam_actor", 200);
        let yield_expr = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 201);
        let prog = val_program(with_expr(handler.clone(), yield_expr));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::ForeignCall {
                    module: "timer".to_string(),
                    func: "sleep".to_string(),
                    args: vec![lit_int("10", 10)],
                    source: crate::ast::NodeId(201),
                }
            ))
        );
    }

    #[test]
    fn native_direct_call_rewrites_no_args_op() {
        let f = Fixture::new();
        let handler = native_handler("Std.Actor.Actor", "beam_actor", 210);
        let yield_expr = yield_native("Std.Actor.Actor", "self", vec![unit_atom()], 211);
        let prog = val_program(with_expr(handler.clone(), yield_expr));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "self".to_string(),
                    args: vec![],
                    source: crate::ast::NodeId(211),
                }
            ))
        );
    }

    #[test]
    fn native_direct_call_rewrites_reordered_args() {
        let f = Fixture::new();
        let handler = native_handler("Std.Actor.Timer", "beam_actor", 220);
        let yield_expr = yield_native(
            "Std.Actor.Timer",
            "send_after",
            vec![lit_int("1", 1), lit_int("2", 2), lit_int("3", 3)],
            221,
        );
        let prog = val_program(with_expr(handler.clone(), yield_expr));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "send_after".to_string(),
                    args: vec![lit_int("2", 2), lit_int("1", 1), lit_int("3", 3)],
                    source: crate::ast::NodeId(221),
                }
            ))
        );
    }

    #[test]
    fn native_direct_call_rewrites_beam_ref_get() {
        let f = Fixture::new();
        let handler = native_handler("Std.Ref.Ref", "beam_ref", 223);
        let yield_expr = yield_native("Std.Ref.Ref", "get", vec![lit_int("1", 1)], 224);
        let prog = val_program(with_expr(handler.clone(), yield_expr));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "get".to_string(),
                    args: vec![lit_int("1", 1)],
                    source: crate::ast::NodeId(224),
                }
            ))
        );
    }

    #[test]
    fn native_direct_call_rewrites_beam_ref_set() {
        let f = Fixture::new();
        let handler = native_handler("Std.Ref.Ref", "beam_ref", 225);
        let yield_expr = yield_native(
            "Std.Ref.Ref",
            "set",
            vec![lit_int("1", 1), lit_int("2", 2)],
            226,
        );
        let prog = val_program(with_expr(handler.clone(), yield_expr));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::Bind {
                    var: MVar {
                        name: "__native_ref_set_226".to_string(),
                        id: 226,
                    },
                    value: Box::new(MExpr::ForeignCall {
                        module: "erlang".to_string(),
                        func: "put".to_string(),
                        args: vec![lit_int("1", 1), lit_int("2", 2)],
                        source: crate::ast::NodeId(226),
                    }),
                    body: Box::new(MExpr::Pure(unit_atom_at(crate::ast::NodeId(226)))),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }
            ))
        );
    }

    #[test]
    fn native_direct_call_rewrites_beam_ref_new() {
        let f = Fixture::new();
        let handler = native_handler("Std.Ref.Ref", "beam_ref", 227);
        let yield_expr = yield_native("Std.Ref.Ref", "new", vec![lit_int("42", 42)], 228);
        let key = MVar {
            name: "__native_ref_key_228".to_string(),
            id: 228,
        };
        let prog = val_program(with_expr(handler.clone(), yield_expr));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(
                handler,
                MExpr::Bind {
                    var: key.clone(),
                    value: Box::new(MExpr::ForeignCall {
                        module: "erlang".to_string(),
                        func: "make_ref".to_string(),
                        args: vec![],
                        source: crate::ast::NodeId(228),
                    }),
                    body: Box::new(MExpr::Bind {
                        var: MVar {
                            name: "__native_ref_put_228".to_string(),
                            id: 229,
                        },
                        value: Box::new(MExpr::ForeignCall {
                            module: "erlang".to_string(),
                            func: "put".to_string(),
                            args: vec![
                                Atom::Var {
                                    name: key.clone(),
                                    source: crate::ast::NodeId(228),
                                },
                                lit_int("42", 42),
                            ],
                            source: crate::ast::NodeId(228),
                        }),
                        body: Box::new(MExpr::Pure(Atom::Var {
                            name: key,
                            source: crate::ast::NodeId(228),
                        })),
                        mode: crate::codegen::monadic::ir::BindMode::Sequence,
                    }),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }
            ))
        );
    }

    #[test]
    fn native_direct_call_skips_prepend_atom_and_spawn() {
        for (effect, op, args, source) in [
            (
                "Std.Actor.Monitor",
                "monitor",
                vec![lit_int("1", 1)],
                crate::ast::NodeId(230),
            ),
            (
                "Std.Actor.Process",
                "spawn",
                vec![unit_atom()],
                crate::ast::NodeId(231),
            ),
        ] {
            let f = Fixture::new();
            let handler = native_handler(effect, "beam_actor", source.0 + 10);
            let yield_expr = yield_native(effect, op, args, source.0);
            let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
            let info = f.info();

            let out = run(prog, &f.h, &info);

            assert_eq!(out, val_program(with_expr(handler, yield_expr)));
        }
    }

    #[test]
    fn native_direct_call_skips_ref_vec_and_unknown_handler_backends() {
        for (effect, handler_name, op, args, source) in [
            (
                "Std.Ref.Ref",
                "ets_ref",
                "get",
                vec![lit_int("1", 1)],
                crate::ast::NodeId(241),
            ),
            (
                "Std.Vec.Vec",
                "beam_vec",
                "vec_len",
                vec![lit_int("1", 1)],
                crate::ast::NodeId(242),
            ),
            (
                "Std.Ref.Ref",
                "beam_ref",
                "modify",
                vec![lit_int("1", 1), unit_atom()],
                crate::ast::NodeId(243),
            ),
        ] {
            let f = Fixture::new();
            let handler = native_handler(effect, handler_name, source.0 + 10);
            let yield_expr = yield_native(effect, op, args, source.0);
            let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
            let info = f.info();

            let out = run(prog, &f.h, &info);

            assert_eq!(out, val_program(with_expr(handler, yield_expr)));
        }
    }

    #[test]
    fn native_direct_call_respects_inner_blockers() {
        let f = Fixture::new();
        let outer = native_handler("Std.Actor.Timer", "beam_actor", 250);
        let dynamic = MHandler::Dynamic {
            effects: vec!["Std.Actor.Timer".to_string()],
            op_tuple: var("ops", 251),
            return_lambda: None,
            source: crate::ast::NodeId(252),
        };
        let yield_expr = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 253);
        let prog = val_program(with_expr(
            outer.clone(),
            with_expr(dynamic.clone(), yield_expr.clone()),
        ));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(outer, with_expr(dynamic, yield_expr)))
        );
    }

    #[test]
    fn native_direct_call_respects_static_and_composite_blockers() {
        let f = Fixture::new();
        let outer = native_handler("Std.Actor.Timer", "beam_actor", 260);
        let blocking_arm = MHandlerArm {
            id: crate::ast::NodeId(261),
            op: effect_op("Std.Actor.Timer", "sleep", 2),
            params: vec![pat_var("ms", 262)],
            body: Box::new(resume(var("ms", 262))),
            finally_block: None,
            span: span(),
        };
        let static_inner = MHandler::Static {
            effects: vec!["Std.Actor.Timer".to_string()],
            arms: vec![blocking_arm],
            return_clause: None,
            source: crate::ast::NodeId(263),
        };
        let composite = MHandler::Composite {
            handlers: vec![native_handler("Std.Actor.Timer", "beam_actor", 264)],
            source: crate::ast::NodeId(265),
        };

        for inner in [static_inner, composite] {
            let yield_expr = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 266);
            let prog = val_program(with_expr(
                outer.clone(),
                with_expr(inner.clone(), yield_expr.clone()),
            ));
            let info = f.info();

            let out = run(prog, &f.h, &info);

            assert_eq!(
                out,
                val_program(with_expr(outer.clone(), with_expr(inner, yield_expr)))
            );
        }
    }

    #[test]
    fn native_direct_call_skips_unknown_op_and_arg_mismatch() {
        for (op, args, source) in [
            ("missing", vec![lit_int("1", 1)], crate::ast::NodeId(270)),
            ("sleep", vec![], crate::ast::NodeId(271)),
        ] {
            let f = Fixture::new();
            let handler = native_handler("Std.Actor.Timer", "beam_actor", source.0 + 10);
            let yield_expr = yield_native("Std.Actor.Timer", op, args, source.0);
            let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
            let info = f.info();

            let out = run(prog, &f.h, &info);

            assert_eq!(out, val_program(with_expr(handler, yield_expr)));
        }
    }

    #[test]
    fn helper_inline_exposes_yield_to_static_direct_call() {
        let mut f = Fixture::new();
        let arm = tail_arm(280, vec![pat_unit(281)], resume(lit_int("42", 42)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(280), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let helper = helper_fun(
            "helper",
            282,
            vec![pat_unit(283)],
            yield_log(vec![unit_atom()], crate::ast::NodeId(284)),
        );
        let caller = MDecl::Val(MVal {
            id: crate::ast::NodeId(285),
            public: false,
            name: "caller".to_string(),
            value: with_expr(
                handler.clone(),
                MExpr::App {
                    head: var("helper", 286),
                    args: vec![unit_atom()],
                    source: crate::ast::NodeId(287),
                },
            ),
            span: span(),
        });
        let info = f.info();

        let out = run(vec![helper.clone(), caller], &f.h, &info);

        assert_eq!(
            out,
            vec![
                helper,
                MDecl::Val(MVal {
                    id: crate::ast::NodeId(285),
                    public: false,
                    name: "caller".to_string(),
                    value: with_expr(handler, MExpr::Pure(lit_int("42", 42))),
                    span: span(),
                })
            ]
        );
    }

    #[test]
    fn helper_inline_skips_multi_clause_function() {
        let mut f = Fixture::new();
        let arm = tail_arm(290, vec![pat_unit(291)], resume(lit_int("42", 42)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(290), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let helper_a = helper_fun(
            "helper",
            292,
            vec![pat_unit(293)],
            yield_log(vec![unit_atom()], crate::ast::NodeId(294)),
        );
        let helper_b = helper_fun(
            "helper",
            295,
            vec![pat_var("x", 296)],
            MExpr::Pure(var("x", 296)),
        );
        let call = MExpr::App {
            head: var("helper", 297),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(298),
        };
        let caller = MDecl::Val(MVal {
            id: crate::ast::NodeId(299),
            public: false,
            name: "caller".to_string(),
            value: with_expr(handler.clone(), call.clone()),
            span: span(),
        });
        let info = f.info();

        let out = run(
            vec![helper_a.clone(), helper_b.clone(), caller],
            &f.h,
            &info,
        );

        assert_eq!(
            out,
            vec![
                helper_a,
                helper_b,
                MDecl::Val(MVal {
                    id: crate::ast::NodeId(299),
                    public: false,
                    name: "caller".to_string(),
                    value: with_expr(handler, call),
                    span: span(),
                })
            ]
        );
    }

    #[test]
    fn helper_inline_respects_dynamic_same_effect_blocker() {
        let mut f = Fixture::new();
        let arm = tail_arm(300, vec![pat_unit(301)], resume(lit_int("42", 42)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(300), ResumptionKind::TailResumptive);
        let outer = static_log_handler(vec![arm]);
        let dynamic = MHandler::Dynamic {
            effects: vec!["Log".to_string()],
            op_tuple: var("ops", 302),
            return_lambda: None,
            source: crate::ast::NodeId(303),
        };
        let helper = helper_fun(
            "helper",
            304,
            vec![pat_unit(305)],
            yield_log(vec![unit_atom()], crate::ast::NodeId(306)),
        );
        let caller = MDecl::Val(MVal {
            id: crate::ast::NodeId(307),
            public: false,
            name: "caller".to_string(),
            value: with_expr(
                outer.clone(),
                with_expr(
                    dynamic.clone(),
                    MExpr::App {
                        head: var("helper", 308),
                        args: vec![unit_atom()],
                        source: crate::ast::NodeId(309),
                    },
                ),
            ),
            span: span(),
        });
        let info = f.info();

        let out = run(vec![helper.clone(), caller], &f.h, &info);

        assert_eq!(
            out,
            vec![
                helper,
                MDecl::Val(MVal {
                    id: crate::ast::NodeId(307),
                    public: false,
                    name: "caller".to_string(),
                    value: with_expr(
                        outer,
                        with_expr(
                            dynamic,
                            MExpr::App {
                                head: var("helper", 308),
                                args: vec![unit_atom()],
                                source: crate::ast::NodeId(309),
                            }
                        )
                    ),
                    span: span(),
                })
            ]
        );
    }

    #[test]
    fn helper_inline_skips_multi_yield_helper() {
        let mut f = Fixture::new();
        let arm = tail_arm(310, vec![pat_unit(311)], resume(lit_int("42", 42)), None);
        f.h.resumption
            .insert(crate::ast::NodeId(310), ResumptionKind::TailResumptive);
        let handler = static_log_handler(vec![arm]);
        let helper_body = bind_expr(
            mv("_", 312),
            yield_log(vec![unit_atom()], crate::ast::NodeId(313)),
            yield_fail(vec![lit_int("1", 1)], crate::ast::NodeId(314)),
        );
        let helper = helper_fun("helper", 315, vec![pat_unit(316)], helper_body);
        let call = MExpr::App {
            head: var("helper", 317),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(318),
        };
        let caller = MDecl::Val(MVal {
            id: crate::ast::NodeId(319),
            public: false,
            name: "caller".to_string(),
            value: with_expr(handler.clone(), call.clone()),
            span: span(),
        });
        let info = f.info();

        let out = run(vec![helper.clone(), caller], &f.h, &info);

        assert_eq!(
            out,
            vec![
                helper,
                MDecl::Val(MVal {
                    id: crate::ast::NodeId(319),
                    public: false,
                    name: "caller".to_string(),
                    value: with_expr(handler, call),
                    span: span(),
                })
            ]
        );
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

    fn helper_fun(name: &str, id: u32, params: Vec<Pat>, body: MExpr) -> MDecl {
        MDecl::FunBinding(MFunBinding {
            id: crate::ast::NodeId(id),
            name: name.to_string(),
            name_span: span(),
            params,
            guard: None,
            body,
            span: span(),
        })
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

    fn yield_fail(args: Vec<Atom>, source: crate::ast::NodeId) -> MExpr {
        MExpr::Yield {
            op: effect_op("Std.Fail.Fail", "fail", 1),
            args,
            source,
        }
    }

    fn yield_native(effect: &str, op: &str, args: Vec<Atom>, source: u32) -> MExpr {
        MExpr::Yield {
            op: effect_op(effect, op, 0),
            args,
            source: crate::ast::NodeId(source),
        }
    }

    fn effect_op(effect: &str, op: &str, op_index: u32) -> EffectOpRef {
        EffectOpRef {
            effect: effect.to_string(),
            op: op.to_string(),
            op_index,
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

    fn native_handler(effect: &str, handler: &str, source: u32) -> MHandler {
        MHandler::Native {
            effects: vec![effect.to_string()],
            handler: handler.to_string(),
            source: crate::ast::NodeId(source),
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
