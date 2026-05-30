// effect_opt/ — monadic IR optimization stage.
//
// Currently implements step 9:
//   - bind collapse — Bind(Pure(a), x, B) → B[x := a]
//
// Still deferred:
//   - step 10: bind_to_let.rs     — Bind → Let where value is pure
//   - step 11: direct_call.rs     — tail-resumptive Yield → inlined arm body
//
// See docs/planning/uniform-effect-translation/effect-optimization-spec.md
// for rewrite specifications, soundness conditions, and fixpoint strategy.

use crate::ast::{
    ComprehensionQualifier, Expr, ExprKind, Handler, HandlerItem, Pat, Stmt, StringPart,
};
use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, MArm, MDecl, MDictConstructor, MExpr, MFunBinding, MHandler, MHandlerArm,
    MProgram, MVal, MVar,
};
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
    _h: &HandlerAnalysis,
    _e: &EffectInfo,
    opts: RunOptions,
) -> MProgram {
    if opts.skip {
        return m;
    }

    let mut optimizer = Optimizer::new(opts);
    optimizer.optimize_program(m)
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RunOptions {
    /// Emit no-op even after rewrites land. Useful for benchmarking and
    /// bisecting miscompiles between the translator and the optimizer.
    pub skip: bool,
}

struct Optimizer {
    opts: RunOptions,
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

impl Optimizer {
    fn new(opts: RunOptions) -> Self {
        Self { opts }
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
        let (expr, local_change) = self.try_bind_collapse(expr);
        let mut change = child_change;
        change.mark_if(local_change);
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
                let (handler, handler_change) = self.optimize_handler(handler);
                let (body, body_change) = self.optimize_expr(*body);
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
                let (body, body_change) = self.optimize_expr(*body);
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
                let (body, change) = self.optimize_expr(*body);
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
}

impl RunOptions {
    fn bind_collapse(self) -> bool {
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
    use crate::codegen::monadic::ir::MProgram;
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
    fn bind_collapse_blocks_pattern_capture() {
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

        let out = run(prog.clone(), &f.h, &info);

        assert_eq!(out, prog);
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
        MExpr::Bind {
            var,
            value: Box::new(MExpr::Pure(value)),
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

    fn pat_var(name: &str, id: u32) -> Pat {
        Pat::Var {
            name: name.to_string(),
            id: crate::ast::NodeId(id),
            span: span(),
        }
    }

    fn span() -> crate::token::Span {
        crate::token::Span { start: 0, end: 0 }
    }
}
