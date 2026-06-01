//! Early specialization for statically-known reader/config handlers.
//!
//! This pass is intentionally narrow. It recognizes static handler arms of
//! the shape `op () = resume value` and rewrites matching `Yield`s in the
//! handled body to that value before the general handler protocol reaches Core
//! lowering.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use crate::ast::{Lit, NodeId, Pat};
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, EffectOpRef, MArm, MDecl, MExpr, MFunBinding, MHandler, MHandlerArm, MProgram,
};
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use crate::codegen::type_shape;

#[derive(Debug, Clone, PartialEq)]
enum HandlerFrame {
    Reader {
        op: EffectOpRef,
        replacement: Box<MExpr>,
        free_names: HashSet<String>,
    },
    Blocking {
        effects: Vec<String>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Change(bool);

impl Change {
    const UNCHANGED: Self = Self(false);
    const CHANGED: Self = Self(true);

    fn mark_if(&mut self, other: Self) {
        self.0 |= other.0;
    }
}

/// Run the static reader-handler specialization pass.
pub fn run(
    program: MProgram,
    effect_info: &EffectInfo<'_>,
    resolution: &ResolutionMap,
) -> MProgram {
    let functions = program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f) if !f.name.starts_with(STATIC_READER_VARIANT_PREFIX) => {
                Some((f.name.clone(), f.clone()))
            }
            _ => None,
        })
        .collect();
    let mut pass = ReaderSpecializer {
        effect_info,
        resolution,
        functions,
        variant_cache: HashMap::new(),
        generated_variants: Vec::new(),
    };
    let mut out: MProgram = program
        .into_iter()
        .map(|decl| pass.optimize_decl(decl).0)
        .collect();
    out.extend(pass.generated_variants.into_iter().map(MDecl::FunBinding));
    out
}

struct ReaderSpecializer<'a, 'info> {
    effect_info: &'a EffectInfo<'info>,
    resolution: &'a ResolutionMap,
    functions: HashMap<String, MFunBinding>,
    variant_cache: HashMap<(String, String), String>,
    generated_variants: Vec<MFunBinding>,
}

const STATIC_READER_VARIANT_PREFIX: &str = "__saga_static_variant__reader";

impl ReaderSpecializer<'_, '_> {
    fn optimize_decl(&mut self, decl: MDecl) -> (MDecl, Change) {
        match decl {
            MDecl::FunBinding(mut fb) => {
                let mut scope = HashSet::new();
                for param in &fb.params {
                    collect_pat_binders(param, &mut scope);
                }
                let (body, change) = self.optimize_expr(fb.body, &[], &scope);
                fb.body = body;
                (MDecl::FunBinding(fb), change)
            }
            MDecl::Val(mut val) => {
                let (value, change) = self.optimize_expr(val.value, &[], &HashSet::new());
                val.value = value;
                (MDecl::Val(val), change)
            }
            MDecl::DictConstructor(mut dict) => {
                let mut change = Change::UNCHANGED;
                dict.methods = dict
                    .methods
                    .into_iter()
                    .map(|method| {
                        let (method, method_change) =
                            self.optimize_expr(method, &[], &HashSet::new());
                        change.mark_if(method_change);
                        method
                    })
                    .collect();
                (MDecl::DictConstructor(dict), change)
            }
            MDecl::Passthrough(_) => (decl, Change::UNCHANGED),
        }
    }

    fn optimize_expr(
        &mut self,
        expr: MExpr,
        stack: &[HandlerFrame],
        scoped_names: &HashSet<String>,
    ) -> (MExpr, Change) {
        match expr {
            MExpr::Pure(atom) => {
                let (atom, change) = self.optimize_atom(atom);
                (MExpr::Pure(atom), change)
            }
            MExpr::Yield { op, args, source } => {
                let mut change = Change::UNCHANGED;
                let args = args
                    .into_iter()
                    .map(|arg| {
                        let (arg, arg_change) = self.optimize_atom(arg);
                        change.mark_if(arg_change);
                        arg
                    })
                    .collect::<Vec<_>>();

                if let Some(replacement) = self.reader_replacement(stack, &op, scoped_names) {
                    return (replacement, Change::CHANGED);
                }

                (MExpr::Yield { op, args, source }, change)
            }
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => {
                let (value, value_change) = self.optimize_expr(*value, stack, scoped_names);
                let mut body_scope = scoped_names.clone();
                body_scope.insert(var.name.clone());
                let (body, body_change) = self.optimize_expr(*body, stack, &body_scope);
                let mut change = value_change;
                change.mark_if(body_change);
                if self.expr_is_non_yielding(&value) {
                    return (
                        MExpr::Let {
                            var,
                            value: Box::new(value),
                            body: Box::new(body),
                        },
                        Change::CHANGED,
                    );
                }
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
                let (value, value_change) = self.optimize_expr(*value, stack, scoped_names);
                let mut body_scope = scoped_names.clone();
                body_scope.insert(var.name.clone());
                let (body, body_change) = self.optimize_expr(*body, stack, &body_scope);
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
                let (body, body_change) = self.optimize_expr(*body, stack, scoped_names);
                let (cleanup, cleanup_change) = self.optimize_expr(*cleanup, stack, scoped_names);
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
                let (scrutinee, scrut_change) = self.optimize_atom(scrutinee);
                let mut change = scrut_change;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, arm_change) = self.optimize_arm(arm, stack, scoped_names);
                        change.mark_if(arm_change);
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
                let (then_branch, then_change) =
                    self.optimize_expr(*then_branch, stack, scoped_names);
                let (else_branch, else_change) =
                    self.optimize_expr(*else_branch, stack, scoped_names);
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
                let mut change = head_change;
                let args = args
                    .into_iter()
                    .map(|arg| {
                        let (arg, arg_change) = self.optimize_atom(arg);
                        change.mark_if(arg_change);
                        arg
                    })
                    .collect();
                if let Some(variant_head) = self.reader_variant_head(&head, stack) {
                    return (
                        MExpr::App {
                            head: variant_head,
                            args,
                            source,
                        },
                        Change::CHANGED,
                    );
                }
                (MExpr::App { head, args, source }, change)
            }
            MExpr::With {
                handler,
                body,
                source,
            } => {
                let (handler, handler_change) = self.optimize_handler(handler);
                let mut body_stack = stack.to_vec();
                body_stack.extend(self.frames_for_handler(&handler));
                let (body, body_change) = self.optimize_expr(*body, &body_stack, scoped_names);
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
                let mut change = record_change;
                let fields = fields
                    .into_iter()
                    .map(|(name, atom)| {
                        let (atom, atom_change) = self.optimize_atom(atom);
                        change.mark_if(atom_change);
                        (name, atom)
                    })
                    .collect();
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
                let mut change = Change::UNCHANGED;
                let args = args
                    .into_iter()
                    .map(|arg| {
                        let (arg, arg_change) = self.optimize_atom(arg);
                        change.mark_if(arg_change);
                        arg
                    })
                    .collect();
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
                let mut change = Change::UNCHANGED;
                let segments = segments
                    .into_iter()
                    .map(|mut segment| {
                        let (value, value_change) = self.optimize_atom(segment.value);
                        segment.value = value;
                        change.mark_if(value_change);
                        segment
                    })
                    .collect();
                (MExpr::BitString { segments, source }, change)
            }
            MExpr::Receive {
                arms,
                after,
                source,
            } => {
                let mut change = Change::UNCHANGED;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, arm_change) = self.optimize_arm(arm, stack, scoped_names);
                        change.mark_if(arm_change);
                        arm
                    })
                    .collect();
                let after = after.map(|(timeout, body)| {
                    let (timeout, timeout_change) = self.optimize_atom(timeout);
                    let (body, body_change) = self.optimize_expr(*body, stack, scoped_names);
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
                let (body, body_change) = self.optimize_expr(*body, &[], &HashSet::new());
                let (rest, rest_change) = self.optimize_expr(*rest, stack, scoped_names);
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
                let mut change = Change::UNCHANGED;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, arm_change) =
                            self.optimize_handler_arm(arm, &[], &HashSet::new());
                        change.mark_if(arm_change);
                        arm
                    })
                    .collect();
                let return_clause = return_clause.map(|arm| {
                    let (arm, arm_change) = self.optimize_handler_arm(*arm, &[], &HashSet::new());
                    change.mark_if(arm_change);
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

    fn optimize_atom(&mut self, atom: Atom) -> (Atom, Change) {
        match atom {
            Atom::Lambda {
                params,
                body,
                source,
            } => {
                let (body, change) = self.optimize_expr(*body, &[], &HashSet::new());
                (
                    Atom::Lambda {
                        params,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            Atom::Ctor { name, args, source } => {
                let mut change = Change::UNCHANGED;
                let args = args
                    .into_iter()
                    .map(|arg| {
                        let (arg, arg_change) = self.optimize_atom(arg);
                        change.mark_if(arg_change);
                        arg
                    })
                    .collect();
                (Atom::Ctor { name, args, source }, change)
            }
            Atom::Tuple { elements, source } => {
                let mut change = Change::UNCHANGED;
                let elements = elements
                    .into_iter()
                    .map(|element| {
                        let (element, element_change) = self.optimize_atom(element);
                        change.mark_if(element_change);
                        element
                    })
                    .collect();
                (Atom::Tuple { elements, source }, change)
            }
            Atom::AnonRecord { fields, source } => {
                let mut change = Change::UNCHANGED;
                let fields = fields
                    .into_iter()
                    .map(|(name, atom)| {
                        let (atom, atom_change) = self.optimize_atom(atom);
                        change.mark_if(atom_change);
                        (name, atom)
                    })
                    .collect();
                (Atom::AnonRecord { fields, source }, change)
            }
            Atom::Record {
                name,
                fields,
                source,
            } => {
                let mut change = Change::UNCHANGED;
                let fields = fields
                    .into_iter()
                    .map(|(field, atom)| {
                        let (atom, atom_change) = self.optimize_atom(atom);
                        change.mark_if(atom_change);
                        (field, atom)
                    })
                    .collect();
                (
                    Atom::Record {
                        name,
                        fields,
                        source,
                    },
                    change,
                )
            }
            Atom::BackendSpawnThunk { callback, source } => {
                let (callback, change) = self.optimize_atom(*callback);
                (
                    Atom::BackendSpawnThunk {
                        callback: Box::new(callback),
                        source,
                    },
                    change,
                )
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => (atom, Change::UNCHANGED),
        }
    }

    fn optimize_arm(
        &mut self,
        arm: MArm,
        stack: &[HandlerFrame],
        scoped_names: &HashSet<String>,
    ) -> (MArm, Change) {
        let mut arm_scope = scoped_names.clone();
        collect_pat_binders(&arm.pattern, &mut arm_scope);
        let guard = match arm.guard {
            Some(guard) => {
                let (guard, _) = self.optimize_expr(guard, &[], &HashSet::new());
                Some(guard)
            }
            None => None,
        };
        let (body, body_change) = self.optimize_expr(arm.body, stack, &arm_scope);
        (
            MArm {
                pattern: arm.pattern,
                guard,
                body,
                span: arm.span,
            },
            body_change,
        )
    }

    fn optimize_handler(&mut self, handler: MHandler) -> (MHandler, Change) {
        match handler {
            MHandler::Static {
                effects,
                arms,
                return_clause,
                source,
            } => {
                let mut change = Change::UNCHANGED;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, arm_change) =
                            self.optimize_handler_arm(arm, &[], &HashSet::new());
                        change.mark_if(arm_change);
                        arm
                    })
                    .collect();
                let return_clause = return_clause.map(|arm| {
                    let (arm, arm_change) = self.optimize_handler_arm(arm, &[], &HashSet::new());
                    change.mark_if(arm_change);
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
            MHandler::Composite { handlers, source } => {
                let mut change = Change::UNCHANGED;
                let handlers = handlers
                    .into_iter()
                    .map(|handler| {
                        let (handler, handler_change) = self.optimize_handler(handler);
                        change.mark_if(handler_change);
                        handler
                    })
                    .collect();
                (MHandler::Composite { handlers, source }, change)
            }
            MHandler::Dynamic { .. } | MHandler::Native { .. } => (handler, Change::UNCHANGED),
        }
    }

    fn optimize_handler_arm(
        &mut self,
        arm: MHandlerArm,
        stack: &[HandlerFrame],
        scoped_names: &HashSet<String>,
    ) -> (MHandlerArm, Change) {
        let mut arm_scope = scoped_names.clone();
        for param in &arm.params {
            collect_pat_binders(param, &mut arm_scope);
        }
        let (body, body_change) = self.optimize_expr(*arm.body, stack, &arm_scope);
        let finally_block = arm.finally_block.map(|cleanup| {
            let (cleanup, cleanup_change) = self.optimize_expr(*cleanup, stack, scoped_names);
            let _ = cleanup_change;
            Box::new(cleanup)
        });
        (
            MHandlerArm {
                id: arm.id,
                op: arm.op,
                params: arm.params,
                body: Box::new(body),
                finally_block,
                span: arm.span,
            },
            body_change,
        )
    }

    fn frames_for_handler(&self, handler: &MHandler) -> Vec<HandlerFrame> {
        match handler {
            MHandler::Static {
                effects,
                arms,
                return_clause,
                ..
            } => {
                let mut frames = vec![HandlerFrame::Blocking {
                    effects: effects.clone(),
                }];
                if return_clause.is_none() {
                    for arm in arms {
                        let matching_arms = arms
                            .iter()
                            .filter(|candidate| {
                                candidate.op.effect == arm.op.effect && candidate.op.op == arm.op.op
                            })
                            .count();
                        if matching_arms == 1
                            && let Some(replacement) = self.reader_replacement_for_arm(arm)
                        {
                            let free_names = expr_free_names(&replacement);
                            frames.push(HandlerFrame::Reader {
                                op: arm.op.clone(),
                                replacement: Box::new(replacement),
                                free_names,
                            });
                        }
                    }
                }
                frames
            }
            MHandler::Dynamic { effects, .. } | MHandler::Native { effects, .. } => {
                vec![HandlerFrame::Blocking {
                    effects: effects.clone(),
                }]
            }
            MHandler::Composite { handlers, .. } => vec![HandlerFrame::Blocking {
                effects: handlers.iter().flat_map(handler_effects).collect(),
            }],
        }
    }

    fn reader_replacement(
        &self,
        stack: &[HandlerFrame],
        op: &EffectOpRef,
        scoped_names: &HashSet<String>,
    ) -> Option<MExpr> {
        for frame in stack.iter().rev() {
            match frame {
                HandlerFrame::Reader {
                    op: frame_op,
                    replacement,
                    free_names,
                } if frame_op.effect == op.effect && frame_op.op == op.op => {
                    if free_names.iter().any(|name| scoped_names.contains(name)) {
                        return None;
                    }
                    return Some((**replacement).clone());
                }
                HandlerFrame::Blocking { effects } if effects.iter().any(|e| e == &op.effect) => {
                    return None;
                }
                _ => {}
            }
        }
        None
    }

    fn reader_replacement_for_arm(&self, arm: &MHandlerArm) -> Option<MExpr> {
        if arm.finally_block.is_some() || !arm.params.iter().all(is_ignored_reader_param) {
            return None;
        }
        self.reader_body_to_expr(&arm.body)
    }

    fn reader_body_to_expr(&self, body: &MExpr) -> Option<MExpr> {
        match body {
            MExpr::Resume { value, .. } => Some(MExpr::Pure(value.clone())),
            MExpr::Let { var, value, body } if self.expr_is_non_yielding(value) => {
                let body = self.reader_body_to_expr(body)?;
                Some(MExpr::Let {
                    var: var.clone(),
                    value: value.clone(),
                    body: Box::new(body),
                })
            }
            MExpr::Bind {
                var, value, body, ..
            } if self.expr_is_non_yielding(value) => {
                let body = self.reader_body_to_expr(body)?;
                Some(MExpr::Let {
                    var: var.clone(),
                    value: value.clone(),
                    body: Box::new(body),
                })
            }
            _ => None,
        }
    }

    fn expr_is_non_yielding(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => atom_is_non_yielding(atom),
            MExpr::Let { value, body, .. } | MExpr::Bind { value, body, .. } => {
                self.expr_is_non_yielding(value) && self.expr_is_non_yielding(body)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                atom_is_non_yielding(scrutinee)
                    && arms.iter().all(|arm| {
                        arm.guard
                            .as_ref()
                            .is_none_or(|g| self.expr_is_non_yielding(g))
                            && self.expr_is_non_yielding(&arm.body)
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                atom_is_non_yielding(cond)
                    && self.expr_is_non_yielding(then_branch)
                    && self.expr_is_non_yielding(else_branch)
            }
            MExpr::App { head, args, .. } => {
                atom_is_non_yielding(head)
                    && args.iter().all(atom_is_non_yielding)
                    && self.app_head_is_closed_empty_effect_row(head)
            }
            MExpr::FieldAccess { record, .. } => atom_is_non_yielding(record),
            MExpr::RecordUpdate { record, fields, .. } => {
                atom_is_non_yielding(record)
                    && fields.iter().all(|(_, atom)| atom_is_non_yielding(atom))
            }
            MExpr::DictMethodAccess { dict, .. } => atom_is_non_yielding(dict),
            MExpr::BinOp { left, right, .. } => {
                atom_is_non_yielding(left) && atom_is_non_yielding(right)
            }
            MExpr::UnaryMinus { value, .. } => atom_is_non_yielding(value),
            MExpr::BitString { segments, .. } => segments
                .iter()
                .all(|segment| atom_is_non_yielding(&segment.value)),
            MExpr::ForeignCall { .. }
            | MExpr::Yield { .. }
            | MExpr::Ensure { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
        }
    }

    fn app_head_is_closed_empty_effect_row(&self, head: &Atom) -> bool {
        let source = atom_source(head);
        if let Some(ty) = self.effect_info.type_at_node.get(&source) {
            let (_, effects, has_open_row) = type_shape::arity_and_evidence_from_type(ty);
            return effects.is_empty() && !has_open_row;
        }

        if let Some(resolved) = self.resolution.get(&source) {
            return match &resolved.kind {
                ResolvedCodegenKind::BeamFunction { effects, .. }
                | ResolvedCodegenKind::ExternalFunction { effects, .. } => effects.is_empty(),
                ResolvedCodegenKind::Intrinsic { .. } => true,
            };
        }

        matches!(head, Atom::DictRef { .. })
    }

    fn reader_variant_head(&mut self, head: &Atom, stack: &[HandlerFrame]) -> Option<Atom> {
        if !stack
            .iter()
            .any(|frame| matches!(frame, HandlerFrame::Reader { .. }))
        {
            return None;
        }

        let Atom::Var { name, .. } = head else {
            return None;
        };
        if name.name.starts_with(STATIC_READER_VARIANT_PREFIX) {
            return None;
        }
        if !self.functions.contains_key(&name.name) {
            return None;
        }

        let variant_name = self.ensure_reader_variant(&name.name, stack)?;
        Some(Atom::Var {
            name: crate::codegen::monadic::ir::MVar {
                name: variant_name,
                id: name.id,
            },
            source: NodeId::fresh(),
        })
    }

    fn ensure_reader_variant(&mut self, name: &str, stack: &[HandlerFrame]) -> Option<String> {
        let stack_key = reader_stack_key(stack);
        let cache_key = (name.to_string(), stack_key.clone());
        if let Some(existing) = self.variant_cache.get(&cache_key) {
            return Some(existing.clone());
        }

        let original = self.functions.get(name)?.clone();
        if original.guard.is_some() {
            return None;
        }

        let variant_name = reader_variant_name(name, &stack_key);
        self.variant_cache.insert(cache_key, variant_name.clone());

        let mut scope = HashSet::new();
        for param in &original.params {
            collect_pat_binders(param, &mut scope);
        }
        let (body, _) = self.optimize_expr(original.body, stack, &scope);

        self.generated_variants.push(MFunBinding {
            id: NodeId::fresh(),
            public: false,
            name: variant_name.clone(),
            name_span: original.name_span,
            params: original.params,
            guard: None,
            body,
            span: original.span,
        });

        Some(variant_name)
    }
}

fn reader_stack_key(stack: &[HandlerFrame]) -> String {
    format!("{:016x}", stable_hash(&format!("{stack:?}")))
}

fn reader_variant_name(name: &str, stack_key: &str) -> String {
    format!(
        "{}__{}__{}",
        STATIC_READER_VARIANT_PREFIX,
        sanitize_ident_part(name),
        stack_key
    )
}

fn stable_hash(value: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn sanitize_ident_part(value: &str) -> String {
    let mut out = String::new();
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() { "_".to_string() } else { out }
}

fn handler_effects(handler: &MHandler) -> Vec<String> {
    match handler {
        MHandler::Static { effects, .. }
        | MHandler::Dynamic { effects, .. }
        | MHandler::Native { effects, .. } => effects.clone(),
        MHandler::Composite { handlers, .. } => handlers.iter().flat_map(handler_effects).collect(),
    }
}

fn is_ignored_reader_param(param: &Pat) -> bool {
    matches!(
        param,
        Pat::Wildcard { .. }
            | Pat::Lit {
                value: Lit::Unit,
                ..
            }
    )
}

fn atom_source(atom: &Atom) -> NodeId {
    match atom {
        Atom::Var { source, .. }
        | Atom::Lit { source, .. }
        | Atom::Ctor { source, .. }
        | Atom::Tuple { source, .. }
        | Atom::AnonRecord { source, .. }
        | Atom::Record { source, .. }
        | Atom::Lambda { source, .. }
        | Atom::DictRef { source, .. }
        | Atom::QualifiedRef { source, .. }
        | Atom::Symbol { source, .. }
        | Atom::BackendAtom { source, .. }
        | Atom::BackendSpawnThunk { source, .. } => *source,
    }
}

fn atom_is_non_yielding(atom: &Atom) -> bool {
    match atom {
        Atom::Lambda { .. } => true,
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            args.iter().all(atom_is_non_yielding)
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().all(|(_, atom)| atom_is_non_yielding(atom))
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_is_non_yielding(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => true,
    }
}

fn expr_free_names(expr: &MExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_expr_free_names(expr, &mut names, &HashSet::new());
    names
}

fn collect_expr_free_names(expr: &MExpr, out: &mut HashSet<String>, scoped: &HashSet<String>) {
    match expr {
        MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
            collect_atom_free_names(atom, out, scoped)
        }
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            for arg in args {
                collect_atom_free_names(arg, out, scoped);
            }
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            collect_expr_free_names(value, out, scoped);
            let mut nested = scoped.clone();
            nested.insert(var.name.clone());
            collect_expr_free_names(body, out, &nested);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_expr_free_names(body, out, scoped);
            collect_expr_free_names(cleanup, out, scoped);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_free_names(scrutinee, out, scoped);
            for arm in arms {
                let mut nested = scoped.clone();
                collect_pat_binders(&arm.pattern, &mut nested);
                if let Some(guard) = &arm.guard {
                    collect_expr_free_names(guard, out, &nested);
                }
                collect_expr_free_names(&arm.body, out, &nested);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_free_names(cond, out, scoped);
            collect_expr_free_names(then_branch, out, scoped);
            collect_expr_free_names(else_branch, out, scoped);
        }
        MExpr::App { head, args, .. } => {
            collect_atom_free_names(head, out, scoped);
            for arg in args {
                collect_atom_free_names(arg, out, scoped);
            }
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_free_names(handler, out, scoped);
            collect_expr_free_names(body, out, scoped);
        }
        MExpr::FieldAccess { record, .. }
        | MExpr::DictMethodAccess { dict: record, .. }
        | MExpr::UnaryMinus { value: record, .. } => collect_atom_free_names(record, out, scoped),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_free_names(record, out, scoped);
            for (_, atom) in fields {
                collect_atom_free_names(atom, out, scoped);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_free_names(left, out, scoped);
            collect_atom_free_names(right, out, scoped);
        }
        MExpr::BitString { segments, .. } => {
            for segment in segments {
                collect_atom_free_names(&segment.value, out, scoped);
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                let mut nested = scoped.clone();
                collect_pat_binders(&arm.pattern, &mut nested);
                collect_expr_free_names(&arm.body, out, &nested);
            }
            if let Some((timeout, body)) = after {
                collect_atom_free_names(timeout, out, scoped);
                collect_expr_free_names(body, out, scoped);
            }
        }
        MExpr::LetFun {
            name, body, rest, ..
        } => {
            let mut nested = scoped.clone();
            nested.insert(name.clone());
            collect_expr_free_names(body, out, &nested);
            collect_expr_free_names(rest, out, &nested);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_free_names(arm, out, scoped);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_free_names(arm, out, scoped);
            }
        }
    }
}

fn collect_atom_free_names(atom: &Atom, out: &mut HashSet<String>, scoped: &HashSet<String>) {
    match atom {
        Atom::Var { name, .. } if !scoped.contains(&name.name) => {
            out.insert(name.name.clone());
        }
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            for arg in args {
                collect_atom_free_names(arg, out, scoped);
            }
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_free_names(atom, out, scoped);
            }
        }
        Atom::Lambda { params, body, .. } => {
            let mut nested = scoped.clone();
            for param in params {
                collect_pat_binders(param, &mut nested);
            }
            collect_expr_free_names(body, out, &nested);
        }
        Atom::BackendSpawnThunk { callback, .. } => {
            collect_atom_free_names(callback, out, scoped);
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

fn collect_handler_free_names(
    handler: &MHandler,
    out: &mut HashSet<String>,
    scoped: &HashSet<String>,
) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_free_names(arm, out, scoped);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_free_names(arm, out, scoped);
            }
        }
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_free_names(handler, out, scoped);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_free_names(op_tuple, out, scoped);
            if let Some(atom) = return_lambda {
                collect_atom_free_names(atom, out, scoped);
            }
        }
        MHandler::Native { .. } => {}
    }
}

fn collect_handler_arm_free_names(
    arm: &MHandlerArm,
    out: &mut HashSet<String>,
    scoped: &HashSet<String>,
) {
    let mut nested = scoped.clone();
    for param in &arm.params {
        collect_pat_binders(param, &mut nested);
    }
    collect_expr_free_names(&arm.body, out, &nested);
    if let Some(cleanup) = &arm.finally_block {
        collect_expr_free_names(cleanup, out, &nested);
    }
}

fn collect_pat_binders(pat: &Pat, out: &mut HashSet<String>) {
    match pat {
        Pat::Var { name, .. } => {
            out.insert(name.clone());
        }
        Pat::Constructor { args, .. }
        | Pat::Tuple { elements: args, .. }
        | Pat::ListPat { elements: args, .. } => {
            for arg in args {
                collect_pat_binders(arg, out);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            if let Some(as_name) = as_name {
                out.insert(as_name.clone());
            }
            for (field, pat) in fields {
                if let Some(pat) = pat {
                    collect_pat_binders(pat, out);
                } else {
                    out.insert(field.clone());
                }
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (field, pat) in fields {
                if let Some(pat) = pat {
                    collect_pat_binders(pat, out);
                } else {
                    out.insert(field.clone());
                }
            }
        }
        Pat::StringPrefix { rest, .. } => collect_pat_binders(rest, out),
        Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                collect_pat_binders(&segment.value, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_binders(head, out);
            collect_pat_binders(tail, out);
        }
        Pat::Or { patterns, .. } => {
            for pattern in patterns {
                collect_pat_binders(pattern, out);
            }
        }
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::monadic::ir::{BindMode, MVal, MVar};
    use crate::typechecker::{RecordInfo, ResolvedEffectOp, ResolvedValue, Type};
    use std::collections::{HashMap, HashSet};

    struct Fixture {
        effect_calls: HashMap<NodeId, ResolvedEffectOp>,
        handler_arms: HashMap<NodeId, ResolvedEffectOp>,
        constructors: HashMap<NodeId, String>,
        fun_effects: HashMap<String, HashSet<String>>,
        let_effect_bindings: HashMap<String, Vec<String>>,
        type_at_node: HashMap<NodeId, Type>,
        records: HashMap<String, RecordInfo>,
        effect_ops: HashMap<String, Vec<String>>,
        handler_effects: HashMap<String, Vec<String>>,
        handler_refs: HashMap<NodeId, ResolvedValue>,
        let_handler_effects: HashMap<NodeId, Vec<String>>,
        resolution: ResolutionMap,
    }

    impl Fixture {
        fn new() -> Self {
            Self {
                effect_calls: HashMap::new(),
                handler_arms: HashMap::new(),
                constructors: HashMap::new(),
                fun_effects: HashMap::new(),
                let_effect_bindings: HashMap::new(),
                type_at_node: HashMap::new(),
                records: HashMap::new(),
                effect_ops: HashMap::new(),
                handler_effects: HashMap::new(),
                handler_refs: HashMap::new(),
                let_handler_effects: HashMap::new(),
                resolution: ResolutionMap::new(),
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
                records: &self.records,
                effect_ops: &self.effect_ops,
                handler_effects: &self.handler_effects,
                handler_refs: &self.handler_refs,
                let_handler_effects: &self.let_handler_effects,
            }
        }
    }

    #[test]
    fn static_reader_handler_rewrites_yield_to_value() {
        let fixture = Fixture::new();
        let op = config_op();
        let value = lit_int("42", 10);
        let program = val_program(MExpr::With {
            handler: static_handler(vec![reader_arm(20, op.clone(), value.clone())], None),
            body: Box::new(yield_expr(op)),
            source: id(30),
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value: out, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(out, MExpr::With { body, .. } if **body == MExpr::Pure(value)));
    }

    #[test]
    fn nested_static_reader_handler_shadows_outer_reader() {
        let fixture = Fixture::new();
        let op = config_op();
        let outer_value = lit_int("1", 10);
        let inner_value = lit_int("2", 11);
        let inner = MExpr::With {
            handler: static_handler(vec![reader_arm(21, op.clone(), inner_value.clone())], None),
            body: Box::new(yield_expr(op.clone())),
            source: id(31),
        };
        let program = val_program(MExpr::With {
            handler: static_handler(vec![reader_arm(20, op, outer_value)], None),
            body: Box::new(inner),
            source: id(30),
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(
            value,
            MExpr::With { body, .. }
                if matches!(&**body, MExpr::With { body, .. } if **body == MExpr::Pure(inner_value))
        ));
    }

    #[test]
    fn dynamic_same_effect_handler_blocks_outer_reader() {
        let fixture = Fixture::new();
        let op = config_op();
        let inner_yield = yield_expr(op.clone());
        let program = val_program(MExpr::With {
            handler: static_handler(vec![reader_arm(20, op.clone(), lit_int("1", 10))], None),
            body: Box::new(MExpr::With {
                handler: MHandler::Dynamic {
                    effects: vec![op.effect.clone()],
                    op_tuple: var("handler_tuple", 40),
                    return_lambda: None,
                    source: id(41),
                },
                body: Box::new(inner_yield.clone()),
                source: id(42),
            }),
            source: id(30),
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(
            value,
            MExpr::With {
                body,
                ..
            } if matches!(&**body, MExpr::With { body, .. } if **body == inner_yield)
        ));
    }

    #[test]
    fn return_clause_disables_reader_specialization() {
        let fixture = Fixture::new();
        let op = config_op();
        let yield_body = yield_expr(op.clone());
        let program = val_program(MExpr::With {
            handler: static_handler(
                vec![reader_arm(20, op.clone(), lit_int("1", 10))],
                Some(reader_arm(21, op, lit_int("2", 11))),
            ),
            body: Box::new(yield_body.clone()),
            source: id(30),
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(value, MExpr::With { body, .. } if **body == yield_body));
    }

    #[test]
    fn nontrivial_param_pattern_disables_reader_specialization() {
        let fixture = Fixture::new();
        let op = config_op();
        let yield_body = yield_expr(op.clone());
        let arm = MHandlerArm {
            id: id(20),
            op,
            params: vec![Pat::Var {
                id: id(21),
                name: "arg".to_string(),
                span: span(),
            }],
            body: Box::new(MExpr::Resume {
                value: lit_int("1", 10),
                source: id(22),
            }),
            finally_block: None,
            span: span(),
        };
        let program = val_program(MExpr::With {
            handler: static_handler(vec![arm], None),
            body: Box::new(yield_body.clone()),
            source: id(30),
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(value, MExpr::With { body, .. } if **body == yield_body));
    }

    #[test]
    fn unrelated_effect_yield_is_left_in_place() {
        let fixture = Fixture::new();
        let config = config_op();
        let other = EffectOpRef {
            effect: "Other".to_string(),
            op: "ask".to_string(),
            op_index: 1,
        };
        let other_yield = yield_expr(other);
        let program = val_program(MExpr::With {
            handler: static_handler(vec![reader_arm(20, config, lit_int("1", 10))], None),
            body: Box::new(other_yield.clone()),
            source: id(30),
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(value, MExpr::With { body, .. } if **body == other_yield));
    }

    #[test]
    fn non_yielding_bind_promotes_to_let() {
        let fixture = Fixture::new();
        let program = val_program(MExpr::Bind {
            var: mv("x", 70),
            value: Box::new(MExpr::Pure(lit_int("1", 71))),
            body: Box::new(MExpr::Pure(var("x", 70))),
            mode: BindMode::Sequence,
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(value, MExpr::Let { var: bound_var, value, body }
            if bound_var.name == "x"
                && **value == MExpr::Pure(lit_int("1", 71))
                && **body == MExpr::Pure(var("x", 70))));
    }

    #[test]
    fn yielding_bind_stays_bind() {
        let fixture = Fixture::new();
        let op = config_op();
        let program = val_program(MExpr::Bind {
            var: mv("x", 70),
            value: Box::new(yield_expr(op)),
            body: Box::new(MExpr::Pure(var("x", 70))),
            mode: BindMode::Sequence,
        });

        let out = run(program, &fixture.info(), &fixture.resolution);

        let [MDecl::Val(MVal { value, .. })] = out.as_slice() else {
            panic!("expected val program");
        };
        assert!(matches!(value, MExpr::Bind { var, .. } if var.name == "x"));
    }

    fn val_program(value: MExpr) -> MProgram {
        vec![MDecl::Val(MVal {
            id: id(1),
            public: false,
            name: "main".to_string(),
            value,
            span: span(),
        })]
    }

    fn static_handler(arms: Vec<MHandlerArm>, return_clause: Option<MHandlerArm>) -> MHandler {
        MHandler::Static {
            effects: vec!["Config".to_string()],
            arms,
            return_clause,
            source: id(99),
        }
    }

    fn reader_arm(id_num: u32, op: EffectOpRef, value: Atom) -> MHandlerArm {
        MHandlerArm {
            id: id(id_num),
            op,
            params: vec![Pat::Lit {
                id: id(id_num + 100),
                value: Lit::Unit,
                span: span(),
            }],
            body: Box::new(MExpr::Resume {
                value,
                source: id(id_num + 200),
            }),
            finally_block: None,
            span: span(),
        }
    }

    fn yield_expr(op: EffectOpRef) -> MExpr {
        MExpr::Yield {
            op,
            args: vec![Atom::Lit {
                value: Lit::Unit,
                source: id(60),
            }],
            source: id(61),
        }
    }

    fn config_op() -> EffectOpRef {
        EffectOpRef {
            effect: "Config".to_string(),
            op: "get".to_string(),
            op_index: 1,
        }
    }

    fn lit_int(raw: &str, node: u32) -> Atom {
        Atom::Lit {
            value: Lit::Int(raw.to_string(), raw.parse().unwrap()),
            source: id(node),
        }
    }

    fn var(name: &str, node: u32) -> Atom {
        Atom::Var {
            name: MVar {
                name: name.to_string(),
                id: node,
            },
            source: id(node),
        }
    }

    fn mv(name: &str, node: u32) -> MVar {
        MVar {
            name: name.to_string(),
            id: node,
        }
    }

    fn id(n: u32) -> NodeId {
        NodeId(n)
    }

    fn span() -> crate::token::Span {
        crate::token::Span { start: 0, end: 0 }
    }
}
