// effect_opt/ — monadic IR optimization stage.
//
// Currently implements steps 9-11:
//   - bind collapse — Bind(Pure(a), x, B) → B[x := a]
//   - Bind→Let promotion — pure binders become direct lets
//   - dead pure-let cleanup — remove unused pure lets
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
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use crate::typechecker::ModuleCodegenInfo;
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
    _e: &EffectInfo,
    opts: RunOptions,
) -> MProgram {
    run_with_options_and_context(m, h, _e, opts, OptimizerContext::default())
}

pub fn run_with_context(
    m: MProgram,
    h: &HandlerAnalysis,
    e: &EffectInfo,
    context: OptimizerContext,
) -> MProgram {
    run_with_options_and_context(m, h, e, RunOptions::default(), context)
}

pub fn run_with_options_and_context(
    m: MProgram,
    h: &HandlerAnalysis,
    _e: &EffectInfo,
    opts: RunOptions,
    context: OptimizerContext,
) -> MProgram {
    if opts.skip {
        return m;
    }

    let mut optimizer = Optimizer::new(opts, h, context);
    optimizer.optimize_program(m)
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RunOptions {
    /// Emit no-op even after rewrites land. Useful for benchmarking and
    /// bisecting miscompiles between the translator and the optimizer.
    pub skip: bool,
}

#[derive(Debug, Clone, Default)]
pub struct OptimizerContext {
    pub resolution: ResolutionMap,
    pub imported_function_variants: HashMap<String, ImportedFunctionVariantCandidate>,
    pub imported_handler_factories: HashMap<String, ImportedHandlerFactoryCandidate>,
    pub imported_dict_constructors: HashMap<String, MDictConstructor>,
    pub imported_private_helpers: HashMap<String, ImportedPrivateHelperCandidate>,
}

#[derive(Debug, Clone)]
pub struct ImportedFunctionVariantCandidate {
    pub source_module: String,
    pub binding: MFunBinding,
    pub public_names: HashSet<String>,
}

#[derive(Debug, Clone)]
pub struct ImportedHandlerFactoryCandidate {
    pub source_module: String,
    pub params: Vec<Pat>,
    pub body: MExpr,
}

#[derive(Debug, Clone)]
pub struct ImportedPrivateHelperCandidate {
    pub source_module: String,
    pub binding: MFunBinding,
}

struct Optimizer<'info> {
    opts: RunOptions,
    context: OptimizerContext,
    handler_analysis: &'info HandlerAnalysis,
    handler_stack: Vec<HandlerFrame>,
    handler_value_bindings: Vec<(String, Option<HandlerValueCandidate>)>,
    dict_value_bindings: Vec<(String, Option<DictValueCandidate>)>,
    dict_method_bindings: Vec<(String, Option<InlineCandidate>)>,
    pure_atom_bindings: Vec<(String, Option<Atom>)>,
    inline_candidates: HashMap<String, InlineCandidate>,
    handler_factory_candidates: HashMap<String, InlineCandidate>,
    dict_constructors: HashMap<String, MDictConstructor>,
    variant_candidates: HashMap<String, VariantCandidate>,
    generated_variant_names: HashSet<String>,
    in_progress_private_helpers: HashSet<String>,
    pending_variants: Vec<MDecl>,
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

impl HandlerFrame {
    fn effects(&self) -> &[String] {
        match self {
            HandlerFrame::Static { effects, .. }
            | HandlerFrame::Native { effects, .. }
            | HandlerFrame::Blocking { effects } => effects,
        }
    }

    fn handles_effect(&self, effect: &str) -> bool {
        self.effects()
            .iter()
            .any(|frame_effect| effect_names_match(frame_effect, effect))
    }
}

#[derive(Debug, Clone)]
struct InlineCandidate {
    params: Vec<Pat>,
    body: MExpr,
}

#[derive(Debug, Clone)]
struct HandlerValueCandidate {
    effects: Vec<String>,
    arms: Vec<MHandlerArm>,
    return_clause: Option<Box<MHandlerArm>>,
    source: crate::ast::NodeId,
}

#[derive(Debug, Clone)]
struct HandlerFactoryPrefixBinding {
    var: MVar,
    value: MExpr,
    mode: Option<crate::codegen::monadic::ir::BindMode>,
}

#[derive(Debug, Clone)]
struct VariantCandidate {
    binding: MFunBinding,
}

#[derive(Debug, Clone)]
struct DictValueCandidate {
    atom: Atom,
    methods: Vec<Atom>,
    key: String,
}

#[derive(Debug, Clone)]
struct DictParamReplacement {
    target: MVar,
    replacement: Atom,
    key: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct EffectSummary {
    erasable_yields: usize,
    residual_yields: usize,
    summarized_calls: usize,
    blockers: usize,
}

impl EffectSummary {
    fn add_assign(&mut self, other: Self) {
        self.erasable_yields += other.erasable_yields;
        self.residual_yields += other.residual_yields;
        self.summarized_calls += other.summarized_calls;
        self.blockers += other.blockers;
    }

    fn has_specialization_opportunity(&self) -> bool {
        self.erasable_yields > 0 || self.summarized_calls > 0
    }
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

impl<'info> Optimizer<'info> {
    fn new(
        opts: RunOptions,
        handler_analysis: &'info HandlerAnalysis,
        context: OptimizerContext,
    ) -> Self {
        Self {
            opts,
            context,
            handler_analysis,
            handler_stack: Vec::new(),
            handler_value_bindings: Vec::new(),
            dict_value_bindings: Vec::new(),
            dict_method_bindings: Vec::new(),
            pure_atom_bindings: Vec::new(),
            inline_candidates: HashMap::new(),
            handler_factory_candidates: HashMap::new(),
            dict_constructors: HashMap::new(),
            variant_candidates: HashMap::new(),
            generated_variant_names: HashSet::new(),
            in_progress_private_helpers: HashSet::new(),
            pending_variants: Vec::new(),
            inline_blocked_names: Vec::new(),
        }
    }

    fn optimize_program(&mut self, mut program: MProgram) -> MProgram {
        let mut changed = true;
        while changed {
            self.inline_candidates = collect_inline_candidates(&program);
            self.handler_factory_candidates = collect_handler_factory_candidates(&program);
            self.dict_constructors = collect_dict_constructors(&program);
            self.variant_candidates = collect_variant_candidates(&program);
            self.pending_variants.clear();
            changed = false;
            program = program
                .into_iter()
                .map(|decl| {
                    let (decl, ch) = self.optimize_decl(decl);
                    changed |= ch == Change::Changed;
                    decl
                })
                .collect();
            if !self.pending_variants.is_empty() {
                changed = true;
                program.append(&mut self.pending_variants);
            }
            let before_cleanup_len = program.len();
            program = remove_dead_variant_sources(program);
            if program.len() != before_cleanup_len {
                changed = true;
            }
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
        let (expr, private_helper_change) = self.try_imported_private_helper_call(expr);
        let (expr, variant_change) = self.try_native_function_variant_call(expr);
        let (expr, inline_change) = self.try_inline_helper_call(expr);
        let (expr, static_variant_change) = self.try_static_function_variant_call(expr);
        let (expr, native_change) = self.try_native_direct_call(expr);
        let (expr, finally_direct_change) = self.try_finally_direct_call(expr);
        let (expr, direct_change) = self.try_direct_call(expr);
        let (expr, handler_factory_change) = self.try_inline_let_bound_handler_factory(expr);
        let (expr, handler_value_change) = self.try_inline_let_bound_handler_value(expr);
        let (expr, collapse_change) = self.try_bind_collapse(expr);
        let (expr, let_collapse_change) = self.try_let_pure_collapse(expr);
        let (expr, let_change) = self.try_bind_to_let(expr);
        let (expr, dead_let_change) = self.try_dead_pure_let(expr);
        let (expr, dead_with_change) = self.try_dead_pure_static_with(expr);
        let mut change = child_change;
        change.mark_if(private_helper_change);
        change.mark_if(variant_change);
        change.mark_if(inline_change);
        change.mark_if(static_variant_change);
        change.mark_if(native_change);
        change.mark_if(finally_direct_change);
        change.mark_if(direct_change);
        change.mark_if(handler_factory_change);
        change.mark_if(handler_value_change);
        change.mark_if(collapse_change);
        change.mark_if(let_collapse_change);
        change.mark_if(let_change);
        change.mark_if(dead_let_change);
        change.mark_if(dead_with_change);
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
                let (body, body_change) = self.optimize_body_after_binding(&var, &value, *body);
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
                let (body, body_change) = self.optimize_body_after_binding(&var, &value, *body);
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
                let (handler, dynamic_change) = self.specialize_dynamic_handler_binding(handler);
                let frame = handler_frame(&handler);
                let (body, body_change) = if let Some(frame) = frame {
                    self.optimize_expr_with_frame(*body, frame)
                } else {
                    self.optimize_expr(*body)
                };
                let mut change = handler_change;
                change.mark_if(dynamic_change);
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

        if expr_is_pure(&value) {
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

    fn try_let_pure_collapse(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.bind_collapse() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Let { var, value, body } = expr else {
            return (expr, Change::Unchanged);
        };

        let MExpr::Pure(atom) = *value else {
            return (MExpr::Let { var, value, body }, Change::Unchanged);
        };

        let free_names = free_atom_names(&atom);
        let substituted = subst_expr(*body, &var, &atom, &free_names);
        if substituted.blocked {
            (
                MExpr::Let {
                    var,
                    value: Box::new(MExpr::Pure(atom)),
                    body: Box::new(substituted.value),
                },
                Change::Unchanged,
            )
        } else {
            (substituted.value, Change::Changed)
        }
    }

    fn try_dead_pure_let(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.dead_pure_let() {
            return (expr, Change::Unchanged);
        }

        let (var, value, body, mode) = match expr {
            MExpr::Let { var, value, body } => (var, value, body, None),
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => (var, value, body, Some(mode)),
            other => return (other, Change::Unchanged),
        };

        if (expr_is_pure(&value) || matches!(&*value, MExpr::HandlerValue { .. }))
            && !expr_contains_target(&body, &var)
        {
            (*body, Change::Changed)
        } else {
            (rebuild_binding(var, value, body, mode), Change::Unchanged)
        }
    }

    fn try_dead_pure_static_with(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.dead_pure_with() {
            return (expr, Change::Unchanged);
        }

        let MExpr::With {
            handler,
            body,
            source,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        match &handler {
            MHandler::Static { return_clause, .. }
                if return_clause.is_none() && expr_is_handler_independent_value(&body) =>
            {
                (*body, Change::Changed)
            }
            _ => (
                MExpr::With {
                    handler,
                    body,
                    source,
                },
                Change::Unchanged,
            ),
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

    fn optimize_body_after_binding(
        &mut self,
        var: &MVar,
        value: &MExpr,
        body: MExpr,
    ) -> (MExpr, Change) {
        if let Some(candidate) = handler_value_candidate(value) {
            self.handler_value_bindings
                .push((var.name.clone(), Some(candidate)));
        } else {
            self.handler_value_bindings.push((var.name.clone(), None));
        }
        if let Some(candidate) = self.dict_value_candidate(value) {
            self.dict_value_bindings
                .push((var.name.clone(), Some(candidate)));
        } else {
            self.dict_value_bindings.push((var.name.clone(), None));
        }
        if let Some(candidate) = self.dict_method_candidate(value) {
            self.dict_method_bindings
                .push((var.name.clone(), Some(candidate)));
        } else {
            self.dict_method_bindings.push((var.name.clone(), None));
        }
        if let MExpr::Pure(atom) = value {
            self.pure_atom_bindings
                .push((var.name.clone(), closed_dict_constructor_arg(atom)));
        } else {
            self.pure_atom_bindings.push((var.name.clone(), None));
        }
        let (body, change) = self.optimize_expr_with_blocked_names(vec![var.name.clone()], body);
        self.pure_atom_bindings.pop();
        self.dict_method_bindings.pop();
        self.dict_value_bindings.pop();
        self.handler_value_bindings.pop();
        (body, change)
    }

    fn dict_value_candidate(&self, value: &MExpr) -> Option<DictValueCandidate> {
        let MExpr::App { head, args, .. } = value else {
            return None;
        };
        let constructor = self.dict_constructor_for_head(head)?;
        if constructor.dict_params.len() != args.len() {
            return None;
        }

        let mut param_replacements = Vec::with_capacity(args.len());
        let mut arg_keys = Vec::with_capacity(args.len());
        for (param, arg) in constructor.dict_params.iter().zip(args) {
            let (replacement, key) = match arg {
                Atom::Var { name: arg_var, .. } => self
                    .lookup_dict_value(&arg_var.name)
                    .map(|arg_dict| (arg_dict.atom, arg_dict.key))
                    .or_else(|| {
                        self.lookup_pure_atom(&arg_var.name).map(|arg| {
                            let key = atom_key(&arg);
                            (arg, key)
                        })
                    })
                    .or_else(|| {
                        closed_dict_constructor_arg(arg).map(|arg| {
                            let key = atom_key(&arg);
                            (arg, key)
                        })
                    })?,
                _ => {
                    let arg = closed_dict_constructor_arg(arg)?;
                    let key = atom_key(&arg);
                    (arg, key)
                }
            };
            param_replacements.push((
                MVar {
                    name: param.clone(),
                    id: 0,
                },
                replacement,
            ));
            arg_keys.push(key);
        }

        let mut methods = Vec::with_capacity(constructor.methods.len());
        for method in &constructor.methods {
            let MExpr::Pure(atom @ Atom::Lambda { .. }) = method else {
                return None;
            };
            let mut method = atom.clone();
            for (target, replacement) in &param_replacements {
                let free_names = free_atom_names(replacement);
                let substituted = subst_atom(method, target, replacement, &free_names);
                if substituted.blocked {
                    return None;
                }
                method = substituted.value;
            }
            methods.push(method);
        }

        let key = if arg_keys.is_empty() {
            constructor.name.clone()
        } else {
            format!("{}({})", constructor.name, arg_keys.join(","))
        };
        Some(DictValueCandidate {
            atom: Atom::Tuple {
                elements: methods.clone(),
                source: constructor.id,
            },
            methods,
            key,
        })
    }

    fn dict_constructor_for_head(&self, head: &Atom) -> Option<&MDictConstructor> {
        match head {
            Atom::DictRef { name, .. } => self
                .dict_constructors
                .get(name)
                .or_else(|| self.context.imported_dict_constructors.get(name)),
            Atom::QualifiedRef { name, source, .. } => {
                let canonical = self
                    .context
                    .resolution
                    .get(source)
                    .map(|resolved| resolved.canonical_name.as_str());
                canonical
                    .and_then(|name| self.context.imported_dict_constructors.get(name))
                    .or_else(|| self.context.imported_dict_constructors.get(name))
            }
            _ => None,
        }
    }

    fn dict_method_candidate(&self, value: &MExpr) -> Option<InlineCandidate> {
        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = value
        else {
            return None;
        };
        let method = self.dict_method_atom(dict, *method_index)?;
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if !dict_method_params_are_supported(&params) {
            return None;
        }
        Some(InlineCandidate {
            params: params.clone(),
            body: body.as_ref().clone(),
        })
    }

    fn dict_method_atom(&self, dict: &Atom, method_index: usize) -> Option<Atom> {
        match dict {
            Atom::Var { name, .. } => self
                .lookup_dict_value(&name.name)
                .and_then(|dict| dict.methods.get(method_index).cloned()),
            Atom::Tuple { elements, .. } => elements.get(method_index).cloned(),
            _ => None,
        }
    }

    fn lookup_dict_value(&self, name: &str) -> Option<DictValueCandidate> {
        self.dict_value_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == name)?
            .1
            .clone()
    }

    fn lookup_dict_method(&self, name: &str) -> Option<InlineCandidate> {
        self.dict_method_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == name)?
            .1
            .clone()
    }

    fn lookup_pure_atom(&self, name: &str) -> Option<Atom> {
        self.pure_atom_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == name)?
            .1
            .clone()
    }

    fn dict_param_replacements(&self, params: &[Pat], args: &[Atom]) -> Vec<DictParamReplacement> {
        params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let Pat::Var { name, id, .. } = param else {
                    return None;
                };
                let Atom::Var { name: arg_var, .. } = arg else {
                    return None;
                };
                let dict = self.lookup_dict_value(&arg_var.name)?;
                Some(DictParamReplacement {
                    target: MVar {
                        name: name.clone(),
                        id: id.0,
                    },
                    replacement: dict.atom,
                    key: dict.key,
                })
            })
            .collect()
    }

    fn specialize_dynamic_handler_binding(&self, handler: MHandler) -> (MHandler, Change) {
        let MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } = handler
        else {
            return (handler, Change::Unchanged);
        };

        let Atom::Var { name, .. } = &op_tuple else {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        };

        let Some((_, maybe_candidate)) = self
            .handler_value_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == &name.name)
        else {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        };
        let Some(candidate) = maybe_candidate.as_ref() else {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        };

        if return_lambda.is_some() || !handler_effect_sets_match(&candidate.effects, &effects) {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        }

        (
            MHandler::Static {
                effects: candidate.effects.clone(),
                arms: candidate.arms.clone(),
                return_clause: candidate.return_clause.as_deref().cloned(),
                source: candidate.source,
            },
            Change::Changed,
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
            Atom::BackendSpawnThunk { callback, source } => {
                let (callback, change) = self.optimize_spawn_callback_atom(*callback);
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
            | Atom::BackendAtom { .. } => (atom, Change::Unchanged),
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

    fn try_native_function_variant_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.native_function_variants() || !self.native_variant_stack_eligible() {
            return (expr, Change::Unchanged);
        }

        let (expr, change) = self.try_function_variant_call(expr, native_variant_name, false);
        if change == Change::Changed {
            return (expr, change);
        }

        self.try_imported_function_variant_call(expr, variant_name_for_imported, false)
    }

    fn try_static_function_variant_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.static_function_variants() || !self.static_variant_stack_eligible() {
            return (expr, Change::Unchanged);
        }

        let (expr, change) = self.try_function_variant_call(expr, static_variant_name, true);
        if change == Change::Changed {
            return (expr, change);
        }

        self.try_imported_function_variant_call(expr, variant_name_for_imported_static, true)
    }

    fn try_function_variant_call(
        &mut self,
        expr: MExpr,
        variant_name_for_stack: fn(&str, &[HandlerFrame]) -> String,
        require_no_residual_yields: bool,
    ) -> (MExpr, Change) {
        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Atom::Var {
            name,
            source: _head_source,
        } = &head
        else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if is_generated_variant_name(&name.name)
            || self.inline_blocked_names.iter().any(|n| n == &name.name)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.variant_candidates.get(&name.name).cloned() else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if args.len() != candidate.binding.params.len() {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }
        let dict_replacements = self.dict_param_replacements(&candidate.binding.params, &args);
        if !self.expr_has_specialization_opportunity(&candidate.binding.body) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let variant_name = variant_name_with_dict_key(
            variant_name_for_stack(&candidate.binding.name, &self.handler_stack),
            &dict_replacements,
        );
        if variant_name == name.name {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(variant_body) = self.optimized_variant_body(
            &candidate.binding,
            &name.name,
            &variant_name,
            Vec::<String>::new(),
            &dict_replacements,
        ) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if require_no_residual_yields && expr_yield_count(&variant_body) != 0 {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let (variant_params, args) = prune_unused_dict_variant_args(
            &candidate.binding.params,
            args,
            &variant_body,
            &dict_replacements,
        );
        self.push_function_variant(
            &variant_name,
            variant_body,
            candidate.binding.clone(),
            variant_params,
        );

        (
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: variant_name,
                        id: name.id,
                    },
                    // Generated variant names are not in the source
                    // resolution map. Reusing the user's original reference
                    // NodeId makes the lowerer resolve this call back to the
                    // source function, so attach the function declaration id
                    // instead.
                    source: candidate.binding.id,
                },
                args,
                source,
            },
            Change::Changed,
        )
    }

    fn try_imported_function_variant_call(
        &mut self,
        expr: MExpr,
        variant_name_for_imported: fn(&str, &str, &[HandlerFrame]) -> String,
        require_no_residual_yields: bool,
    ) -> (MExpr, Change) {
        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some((head_name, head_id, head_source)) = imported_variant_head_info(&head) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if is_generated_variant_name(&head_name)
            || self.inline_blocked_names.iter().any(|n| n == &head_name)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(resolved) = self.context.resolution.get(&head_source) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.lookup_imported_function_variant(resolved) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if args.len() != candidate.binding.params.len() {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }
        let dict_replacements = self.dict_param_replacements(&candidate.binding.params, &args);
        if !require_no_residual_yields
            && !self.expr_has_specialization_opportunity(&candidate.binding.body)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let variant_name = variant_name_with_dict_key(
            variant_name_for_imported(
                &candidate.source_module,
                &candidate.binding.name,
                &self.handler_stack,
            ),
            &dict_replacements,
        );
        let Some(variant_body) = self.optimized_variant_body(
            &candidate.binding,
            &candidate.binding.name,
            &variant_name,
            candidate.public_names.iter().cloned(),
            &dict_replacements,
        ) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if require_no_residual_yields && expr_yield_count(&variant_body) != 0 {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let (variant_params, args) = prune_unused_dict_variant_args(
            &candidate.binding.params,
            args,
            &variant_body,
            &dict_replacements,
        );
        self.push_function_variant(
            &variant_name,
            variant_body,
            candidate.binding.clone(),
            variant_params,
        );

        (
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: variant_name,
                        id: head_id,
                    },
                    source: candidate.binding.id,
                },
                args,
                source,
            },
            Change::Changed,
        )
    }

    fn try_imported_private_helper_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some((head_name, head_id, head_source)) = imported_variant_head_info(&head) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if is_generated_variant_name(&head_name)
            || self.inline_blocked_names.iter().any(|n| n == &head_name)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(resolved) = self.context.resolution.get(&head_source) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.lookup_imported_private_helper(resolved) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if args.len() != candidate.binding.params.len() {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let helper_name = imported_private_helper_variant_name(
            &candidate.source_module,
            &candidate.binding.name,
            &self.handler_stack,
        );
        if !self.generated_variant_names.contains(&helper_name)
            && !self.in_progress_private_helpers.contains(&helper_name)
        {
            self.in_progress_private_helpers.insert(helper_name.clone());
            let body =
                self.optimized_imported_private_helper_body(&candidate.binding, &helper_name);
            self.in_progress_private_helpers.remove(&helper_name);
            self.push_function_variant(
                &helper_name,
                body,
                candidate.binding.clone(),
                candidate.binding.params.clone(),
            );
        }

        (
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: helper_name,
                        id: head_id,
                    },
                    source: candidate.binding.id,
                },
                args,
                source,
            },
            Change::Changed,
        )
    }

    fn optimized_variant_body(
        &mut self,
        binding: &MFunBinding,
        old_name: &str,
        variant_name: &str,
        extra_blocked_names: impl IntoIterator<Item = String>,
        param_replacements: &[DictParamReplacement],
    ) -> Option<MExpr> {
        let mut variant_body =
            rewrite_direct_calls_to_name(binding.body.clone(), old_name, variant_name, binding.id);
        for replacement in param_replacements {
            let free_names = free_atom_names(&replacement.replacement);
            let substituted = subst_expr(
                variant_body,
                &replacement.target,
                &replacement.replacement,
                &free_names,
            );
            if substituted.blocked {
                return None;
            }
            variant_body = substituted.value;
        }

        let old_blocked_len = self.inline_blocked_names.len();
        self.inline_blocked_names
            .extend(bound_names_in_pats(&binding.params));
        self.inline_blocked_names.extend(extra_blocked_names);
        let mut optimized_body = variant_body;
        let mut body_change = Change::Unchanged;
        loop {
            let (next_body, change) = self.optimize_expr(optimized_body);
            if change == Change::Unchanged {
                optimized_body = next_body;
                break;
            }
            body_change = Change::Changed;
            optimized_body = next_body;
        }
        self.inline_blocked_names.truncate(old_blocked_len);

        if body_change == Change::Unchanged {
            None
        } else {
            Some(optimized_body)
        }
    }

    fn optimized_imported_private_helper_body(
        &mut self,
        binding: &MFunBinding,
        helper_name: &str,
    ) -> MExpr {
        let old_blocked_len = self.inline_blocked_names.len();
        self.inline_blocked_names
            .extend(bound_names_in_pats(&binding.params));
        let mut optimized_body = rewrite_direct_calls_to_name(
            binding.body.clone(),
            &binding.name,
            helper_name,
            binding.id,
        );
        loop {
            let (next_body, change) = self.optimize_expr(optimized_body);
            optimized_body = next_body;
            if change == Change::Unchanged {
                break;
            }
        }
        self.inline_blocked_names.truncate(old_blocked_len);
        optimized_body
    }

    fn push_function_variant(
        &mut self,
        variant_name: &str,
        variant_body: MExpr,
        source_binding: MFunBinding,
        params: Vec<Pat>,
    ) {
        if self.generated_variant_names.contains(variant_name) {
            return;
        }
        self.generated_variant_names
            .insert(variant_name.to_string());
        self.pending_variants.push(MDecl::FunBinding(MFunBinding {
            name: variant_name.to_string(),
            public: false,
            params,
            body: variant_body,
            ..source_binding
        }));
    }

    fn lookup_imported_function_variant(
        &self,
        resolved: &crate::codegen::resolve::ResolvedSymbol,
    ) -> Option<ImportedFunctionVariantCandidate> {
        if let Some(candidate) = self
            .context
            .imported_function_variants
            .get(&resolved.canonical_name)
        {
            return Some(candidate.clone());
        }

        let mut matching = self
            .context
            .imported_function_variants
            .values()
            .filter(|candidate| {
                candidate.binding.name == resolved.name
                    && resolved
                        .source_module
                        .as_deref()
                        .is_none_or(|module| module == candidate.source_module)
            });
        let candidate = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        Some(candidate.clone())
    }

    fn lookup_imported_handler_factory(
        &self,
        head: &Atom,
    ) -> Option<ImportedHandlerFactoryCandidate> {
        let (head_name, _, head_source) = imported_variant_head_info(head)?;
        if self.inline_blocked_names.iter().any(|n| n == &head_name) {
            return None;
        }
        let resolved = self.context.resolution.get(&head_source)?;
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return None;
        }
        if let Some(candidate) = self
            .context
            .imported_handler_factories
            .get(&resolved.canonical_name)
        {
            return Some(candidate.clone());
        }

        let mut matching = self
            .context
            .imported_handler_factories
            .values()
            .filter(|candidate| {
                head_name == resolved.name
                    && resolved
                        .source_module
                        .as_deref()
                        .is_none_or(|module| module == candidate.source_module)
            });
        let candidate = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        Some(candidate.clone())
    }

    fn lookup_imported_private_helper(
        &self,
        resolved: &crate::codegen::resolve::ResolvedSymbol,
    ) -> Option<ImportedPrivateHelperCandidate> {
        if let Some(candidate) = self
            .context
            .imported_private_helpers
            .get(&resolved.canonical_name)
        {
            return Some(candidate.clone());
        }

        let mut matching = self
            .context
            .imported_private_helpers
            .values()
            .filter(|candidate| {
                candidate.binding.name == resolved.name
                    && resolved
                        .source_module
                        .as_deref()
                        .is_none_or(|module| module == candidate.source_module)
            });
        let candidate = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        Some(candidate.clone())
    }

    fn native_variant_stack_eligible(&self) -> bool {
        let mut has_native = false;
        for frame in &self.handler_stack {
            match frame {
                HandlerFrame::Native { .. } => has_native = true,
                HandlerFrame::Static { .. } => return false,
                HandlerFrame::Blocking { .. } => {}
            }
        }
        has_native
    }

    fn static_variant_stack_eligible(&self) -> bool {
        let mut has_static = false;
        for frame in &self.handler_stack {
            match frame {
                HandlerFrame::Static { .. } => has_static = true,
                HandlerFrame::Native { .. } => return false,
                HandlerFrame::Blocking { .. } => {}
            }
        }
        has_static
    }

    fn optimize_spawn_callback_atom(&mut self, atom: Atom) -> (Atom, Change) {
        match atom {
            Atom::Lambda {
                params,
                body,
                source,
            } => {
                let blocked_names = bound_names_in_pats(&params);
                let (body, change) = self.optimize_expr_with_blocked_names(blocked_names, *body);
                (
                    Atom::Lambda {
                        params,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            other => self.optimize_atom(other),
        }
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
        if let Some(candidate) = self.lookup_dict_method(&name.name) {
            let Some(inlined) = inline_helper_candidate(&candidate, &args) else {
                return (MExpr::App { head, args, source }, Change::Unchanged);
            };
            if expr_node_count(&inlined) > FUNCTION_VARIANT_BODY_BUDGET
                || (!self.expr_has_specialization_opportunity(&inlined) && !expr_is_pure(&inlined))
            {
                return (MExpr::App { head, args, source }, Change::Unchanged);
            }
            return (inlined, Change::Changed);
        }

        if self.inline_blocked_names.iter().any(|n| n == &name.name) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.inline_candidates.get(&name.name) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        let Some(inlined) = inline_helper_candidate(candidate, &args) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !self.expr_has_specialization_opportunity(&inlined) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        (inlined, Change::Changed)
    }

    fn expr_has_specialization_opportunity(&self, expr: &MExpr) -> bool {
        self.effect_summary(expr).has_specialization_opportunity()
            || expr_contains_dict_method_access(expr)
    }

    fn effect_summary(&self, expr: &MExpr) -> EffectSummary {
        let mut call_stack = HashSet::new();
        self.effect_summary_expr(expr, &mut call_stack, &self.handler_stack)
    }

    fn effect_summary_expr(
        &self,
        expr: &MExpr,
        call_stack: &mut HashSet<String>,
        handler_stack: &[HandlerFrame],
    ) -> EffectSummary {
        match expr {
            MExpr::Yield { op, args, .. } => {
                let mut summary = EffectSummary::default();
                if self.yield_is_erasable_under_stack(op, args, handler_stack) {
                    summary.erasable_yields += 1;
                } else {
                    summary.residual_yields += 1;
                }
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                summary
            }
            MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
                Self::effect_summary_atom(atom)
            }
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                let mut summary = self.effect_summary_expr(value, call_stack, handler_stack);
                summary.add_assign(self.effect_summary_expr(body, call_stack, handler_stack));
                summary
            }
            MExpr::Ensure { body, cleanup } => {
                let mut summary = self.effect_summary_expr(body, call_stack, handler_stack);
                summary.add_assign(self.effect_summary_expr(cleanup, call_stack, handler_stack));
                summary
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                let mut summary = Self::effect_summary_atom(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        summary.add_assign(self.effect_summary_expr(
                            guard,
                            call_stack,
                            handler_stack,
                        ));
                    }
                    summary.add_assign(self.effect_summary_expr(
                        &arm.body,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let mut summary = Self::effect_summary_atom(cond);
                summary.add_assign(self.effect_summary_expr(
                    then_branch,
                    call_stack,
                    handler_stack,
                ));
                summary.add_assign(self.effect_summary_expr(
                    else_branch,
                    call_stack,
                    handler_stack,
                ));
                summary
            }
            MExpr::App { head, args, .. } => {
                let mut summary = Self::effect_summary_atom(head);
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                if let Some((key, body)) = self.summary_callee_body(head, args)
                    && call_stack.insert(key.clone())
                {
                    let callee_summary = self.effect_summary_expr(&body, call_stack, handler_stack);
                    if callee_summary.has_specialization_opportunity() {
                        summary.summarized_calls += 1;
                    }
                    summary.add_assign(callee_summary);
                    call_stack.remove(&key);
                }
                summary
            }
            MExpr::With { handler, body, .. } => {
                let mut summary = self.effect_summary_handler(handler, call_stack, handler_stack);
                if let Some(frame) = handler_frame(handler) {
                    let mut nested_stack = handler_stack.to_vec();
                    nested_stack.push(frame);
                    summary.add_assign(self.effect_summary_expr(body, call_stack, &nested_stack));
                } else {
                    summary.add_assign(self.effect_summary_expr(body, call_stack, handler_stack));
                }
                summary
            }
            MExpr::FieldAccess { record, .. } | MExpr::UnaryMinus { value: record, .. } => {
                Self::effect_summary_atom(record)
            }
            MExpr::DictMethodAccess { dict, .. } => Self::effect_summary_atom(dict),
            MExpr::RecordUpdate { record, fields, .. } => {
                let mut summary = Self::effect_summary_atom(record);
                for (_, atom) in fields {
                    summary.add_assign(Self::effect_summary_atom(atom));
                }
                summary
            }
            MExpr::ForeignCall { args, .. } => {
                let mut summary = EffectSummary::default();
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                summary
            }
            MExpr::BinOp { left, right, .. } => {
                let mut summary = Self::effect_summary_atom(left);
                summary.add_assign(Self::effect_summary_atom(right));
                summary
            }
            MExpr::BitString { segments, .. } => {
                let mut summary = EffectSummary::default();
                for segment in segments {
                    summary.add_assign(Self::effect_summary_atom(&segment.value));
                    if let Some(size) = &segment.size {
                        summary.add_assign(Self::effect_summary_atom(size));
                    }
                }
                summary
            }
            MExpr::Receive { arms, after, .. } => {
                let mut summary = EffectSummary::default();
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        summary.add_assign(self.effect_summary_expr(
                            guard,
                            call_stack,
                            handler_stack,
                        ));
                    }
                    summary.add_assign(self.effect_summary_expr(
                        &arm.body,
                        call_stack,
                        handler_stack,
                    ));
                }
                if let Some((timeout, body)) = after {
                    summary.add_assign(Self::effect_summary_atom(timeout));
                    summary.add_assign(self.effect_summary_expr(body, call_stack, handler_stack));
                }
                summary
            }
            MExpr::LetFun { body, rest, .. } => {
                let mut summary = self.effect_summary_expr(body, call_stack, handler_stack);
                summary.add_assign(self.effect_summary_expr(rest, call_stack, handler_stack));
                summary
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                let mut summary = EffectSummary::default();
                for arm in arms {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                if let Some(arm) = return_clause {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
        }
    }

    fn effect_summary_atom(atom: &Atom) -> EffectSummary {
        match atom {
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                let mut summary = EffectSummary::default();
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                summary
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                let mut summary = EffectSummary::default();
                for (_, atom) in fields {
                    summary.add_assign(Self::effect_summary_atom(atom));
                }
                summary
            }
            Atom::Lambda { body, .. } => {
                // Lambdas run under the handler stack at their eventual call
                // site, not necessarily the stack where the closure value is
                // created. Keep this summary about immediate call bodies.
                if expr_contains_yield(body) {
                    EffectSummary {
                        blockers: 1,
                        ..EffectSummary::default()
                    }
                } else {
                    EffectSummary::default()
                }
            }
            Atom::BackendSpawnThunk { callback, .. } => Self::effect_summary_atom(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => EffectSummary::default(),
        }
    }

    fn effect_summary_handler(
        &self,
        handler: &MHandler,
        call_stack: &mut HashSet<String>,
        handler_stack: &[HandlerFrame],
    ) -> EffectSummary {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                let mut summary = EffectSummary::default();
                for arm in arms {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                if let Some(arm) = return_clause {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
            MHandler::Composite { handlers, .. } => {
                let mut summary = EffectSummary::default();
                for handler in handlers {
                    summary.add_assign(self.effect_summary_handler(
                        handler,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                let mut summary = Self::effect_summary_atom(op_tuple);
                if let Some(return_lambda) = return_lambda {
                    summary.add_assign(Self::effect_summary_atom(return_lambda));
                }
                summary
            }
            MHandler::Native { .. } => EffectSummary::default(),
        }
    }

    fn effect_summary_handler_arm(
        &self,
        arm: &MHandlerArm,
        call_stack: &mut HashSet<String>,
        handler_stack: &[HandlerFrame],
    ) -> EffectSummary {
        let mut summary = self.effect_summary_expr(&arm.body, call_stack, handler_stack);
        if let Some(cleanup) = &arm.finally_block {
            summary.add_assign(self.effect_summary_expr(cleanup, call_stack, handler_stack));
        }
        summary
    }

    fn yield_is_erasable_under_stack(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
        args: &[Atom],
        handler_stack: &[HandlerFrame],
    ) -> bool {
        self.resolve_direct_call_arm_in_stack(handler_stack, op)
            .is_some_and(|arm| inline_tail_resumptive_arm(arm, args).is_some())
            || self
                .resolve_finally_direct_call_arm_in_stack(handler_stack, op)
                .is_some_and(|arm| {
                    inline_tail_resumptive_arm(arm, args)
                        .and_then(|inlined| inlined.finally_block)
                        .is_some_and(|cleanup| {
                            cleanup_vars_are_available_at_perform_site(&cleanup, args)
                        })
                })
            || self
                .resolve_native_direct_call_handler_in_stack(handler_stack, op)
                .and_then(|handler| {
                    native_direct_call_expr(handler, op, args, crate::ast::NodeId(0))
                })
                .is_some()
    }

    fn summary_callee_body(&self, head: &Atom, args: &[Atom]) -> Option<(String, MExpr)> {
        let (head_name, _, head_source) = imported_variant_head_info(head)?;
        if is_generated_variant_name(&head_name)
            || self
                .inline_blocked_names
                .iter()
                .any(|name| name == &head_name)
        {
            return None;
        }

        if let Some(candidate) = self.variant_candidates.get(&head_name)
            && args.len() == candidate.binding.params.len()
        {
            let body = self.summary_body_with_dict_replacements(&candidate.binding, args)?;
            return Some((format!("local:{}", candidate.binding.name), body));
        }

        let resolved = self.context.resolution.get(&head_source)?;
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return None;
        }
        let candidate = self.lookup_imported_function_variant(resolved)?;
        if args.len() != candidate.binding.params.len() {
            return None;
        }
        let body = self.summary_body_with_dict_replacements(&candidate.binding, args)?;
        Some((
            format!(
                "imported:{}.{}",
                candidate.source_module, candidate.binding.name
            ),
            body,
        ))
    }

    fn summary_body_with_dict_replacements(
        &self,
        binding: &MFunBinding,
        args: &[Atom],
    ) -> Option<MExpr> {
        let mut body = binding.body.clone();
        for replacement in self.dict_param_replacements(&binding.params, args) {
            let free_names = free_atom_names(&replacement.replacement);
            let substituted = subst_expr(
                body,
                &replacement.target,
                &replacement.replacement,
                &free_names,
            );
            if substituted.blocked {
                return None;
            }
            body = substituted.value;
        }
        Some(body)
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

    fn try_inline_let_bound_handler_value(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.handler_value_specialization() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Let { var, value, body } = expr else {
            return (expr, Change::Unchanged);
        };

        let MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source: handler_source,
        } = *value
        else {
            return (MExpr::Let { var, value, body }, Change::Unchanged);
        };

        let handler_value = || MExpr::HandlerValue {
            effects: effects.clone(),
            arms: arms.clone(),
            return_clause: return_clause.clone(),
            source: handler_source,
        };

        let MExpr::With {
            handler:
                MHandler::Dynamic {
                    effects: dynamic_effects,
                    op_tuple,
                    return_lambda,
                    source: dynamic_source,
                },
            body: with_body,
            source: with_source,
        } = *body
        else {
            return (
                MExpr::Let {
                    var,
                    value: Box::new(handler_value()),
                    body,
                },
                Change::Unchanged,
            );
        };

        let rebuild = |return_lambda| MExpr::Let {
            var: var.clone(),
            value: Box::new(handler_value()),
            body: Box::new(MExpr::With {
                handler: MHandler::Dynamic {
                    effects: dynamic_effects.clone(),
                    op_tuple: op_tuple.clone(),
                    return_lambda,
                    source: dynamic_source,
                },
                body: with_body.clone(),
                source: with_source,
            }),
        };

        if !atom_is_var_name(&op_tuple, &var) {
            return (rebuild(return_lambda), Change::Unchanged);
        }
        if return_lambda.is_some() || !handler_effect_sets_match(&effects, &dynamic_effects) {
            return (rebuild(return_lambda), Change::Unchanged);
        }

        (
            MExpr::With {
                handler: MHandler::Static {
                    effects,
                    arms,
                    return_clause: return_clause.map(|arm| *arm),
                    source: handler_source,
                },
                body: with_body,
                source: with_source,
            },
            Change::Changed,
        )
    }

    fn try_inline_let_bound_handler_factory(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.handler_factory_inline() {
            return (expr, Change::Unchanged);
        }

        let (var, value, body, mode) = match expr {
            MExpr::Let { var, value, body } => (var, value, body, None),
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => (var, value, body, Some(mode)),
            other => return (other, Change::Unchanged),
        };

        let MExpr::App { head, args, source } = *value else {
            return (rebuild_binding(var, value, body, mode), Change::Unchanged);
        };

        let local_candidate = match &head {
            Atom::Var { name, .. } => self.handler_factory_candidates.get(&name.name).cloned(),
            _ => None,
        };

        let candidate = if let Some(candidate) = local_candidate {
            candidate
        } else if let Some(candidate) = self.lookup_imported_handler_factory(&head) {
            InlineCandidate {
                params: candidate.params,
                body: candidate.body,
            }
        } else {
            return (
                rebuild_binding(var, Box::new(MExpr::App { head, args, source }), body, mode),
                Change::Unchanged,
            );
        };
        let Some(inlined) = inline_helper_candidate(&candidate, &args) else {
            return (
                rebuild_binding(var, Box::new(MExpr::App { head, args, source }), body, mode),
                Change::Unchanged,
            );
        };
        let Some((prefix, handler_value)) = split_handler_factory_body(inlined) else {
            return (
                rebuild_binding(var, Box::new(MExpr::App { head, args, source }), body, mode),
                Change::Unchanged,
            );
        };

        (
            splice_handler_factory_prefix(
                prefix,
                rebuild_binding(var, Box::new(handler_value), body, mode),
            ),
            Change::Changed,
        )
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
        self.resolve_direct_call_arm_in_stack(&self.handler_stack, op)
    }

    fn resolve_direct_call_arm_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack MHandlerArm> {
        let arms = self.innermost_static_arms_for_op_in_stack(handler_stack, op)?;
        let arm = single_matching_arm(arms, op)?;
        if arm.finally_block.is_some() {
            return None;
        }
        if expr_contains_yield(&arm.body) {
            return None;
        }
        if self.handler_analysis.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive) {
            return None;
        }
        Some(arm)
    }

    fn resolve_finally_direct_call_arm(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&MHandlerArm> {
        self.resolve_finally_direct_call_arm_in_stack(&self.handler_stack, op)
    }

    fn resolve_finally_direct_call_arm_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack MHandlerArm> {
        let arms = self.innermost_static_arms_for_op_in_stack(handler_stack, op)?;
        let arm = single_matching_arm(arms, op)?;
        let cleanup = arm.finally_block.as_ref()?;
        if cleanup.contains_resume() {
            return None;
        }
        if expr_contains_yield(&arm.body) {
            return None;
        }
        if self.handler_analysis.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive) {
            return None;
        }
        Some(arm)
    }

    fn innermost_static_arms_for_op_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack [MHandlerArm]> {
        for frame in handler_stack.iter().rev() {
            if !frame.handles_effect(&op.effect) {
                continue;
            }
            return match frame {
                HandlerFrame::Static { arms, .. } => Some(arms),
                HandlerFrame::Native { .. } | HandlerFrame::Blocking { .. } => None,
            };
        }
        None
    }

    fn try_native_direct_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.native_direct_call() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Yield { op, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some(handler) = self.resolve_native_direct_call_handler(&op) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        if handler.rsplit('.').next().unwrap_or(handler) == "beam_actor"
            && op.effect == "Std.Actor.Process"
            && op.op == "spawn"
            && args.len() == 1
        {
            let (callback, _) = self.optimize_spawn_callback_atom(args[0].clone());
            return (
                MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "spawn".to_string(),
                    args: vec![backend_spawn_thunk_at(callback, source)],
                    source,
                },
                Change::Changed,
            );
        }

        let Some(direct_call) = native_direct_call_expr(handler, &op, &args, source) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        (direct_call, Change::Changed)
    }

    fn resolve_native_direct_call_handler(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&str> {
        self.resolve_native_direct_call_handler_in_stack(&self.handler_stack, op)
    }

    fn resolve_native_direct_call_handler_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack str> {
        for frame in handler_stack.iter().rev() {
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

    fn handler_value_specialization(self) -> bool {
        !self.skip
    }

    fn handler_factory_inline(self) -> bool {
        !self.skip
    }

    fn native_direct_call(self) -> bool {
        !self.skip
    }

    fn helper_inline(self) -> bool {
        !self.skip
    }

    fn native_function_variants(self) -> bool {
        !self.skip
    }

    fn static_function_variants(self) -> bool {
        !self.skip
    }

    fn dead_pure_let(self) -> bool {
        !self.skip
    }

    fn dead_pure_with(self) -> bool {
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

fn expr_is_pure(expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(_) => true,
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_is_pure(value) && expr_is_pure(body)
        }
        MExpr::Ensure { .. } => false,
        MExpr::Case { arms, .. } => arms
            .iter()
            .all(|arm| arm.guard.as_ref().is_none_or(expr_is_pure) && expr_is_pure(&arm.body)),
        MExpr::If {
            then_branch,
            else_branch,
            ..
        } => expr_is_pure(then_branch) && expr_is_pure(else_branch),
        MExpr::FieldAccess { .. }
        | MExpr::RecordUpdate { .. }
        | MExpr::DictMethodAccess { .. }
        | MExpr::BinOp { .. }
        | MExpr::UnaryMinus { .. }
        | MExpr::BitString { .. } => true,
        MExpr::App {
            head: Atom::DictRef { .. },
            ..
        } => true,
        MExpr::Yield { .. }
        | MExpr::App { .. }
        | MExpr::With { .. }
        | MExpr::Resume { .. }
        | MExpr::ForeignCall { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => false,
    }
}

fn expr_is_handler_independent_value(expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(atom) => atom_is_handler_independent_value(atom),
        MExpr::Let { value, body, .. } => {
            expr_is_handler_independent_value(value) && expr_is_handler_independent_value(body)
        }
        MExpr::Case { arms, .. } => arms.iter().all(|arm| {
            arm.guard
                .as_ref()
                .is_none_or(expr_is_handler_independent_value)
                && expr_is_handler_independent_value(&arm.body)
        }),
        MExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            expr_is_handler_independent_value(then_branch)
                && expr_is_handler_independent_value(else_branch)
        }
        MExpr::FieldAccess { .. }
        | MExpr::RecordUpdate { .. }
        | MExpr::DictMethodAccess { .. }
        | MExpr::BinOp { .. }
        | MExpr::UnaryMinus { .. }
        | MExpr::BitString { .. } => true,
        MExpr::App { .. }
        | MExpr::Yield { .. }
        | MExpr::Bind { .. }
        | MExpr::Ensure { .. }
        | MExpr::With { .. }
        | MExpr::Resume { .. }
        | MExpr::ForeignCall { .. }
        | MExpr::Receive { .. }
        | MExpr::LetFun { .. }
        | MExpr::HandlerValue { .. } => false,
    }
}

fn atom_is_handler_independent_value(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } => args.iter().all(atom_is_handler_independent_value),
        Atom::Tuple { elements, .. } => elements.iter().all(atom_is_handler_independent_value),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .all(|(_, atom)| atom_is_handler_independent_value(atom)),
        Atom::Lambda { .. } | Atom::BackendSpawnThunk { .. } => false,
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => true,
    }
}

fn expr_contains_dict_method_access(expr: &MExpr) -> bool {
    match expr {
        MExpr::DictMethodAccess { .. } => true,
        MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
            atom_contains_dict_method_access(atom)
        }
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_dict_method_access)
        }
        MExpr::Bind { value, body, .. }
        | MExpr::Let { value, body, .. }
        | MExpr::Ensure {
            body: value,
            cleanup: body,
        } => expr_contains_dict_method_access(value) || expr_contains_dict_method_access(body),
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_dict_method_access(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_dict_method_access)
                        || expr_contains_dict_method_access(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_dict_method_access(cond)
                || expr_contains_dict_method_access(then_branch)
                || expr_contains_dict_method_access(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_dict_method_access(head)
                || args.iter().any(atom_contains_dict_method_access)
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_dict_method_access(handler) || expr_contains_dict_method_access(body)
        }
        MExpr::FieldAccess { record, .. } | MExpr::UnaryMinus { value: record, .. } => {
            atom_contains_dict_method_access(record)
        }
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_dict_method_access(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_dict_method_access(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_dict_method_access(left) || atom_contains_dict_method_access(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_dict_method_access(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_dict_method_access)
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(expr_contains_dict_method_access)
                    || expr_contains_dict_method_access(&arm.body)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_dict_method_access(timeout) || expr_contains_dict_method_access(body)
            })
        }
        MExpr::LetFun { body, rest, .. } => {
            expr_contains_dict_method_access(body) || expr_contains_dict_method_access(rest)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_dict_method_access)
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_contains_dict_method_access(arm))
        }
    }
}

fn handler_contains_dict_method_access(handler: &MHandler) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_contains_dict_method_access)
                || return_clause
                    .as_ref()
                    .is_some_and(handler_arm_contains_dict_method_access)
        }
        MHandler::Native { .. } => false,
        MHandler::Composite { handlers, .. } => {
            handlers.iter().any(handler_contains_dict_method_access)
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_dict_method_access(op_tuple)
                || return_lambda
                    .as_ref()
                    .is_some_and(atom_contains_dict_method_access)
        }
    }
}

fn handler_arm_contains_dict_method_access(arm: &MHandlerArm) -> bool {
    expr_contains_dict_method_access(&arm.body)
        || arm
            .finally_block
            .as_deref()
            .is_some_and(expr_contains_dict_method_access)
}

fn atom_contains_dict_method_access(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            args.iter().any(atom_contains_dict_method_access)
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_contains_dict_method_access(atom)),
        Atom::Lambda { body, .. } => expr_contains_dict_method_access(body),
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_dict_method_access(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

const INLINE_HELPER_BODY_BUDGET: usize = 30;
const FUNCTION_VARIANT_BODY_BUDGET: usize = 220;
const NATIVE_VARIANT_PREFIX: &str = "__saga_native_variant";
const STATIC_VARIANT_PREFIX: &str = "__saga_static_variant";

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

fn collect_handler_factory_candidates(program: &MProgram) -> HashMap<String, InlineCandidate> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl {
            *counts.entry(f.name.clone()).or_default() += 1;
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
            || !expr_ends_in_handler_value(&f.body)
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

fn collect_dict_constructors(program: &MProgram) -> HashMap<String, MDictConstructor> {
    program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::DictConstructor(dc) => Some((dc.name.clone(), dc.clone())),
            _ => None,
        })
        .collect()
}

pub fn collect_imported_handler_factory_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, ImportedHandlerFactoryCandidate> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();
    let public_pure_vals = collect_public_pure_vals(program);

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if !f.public
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > INLINE_HELPER_BODY_BUDGET
            || expr_contains_imported_handler_factory_forbidden_shape(&f.body)
            || expr_has_private_same_module_refs(
                &f.body,
                source_module,
                &f.name,
                &public_names,
                resolution,
            )
        {
            continue;
        }

        let Some(body) = inline_public_pure_vals(f.body.clone(), &public_pure_vals) else {
            continue;
        };
        if !expr_ends_in_handler_value(&body) {
            continue;
        }

        candidates.insert(
            format!("{source_module}.{}", f.name),
            ImportedHandlerFactoryCandidate {
                source_module: source_module.to_string(),
                params: f.params.clone(),
                body,
            },
        );
    }

    candidates
}

fn collect_public_pure_vals(program: &MProgram) -> HashMap<String, Atom> {
    let mut vals = HashMap::new();
    for decl in program {
        let MDecl::Val(v) = decl else {
            continue;
        };
        if !v.public {
            continue;
        }
        let MExpr::Pure(atom) = &v.value else {
            continue;
        };
        vals.insert(v.name.clone(), atom.clone());
    }
    vals
}

fn inline_public_pure_vals(expr: MExpr, vals: &HashMap<String, Atom>) -> Option<MExpr> {
    let mut expr = expr;
    for (name, atom) in vals {
        let target = MVar {
            name: name.clone(),
            id: 0,
        };
        let free_names = free_atom_names(atom);
        let substituted = subst_expr(expr, &target, atom, &free_names);
        if substituted.blocked {
            return None;
        }
        expr = substituted.value;
    }
    Some(expr)
}

fn collect_variant_candidates(program: &MProgram) -> HashMap<String, VariantCandidate> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if is_generated_variant_name(&f.name) || counts.get(&f.name) != Some(&1) {
            continue;
        }
        if f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > FUNCTION_VARIANT_BODY_BUDGET
        {
            continue;
        }
        candidates.insert(f.name.clone(), VariantCandidate { binding: f.clone() });
    }
    candidates
}

pub fn collect_imported_function_variant_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, ImportedFunctionVariantCandidate> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if !f.public
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > FUNCTION_VARIANT_BODY_BUDGET
            || expr_contains_xmod_variant_forbidden_shape(&f.body)
            || expr_has_private_same_module_refs(
                &f.body,
                source_module,
                &f.name,
                &public_names,
                resolution,
            )
        {
            continue;
        }

        let candidate = ImportedFunctionVariantCandidate {
            source_module: source_module.to_string(),
            binding: f.clone(),
            public_names: public_names.clone(),
        };
        candidates.insert(format!("{source_module}.{}", f.name), candidate);
    }

    candidates
}

pub fn collect_imported_dict_constructors(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
    cloneable_private_helpers: &HashSet<String>,
) -> HashMap<String, MDictConstructor> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::DictConstructor(dc) = decl else {
            continue;
        };
        // Dict constructors are compiler-generated implementation details.
        // The source export table is not a reliable visibility filter for
        // them, and imported optimized bodies may legitimately reference
        // private impl dictionaries. Private helper calls are admitted here:
        // the optimizer rewrites them to caller-local generated helper clones
        // before lowering, so the generated body never needs a remote call to
        // an unexported function.
        if !imported_dict_constructor_supported(dc) {
            continue;
        }
        if dc.methods.iter().any(|method| {
            expr_has_private_same_module_refs_except(
                method,
                source_module,
                &dc.name,
                &public_names,
                resolution,
                cloneable_private_helpers,
            )
        }) {
            continue;
        }
        candidates.insert(dc.name.clone(), dc.clone());
    }

    candidates
}

pub fn collect_imported_private_helper_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, ImportedPrivateHelperCandidate> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && !f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut raw_candidates: HashMap<String, MFunBinding> = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if f.public
            || public_names.contains(&f.name)
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || expr_node_count(&f.body) > FUNCTION_VARIANT_BODY_BUDGET
            || expr_contains_xmod_variant_forbidden_shape(&f.body)
        {
            continue;
        }
        raw_candidates.insert(f.name.clone(), f.clone());
    }

    let mut cloneable = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for (name, f) in &raw_candidates {
            if cloneable.contains(name) {
                continue;
            }
            if expr_has_private_same_module_refs_except(
                &f.body,
                source_module,
                name,
                &public_names,
                resolution,
                &cloneable,
            ) {
                continue;
            }
            cloneable.insert(name.clone());
            changed = true;
        }
    }

    let mut candidates = HashMap::new();
    for name in cloneable {
        let Some(binding) = raw_candidates.get(&name).cloned() else {
            continue;
        };
        candidates.insert(
            format!("{source_module}.{name}"),
            ImportedPrivateHelperCandidate {
                source_module: source_module.to_string(),
                binding,
            },
        );
    }

    candidates
}

fn imported_dict_constructor_supported(dc: &MDictConstructor) -> bool {
    dc.methods.iter().all(|method| {
        let MExpr::Pure(Atom::Lambda { body, .. }) = method else {
            return false;
        };
        expr_node_count(body) <= FUNCTION_VARIANT_BODY_BUDGET
            && !expr_contains_imported_dict_constructor_forbidden_shape(body)
    })
}

fn expr_contains_imported_dict_constructor_forbidden_shape(expr: &MExpr) -> bool {
    expr_contains_xmod_variant_forbidden_shape(expr)
}

fn imported_variant_head_info(atom: &Atom) -> Option<(String, u32, crate::ast::NodeId)> {
    match atom {
        Atom::Var { name, source } => Some((name.name.clone(), name.id, *source)),
        Atom::QualifiedRef { name, source, .. } => Some((name.clone(), source.0, *source)),
        _ => None,
    }
}

fn remove_dead_variant_sources(program: MProgram) -> MProgram {
    let reachable = reachable_decl_names(&program);
    let generated_source_ids = generated_variant_source_ids(&program, &reachable);
    if generated_source_ids.is_empty() {
        return program;
    }

    program
        .into_iter()
        .filter(|decl| match decl {
            MDecl::FunBinding(f)
                if !f.public
                    && !is_generated_variant_name(&f.name)
                    && generated_source_ids.contains(&f.id) =>
            {
                reachable.contains(&f.name)
            }
            _ => true,
        })
        .collect()
}

fn generated_variant_source_ids(
    program: &MProgram,
    reachable: &HashSet<String>,
) -> HashSet<crate::ast::NodeId> {
    program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f)
                if is_generated_variant_name(&f.name) && reachable.contains(&f.name) =>
            {
                Some(f.id)
            }
            _ => None,
        })
        .collect()
}

fn reachable_decl_names(program: &MProgram) -> HashSet<String> {
    let decl_names: HashSet<String> = program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f) => Some(f.name.clone()),
            MDecl::Val(v) => Some(v.name.clone()),
            MDecl::DictConstructor(d) => Some(d.name.clone()),
            MDecl::Passthrough(_) => None,
        })
        .collect();

    let mut reachable = HashSet::new();
    let mut worklist = program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f) if f.public || f.name == "main" || f.name == "tests" => {
                Some(f.name.clone())
            }
            MDecl::Val(v) if v.public || v.name == "main" || v.name == "tests" => {
                Some(v.name.clone())
            }
            MDecl::DictConstructor(d) => Some(d.name.clone()),
            MDecl::Passthrough(_) | MDecl::FunBinding(_) | MDecl::Val(_) => None,
        })
        .collect::<Vec<_>>();

    while let Some(name) = worklist.pop() {
        if !reachable.insert(name.clone()) {
            continue;
        }
        let Some(decl) = program
            .iter()
            .find(|decl| decl_name(decl) == Some(name.as_str()))
        else {
            continue;
        };
        let mut refs = HashSet::new();
        collect_decl_name_refs(decl, &mut refs);
        for reference in refs {
            if decl_names.contains(&reference) && !reachable.contains(&reference) {
                worklist.push(reference);
            }
        }
    }

    reachable
}

fn decl_name(decl: &MDecl) -> Option<&str> {
    match decl {
        MDecl::FunBinding(f) => Some(&f.name),
        MDecl::Val(v) => Some(&v.name),
        MDecl::DictConstructor(d) => Some(&d.name),
        MDecl::Passthrough(_) => None,
    }
}

fn collect_decl_name_refs(decl: &MDecl, out: &mut HashSet<String>) {
    match decl {
        MDecl::FunBinding(f) => {
            if let Some(guard) = &f.guard {
                collect_expr_var_names(guard, out);
            }
            collect_expr_var_names(&f.body, out);
        }
        MDecl::Val(v) => collect_expr_var_names(&v.value, out),
        MDecl::DictConstructor(d) => {
            for method in &d.methods {
                collect_expr_var_names(method, out);
            }
        }
        MDecl::Passthrough(_) => {}
    }
}

fn native_variant_name(name: &str, stack: &[HandlerFrame]) -> String {
    let mut parts = vec![NATIVE_VARIANT_PREFIX.to_string(), sanitize_ident_part(name)];
    for frame in stack {
        match frame {
            HandlerFrame::Native { effects, handler } => {
                parts.push("native".to_string());
                parts.push(sanitize_ident_part(handler));
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
            HandlerFrame::Blocking { effects } => {
                parts.push("blocking".to_string());
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
            HandlerFrame::Static { .. } => {}
        }
    }
    parts.join("__")
}

fn variant_name_for_imported(source_module: &str, name: &str, stack: &[HandlerFrame]) -> String {
    native_variant_name(&format!("xmod__{source_module}__{name}"), stack)
}

fn variant_name_for_imported_static(
    source_module: &str,
    name: &str,
    stack: &[HandlerFrame],
) -> String {
    static_variant_name(&format!("xmod__{source_module}__{name}"), stack)
}

fn imported_private_helper_variant_name(
    source_module: &str,
    name: &str,
    stack: &[HandlerFrame],
) -> String {
    static_variant_name(&format!("xmod_helper__{source_module}__{name}"), stack)
}

fn variant_name_with_dict_key(base: String, dict_replacements: &[DictParamReplacement]) -> String {
    if dict_replacements.is_empty() {
        return base;
    }

    let mut key = String::new();
    for replacement in dict_replacements {
        key.push_str(&replacement.target.name);
        key.push('=');
        key.push_str(&replacement.key);
        key.push(';');
    }
    format!("{base}__dict_{:016x}", stable_key_hash(&key))
}

fn stable_key_hash(value: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in value.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn atom_key(atom: &Atom) -> String {
    match atom {
        Atom::Var { name, .. } => format!("var:{}", name.name),
        Atom::Lit { value, .. } => format!("lit:{value:?}"),
        Atom::Ctor { name, args, .. } => {
            let args = args.iter().map(atom_key).collect::<Vec<_>>().join(",");
            format!("ctor:{name}({args})")
        }
        Atom::Tuple { elements, .. } => {
            let elements = elements.iter().map(atom_key).collect::<Vec<_>>().join(",");
            format!("tuple:({elements})")
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|(name, value)| format!("{name}:{}", atom_key(value)))
                .collect::<Vec<_>>()
                .join(",");
            format!("record:{{{fields}}}")
        }
        Atom::Lambda { source, .. } => format!("lambda:{}", source.0),
        Atom::DictRef { name, .. } => format!("dict:{name}"),
        Atom::QualifiedRef { module, name, .. } => format!("qualified:{module}.{name}"),
        Atom::Symbol { symbol, .. } => format!("symbol:{symbol}"),
        Atom::BackendAtom { atom, .. } => format!("backend_atom:{atom}"),
        Atom::BackendSpawnThunk { source, .. } => format!("spawn_thunk:{}", source.0),
    }
}

fn closed_dict_constructor_arg(atom: &Atom) -> Option<Atom> {
    match atom {
        Atom::Var { .. } | Atom::Lambda { .. } | Atom::QualifiedRef { .. } => None,
        Atom::Lit { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. }
        | Atom::DictRef { .. }
        | Atom::BackendSpawnThunk { .. } => Some(atom.clone()),
        Atom::Ctor { args, .. }
            if args
                .iter()
                .all(|arg| closed_dict_constructor_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::Tuple { elements, .. }
            if elements
                .iter()
                .all(|arg| closed_dict_constructor_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. }
            if fields
                .iter()
                .all(|(_, arg)| closed_dict_constructor_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::Ctor { .. } | Atom::Tuple { .. } | Atom::AnonRecord { .. } | Atom::Record { .. } => {
            None
        }
    }
}

fn prune_unused_dict_variant_args(
    params: &[Pat],
    args: Vec<Atom>,
    body: &MExpr,
    dict_replacements: &[DictParamReplacement],
) -> (Vec<Pat>, Vec<Atom>) {
    if dict_replacements.is_empty() {
        return (params.to_vec(), args);
    }

    let prunable_targets = dict_replacements
        .iter()
        .map(|replacement| replacement.target.clone())
        .collect::<Vec<_>>();
    let mut params_out = Vec::with_capacity(params.len());
    let mut args_out = Vec::with_capacity(args.len());
    let mut pruned_any = false;

    for (param, arg) in params.iter().cloned().zip(args) {
        let target = match &param {
            Pat::Var { name, id, .. } => Some(MVar {
                name: name.clone(),
                id: id.0,
            }),
            _ => None,
        };
        let should_prune = target.as_ref().is_some_and(|target| {
            prunable_targets
                .iter()
                .any(|replacement_target| var_matches(target, replacement_target))
                && !expr_contains_target(body, target)
        });

        if should_prune {
            pruned_any = true;
        } else {
            params_out.push(param);
            args_out.push(arg);
        }
    }

    if pruned_any {
        (params_out, args_out)
    } else {
        (params.to_vec(), args_out)
    }
}

fn static_variant_name(name: &str, stack: &[HandlerFrame]) -> String {
    let mut parts = vec![STATIC_VARIANT_PREFIX.to_string(), sanitize_ident_part(name)];
    for frame in stack {
        match frame {
            HandlerFrame::Static { effects, arms } => {
                parts.push("static".to_string());
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
                let mut arm_keys: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        (
                            arm.op.effect.as_str(),
                            arm.op.op.as_str(),
                            arm.id.0,
                            arm.op.op_index,
                        )
                    })
                    .collect();
                arm_keys.sort();
                for (effect, op, id, op_index) in arm_keys {
                    parts.push(sanitize_ident_part(effect));
                    parts.push(sanitize_ident_part(op));
                    parts.push(id.to_string());
                    parts.push(op_index.to_string());
                }
            }
            HandlerFrame::Blocking { effects } => {
                parts.push("blocking".to_string());
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
            HandlerFrame::Native { effects, handler } => {
                parts.push("native".to_string());
                parts.push(sanitize_ident_part(handler));
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
        }
    }
    parts.join("__")
}

pub(crate) fn is_generated_variant_name(name: &str) -> bool {
    name.starts_with(NATIVE_VARIANT_PREFIX) || name.starts_with(STATIC_VARIANT_PREFIX)
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

fn rewrite_direct_calls_to_name(
    expr: MExpr,
    old_name: &str,
    new_name: &str,
    new_source: crate::ast::NodeId,
) -> MExpr {
    match expr {
        MExpr::App { head, args, source } => MExpr::App {
            head: rewrite_direct_call_atom_to_name(head, old_name, new_name, new_source),
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        MExpr::Pure(atom) => MExpr::Pure(rewrite_non_call_atom_refs(atom)),
        MExpr::Yield { op, args, source } => MExpr::Yield {
            op,
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let value = rewrite_direct_calls_to_name(*value, old_name, new_name, new_source);
            let body = if var.name == old_name {
                *body
            } else {
                rewrite_direct_calls_to_name(*body, old_name, new_name, new_source)
            };
            MExpr::Bind {
                var,
                value: Box::new(value),
                body: Box::new(body),
                mode,
            }
        }
        MExpr::Let { var, value, body } => {
            let value = rewrite_direct_calls_to_name(*value, old_name, new_name, new_source);
            let body = if var.name == old_name {
                *body
            } else {
                rewrite_direct_calls_to_name(*body, old_name, new_name, new_source)
            };
            MExpr::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            }
        }
        MExpr::Ensure { body, cleanup } => MExpr::Ensure {
            body: Box::new(rewrite_direct_calls_to_name(
                *body, old_name, new_name, new_source,
            )),
            cleanup: Box::new(rewrite_direct_calls_to_name(
                *cleanup, old_name, new_name, new_source,
            )),
        },
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => MExpr::Case {
            scrutinee: rewrite_non_call_atom_refs(scrutinee),
            arms: arms
                .into_iter()
                .map(|arm| rewrite_call_arm_refs(arm, old_name, new_name, new_source))
                .collect(),
            source,
        },
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => MExpr::If {
            cond: rewrite_non_call_atom_refs(cond),
            then_branch: Box::new(rewrite_direct_calls_to_name(
                *then_branch,
                old_name,
                new_name,
                new_source,
            )),
            else_branch: Box::new(rewrite_direct_calls_to_name(
                *else_branch,
                old_name,
                new_name,
                new_source,
            )),
            source,
        },
        // A nested handler changes the evidence context. Keep recursive calls
        // inside it on the original slow path unless a later optimizer pass
        // deliberately specializes that inner context too.
        MExpr::With { .. } => expr,
        MExpr::Resume { value, source } => MExpr::Resume {
            value: rewrite_non_call_atom_refs(value),
            source,
        },
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            anon_fields,
            source,
        } => MExpr::FieldAccess {
            record: rewrite_non_call_atom_refs(record),
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
            record: rewrite_non_call_atom_refs(record),
            fields: fields
                .into_iter()
                .map(|(field, atom)| (field, rewrite_non_call_atom_refs(atom)))
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
            dict: rewrite_non_call_atom_refs(dict),
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
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => MExpr::BinOp {
            op,
            left: rewrite_non_call_atom_refs(left),
            right: rewrite_non_call_atom_refs(right),
            source,
        },
        MExpr::UnaryMinus { value, source } => MExpr::UnaryMinus {
            value: rewrite_non_call_atom_refs(value),
            source,
        },
        MExpr::BitString { segments, source } => MExpr::BitString {
            segments: segments
                .into_iter()
                .map(|mut seg| {
                    seg.value = rewrite_non_call_atom_refs(seg.value);
                    seg.size = seg.size.map(rewrite_non_call_atom_refs);
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
                .map(|arm| rewrite_call_arm_refs(arm, old_name, new_name, new_source))
                .collect(),
            after: after.map(|(timeout, body)| {
                (
                    rewrite_non_call_atom_refs(timeout),
                    Box::new(rewrite_direct_calls_to_name(
                        *body, old_name, new_name, new_source,
                    )),
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
        } => {
            let body = if name == old_name || pats_bind_name(&params, old_name) {
                *body
            } else {
                rewrite_direct_calls_to_name(*body, old_name, new_name, new_source)
            };
            let rest = if name == old_name {
                *rest
            } else {
                rewrite_direct_calls_to_name(*rest, old_name, new_name, new_source)
            };
            MExpr::LetFun {
                name,
                params,
                body: Box::new(body),
                rest: Box::new(rest),
                source,
            }
        }
        MExpr::HandlerValue { .. } => expr,
    }
}

fn rewrite_direct_call_atom_to_name(
    atom: Atom,
    old_name: &str,
    new_name: &str,
    new_source: crate::ast::NodeId,
) -> Atom {
    match atom {
        Atom::Var { mut name, .. } if name.name == old_name => {
            name.name = new_name.to_string();
            Atom::Var {
                name,
                source: new_source,
            }
        }
        other => rewrite_non_call_atom_refs(other),
    }
}

fn rewrite_non_call_atom_refs(atom: Atom) -> Atom {
    match atom {
        Atom::Ctor { name, args, source } => Atom::Ctor {
            name,
            args: args.into_iter().map(rewrite_non_call_atom_refs).collect(),
            source,
        },
        Atom::Tuple { elements, source } => Atom::Tuple {
            elements: elements
                .into_iter()
                .map(rewrite_non_call_atom_refs)
                .collect(),
            source,
        },
        Atom::AnonRecord { fields, source } => Atom::AnonRecord {
            fields: fields
                .into_iter()
                .map(|(field, atom)| (field, rewrite_non_call_atom_refs(atom)))
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
                .map(|(field, atom)| (field, rewrite_non_call_atom_refs(atom)))
                .collect(),
            source,
        },
        Atom::BackendSpawnThunk { callback, source } => Atom::BackendSpawnThunk {
            callback: Box::new(rewrite_non_call_atom_refs(*callback)),
            source,
        },
        // Lambda bodies run in their own call context. Do not rewrite recursive
        // calls inside them as part of this generated function variant.
        Atom::Lambda { .. }
        | Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => atom,
    }
}

fn rewrite_call_arm_refs(
    arm: MArm,
    old_name: &str,
    new_name: &str,
    new_source: crate::ast::NodeId,
) -> MArm {
    if pat_binds_name(&arm.pattern, old_name) {
        return arm;
    }
    MArm {
        guard: arm
            .guard
            .map(|guard| rewrite_direct_calls_to_name(guard, old_name, new_name, new_source)),
        body: rewrite_direct_calls_to_name(arm.body, old_name, new_name, new_source),
        ..arm
    }
}

fn helper_params_are_supported(params: &[Pat]) -> bool {
    params.iter().all(supported_inline_param)
}

fn dict_method_params_are_supported(params: &[Pat]) -> bool {
    params.iter().all(|param| {
        supported_inline_param(param)
            || matches!(param, Pat::Constructor { .. } | Pat::Tuple { .. })
    })
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
    for (param, arg) in candidate.params.iter().zip(args).rev() {
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
            Pat::Constructor { .. } | Pat::Tuple { .. } => {
                body = MExpr::Case {
                    scrutinee: arg.clone(),
                    arms: vec![MArm {
                        pattern: param.clone(),
                        guard: None,
                        body,
                        span: param.span(),
                    }],
                    source: param.id(),
                };
            }
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
        NativeArgTransform::PrependAtom(atom) => {
            let mut out = Vec::with_capacity(args.len() + 1);
            out.push(backend_atom_at(atom, source));
            out.extend(args.iter().cloned());
            out
        }
        NativeArgTransform::Reorder(indices) => {
            let mut out = Vec::with_capacity(indices.len());
            for &idx in indices {
                out.push(args.get(idx)?.clone());
            }
            out
        }
        NativeArgTransform::WrapThunk(idx) => {
            if op.effect != "Std.Actor.Process" || op.op != "spawn" {
                return None;
            }
            let callback = args.get(idx)?.clone();
            (0..spec.param_count)
                .map(|i| {
                    if i == idx {
                        Some(backend_spawn_thunk_at(callback.clone(), source))
                    } else {
                        args.get(i).cloned()
                    }
                })
                .collect::<Option<Vec<_>>>()?
        }
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

fn backend_atom_at(atom: &str, source: crate::ast::NodeId) -> Atom {
    Atom::BackendAtom {
        atom: atom.to_string(),
        source,
    }
}

fn backend_spawn_thunk_at(callback: Atom, source: crate::ast::NodeId) -> Atom {
    Atom::BackendSpawnThunk {
        callback: Box::new(callback),
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
        Atom::BackendSpawnThunk { callback, .. } => 1 + atom_node_count(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => 1,
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

fn effect_names_match(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    let a_is_qualified = a.contains('.');
    let b_is_qualified = b.contains('.');
    if a_is_qualified && b_is_qualified {
        return false;
    }
    a.rsplit('.').next() == b.rsplit('.').next()
}

fn handler_effect_sets_match(left: &[String], right: &[String]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .all(|l| right.iter().any(|r| effect_names_match(l, r)))
}

fn handler_value_candidate(expr: &MExpr) -> Option<HandlerValueCandidate> {
    let MExpr::HandlerValue {
        effects,
        arms,
        return_clause,
        source,
    } = expr
    else {
        return None;
    };

    Some(HandlerValueCandidate {
        effects: effects.clone(),
        arms: arms.clone(),
        return_clause: return_clause.clone(),
        source: *source,
    })
}

fn expr_ends_in_handler_value(expr: &MExpr) -> bool {
    match expr {
        MExpr::HandlerValue { .. } => true,
        MExpr::Bind { body, .. } | MExpr::Let { body, .. } => expr_ends_in_handler_value(body),
        _ => false,
    }
}

fn split_handler_factory_body(expr: MExpr) -> Option<(Vec<HandlerFactoryPrefixBinding>, MExpr)> {
    match expr {
        MExpr::HandlerValue { .. } => Some((Vec::new(), expr)),
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        } => {
            let (mut prefix, handler_value) = split_handler_factory_body(*body)?;
            prefix.insert(
                0,
                HandlerFactoryPrefixBinding {
                    var,
                    value: *value,
                    mode: Some(mode),
                },
            );
            Some((prefix, handler_value))
        }
        MExpr::Let { var, value, body } => {
            let (mut prefix, handler_value) = split_handler_factory_body(*body)?;
            prefix.insert(
                0,
                HandlerFactoryPrefixBinding {
                    var,
                    value: *value,
                    mode: None,
                },
            );
            Some((prefix, handler_value))
        }
        _ => None,
    }
}

fn splice_handler_factory_prefix(prefix: Vec<HandlerFactoryPrefixBinding>, body: MExpr) -> MExpr {
    prefix.into_iter().rev().fold(body, |body, binding| {
        rebuild_binding(
            binding.var,
            Box::new(binding.value),
            Box::new(body),
            binding.mode,
        )
    })
}

fn rebuild_binding(
    var: MVar,
    value: Box<MExpr>,
    body: Box<MExpr>,
    mode: Option<crate::codegen::monadic::ir::BindMode>,
) -> MExpr {
    if let Some(mode) = mode {
        MExpr::Bind {
            var,
            value,
            body,
            mode,
        }
    } else {
        MExpr::Let { var, value, body }
    }
}

fn atom_is_var_name(atom: &Atom, var: &MVar) -> bool {
    matches!(
        atom,
        Atom::Var { name, .. } if name.name == var.name
    )
}

fn single_matching_arm<'a>(
    arms: &'a [MHandlerArm],
    op: &crate::codegen::monadic::ir::EffectOpRef,
) -> Option<&'a MHandlerArm> {
    let mut matching = arms
        .iter()
        .filter(|arm| effect_names_match(&arm.op.effect, &op.effect) && arm.op.op == op.op);
    let arm = matching.next()?;
    if matching.next().is_some() {
        return None;
    }
    Some(arm)
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
        Atom::BackendSpawnThunk { callback, .. } => atom_yield_count(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => 0,
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
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_inline_forbidden_shape(callback),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

fn expr_contains_xmod_variant_forbidden_shape(expr: &MExpr) -> bool {
    match expr {
        MExpr::With { .. } | MExpr::LetFun { .. } | MExpr::HandlerValue { .. } => true,
        MExpr::Pure(atom) => atom_contains_xmod_variant_forbidden_shape(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_xmod_variant_forbidden_shape)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_xmod_variant_forbidden_shape(value)
                || expr_contains_xmod_variant_forbidden_shape(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_xmod_variant_forbidden_shape(body)
                || expr_contains_xmod_variant_forbidden_shape(cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_xmod_variant_forbidden_shape(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_xmod_variant_forbidden_shape)
                        || expr_contains_xmod_variant_forbidden_shape(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_xmod_variant_forbidden_shape(cond)
                || expr_contains_xmod_variant_forbidden_shape(then_branch)
                || expr_contains_xmod_variant_forbidden_shape(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_xmod_variant_forbidden_shape(head)
                || args.iter().any(atom_contains_xmod_variant_forbidden_shape)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_xmod_variant_forbidden_shape(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_xmod_variant_forbidden_shape(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_xmod_variant_forbidden_shape(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_xmod_variant_forbidden_shape(left)
                || atom_contains_xmod_variant_forbidden_shape(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_xmod_variant_forbidden_shape(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_xmod_variant_forbidden_shape)
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(expr_contains_xmod_variant_forbidden_shape)
                    || expr_contains_xmod_variant_forbidden_shape(&arm.body)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_xmod_variant_forbidden_shape(timeout)
                    || expr_contains_xmod_variant_forbidden_shape(body)
            })
        }
    }
}

fn expr_contains_imported_handler_factory_forbidden_shape(expr: &MExpr) -> bool {
    match expr {
        MExpr::With { .. } | MExpr::Receive { .. } | MExpr::LetFun { .. } => true,
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(|arm| {
                expr_contains_imported_handler_factory_forbidden_shape(&arm.body)
                    || arm.finally_block.as_ref().is_some_and(|cleanup| {
                        expr_contains_imported_handler_factory_forbidden_shape(cleanup)
                    })
            }) || return_clause.as_ref().is_some_and(|arm| {
                expr_contains_imported_handler_factory_forbidden_shape(&arm.body)
                    || arm.finally_block.as_ref().is_some_and(|cleanup| {
                        expr_contains_imported_handler_factory_forbidden_shape(cleanup)
                    })
            })
        }
        MExpr::Pure(atom) => atom_contains_xmod_variant_forbidden_shape(atom),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_contains_xmod_variant_forbidden_shape)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_imported_handler_factory_forbidden_shape(value)
                || expr_contains_imported_handler_factory_forbidden_shape(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_imported_handler_factory_forbidden_shape(body)
                || expr_contains_imported_handler_factory_forbidden_shape(cleanup)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_xmod_variant_forbidden_shape(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_contains_imported_handler_factory_forbidden_shape)
                        || expr_contains_imported_handler_factory_forbidden_shape(&arm.body)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_xmod_variant_forbidden_shape(cond)
                || expr_contains_imported_handler_factory_forbidden_shape(then_branch)
                || expr_contains_imported_handler_factory_forbidden_shape(else_branch)
        }
        MExpr::App { head, args, .. } => {
            atom_contains_xmod_variant_forbidden_shape(head)
                || args.iter().any(atom_contains_xmod_variant_forbidden_shape)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => atom_contains_xmod_variant_forbidden_shape(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_xmod_variant_forbidden_shape(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_xmod_variant_forbidden_shape(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_xmod_variant_forbidden_shape(left)
                || atom_contains_xmod_variant_forbidden_shape(right)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|seg| {
            atom_contains_xmod_variant_forbidden_shape(&seg.value)
                || seg
                    .size
                    .as_ref()
                    .is_some_and(atom_contains_xmod_variant_forbidden_shape)
        }),
    }
}

fn atom_contains_xmod_variant_forbidden_shape(atom: &Atom) -> bool {
    match atom {
        Atom::Lambda { .. } => true,
        Atom::Ctor { args, .. } => args.iter().any(atom_contains_xmod_variant_forbidden_shape),
        Atom::Tuple { elements, .. } => elements
            .iter()
            .any(atom_contains_xmod_variant_forbidden_shape),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_contains_xmod_variant_forbidden_shape(atom)),
        Atom::BackendSpawnThunk { callback, .. } => {
            atom_contains_xmod_variant_forbidden_shape(callback)
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
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
        Atom::BackendSpawnThunk { callback, .. } => atom_calls_any(callback, names),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
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

fn expr_has_private_same_module_refs(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
) -> bool {
    expr_has_private_same_module_refs_except(
        expr,
        source_module,
        self_name,
        public_names,
        resolution,
        &HashSet::new(),
    )
}

fn expr_has_private_same_module_refs_except(
    expr: &MExpr,
    source_module: &str,
    self_name: &str,
    public_names: &HashSet<String>,
    resolution: &ResolutionMap,
    allowed_private_names: &HashSet<String>,
) -> bool {
    let mut refs = Vec::new();
    collect_app_head_refs(expr, &mut refs);
    refs.into_iter().any(|(name, source)| {
        let Some(resolved) = resolution.get(&source) else {
            return false;
        };
        if !matches!(
            resolved.kind,
            ResolvedCodegenKind::BeamFunction { .. }
                | ResolvedCodegenKind::ExternalFunction { .. }
                | ResolvedCodegenKind::Intrinsic { .. }
        ) {
            return false;
        }
        let same_module = resolved
            .source_module
            .as_deref()
            .is_none_or(|module| module == source_module);
        same_module
            && name != self_name
            && !public_names.contains(&name)
            && !allowed_private_names.contains(&name)
    })
}

fn collect_app_head_refs(expr: &MExpr, out: &mut Vec<(String, crate::ast::NodeId)>) {
    match expr {
        MExpr::App { head, args, .. } => {
            if let Atom::Var { name, source } = head {
                out.push((name.name.clone(), *source));
            }
            collect_atom_list_app_refs(args, out);
        }
        MExpr::Pure(atom) => collect_atom_app_refs(atom, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_app_refs(args, out)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_app_head_refs(value, out);
            collect_app_head_refs(body, out);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_app_head_refs(body, out);
            collect_app_head_refs(cleanup, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_app_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_app_head_refs(guard, out);
                }
                collect_app_head_refs(&arm.body, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_app_refs(cond, out);
            collect_app_head_refs(then_branch, out);
            collect_app_head_refs(else_branch, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_app_refs(handler, out);
            collect_app_head_refs(body, out);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_app_refs(value, out),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_app_refs(record, out);
            for (_, atom) in fields {
                collect_atom_app_refs(atom, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_app_refs(left, out);
            collect_atom_app_refs(right, out);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_app_refs(&seg.value, out);
                if let Some(size) = &seg.size {
                    collect_atom_app_refs(size, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_app_head_refs(guard, out);
                }
                collect_app_head_refs(&arm.body, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_app_refs(timeout, out);
                collect_app_head_refs(body, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_app_head_refs(body, out);
            collect_app_head_refs(rest, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_app_refs(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_app_refs(arm, out);
            }
        }
    }
}

fn collect_atom_app_refs(atom: &Atom, out: &mut Vec<(String, crate::ast::NodeId)>) {
    match atom {
        Atom::Lambda { body, .. } => collect_app_head_refs(body, out),
        Atom::Ctor { args, .. } => collect_atom_list_app_refs(args, out),
        Atom::Tuple { elements, .. } => collect_atom_list_app_refs(elements, out),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_app_refs(atom, out);
            }
        }
        Atom::BackendSpawnThunk { callback, .. } => collect_atom_app_refs(callback, out),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

fn collect_atom_list_app_refs(atoms: &[Atom], out: &mut Vec<(String, crate::ast::NodeId)>) {
    for atom in atoms {
        collect_atom_app_refs(atom, out);
    }
}

fn collect_handler_app_refs(handler: &MHandler, out: &mut Vec<(String, crate::ast::NodeId)>) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_app_refs(arm, out);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_app_refs(arm, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_app_refs(handler, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_app_refs(op_tuple, out);
            if let Some(atom) = return_lambda {
                collect_atom_app_refs(atom, out);
            }
        }
    }
}

fn collect_handler_arm_app_refs(arm: &MHandlerArm, out: &mut Vec<(String, crate::ast::NodeId)>) {
    collect_app_head_refs(&arm.body, out);
    if let Some(cleanup) = &arm.finally_block {
        collect_app_head_refs(cleanup, out);
    }
}

fn atom_contains_yield(atom: &Atom) -> bool {
    match atom {
        Atom::Ctor { args, .. } => args.iter().any(atom_contains_yield),
        Atom::Tuple { elements, .. } => elements.iter().any(atom_contains_yield),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().any(|(_, atom)| atom_contains_yield(atom))
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_yield(callback),
        Atom::Lambda { body, .. } => expr_contains_yield(body),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
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
        Atom::BackendSpawnThunk { .. } => atom,
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => atom,
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
        Atom::BackendSpawnThunk { callback, source } => {
            let out = subst_atom(*callback, target, replacement, replacement_free_names);
            map_subst(out, |callback| Atom::BackendSpawnThunk {
                callback: Box::new(callback),
                source,
            })
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => SubstOutcome::unchanged(atom),
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
    collect_atom_free_names(atom, &mut out, &HashSet::new());
    out
}

fn collect_atom_free_names(atom: &Atom, out: &mut HashSet<String>, bound: &HashSet<String>) {
    match atom {
        Atom::Var { name, .. } => {
            if !bound.contains(&name.name) {
                out.insert(name.name.clone());
            }
        }
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            for arg in args {
                collect_atom_free_names(arg, out, bound);
            }
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_free_names(atom, out, bound);
            }
        }
        Atom::Lambda { params, body, .. } => {
            let mut scoped = bound.clone();
            scoped.extend(bound_names_in_pats(params));
            collect_expr_free_names(body, out, &scoped);
        }
        Atom::BackendSpawnThunk { callback, .. } => {
            collect_atom_free_names(callback, out, bound);
        }
        Atom::QualifiedRef { name, .. } => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

fn collect_atom_list_free_names(
    atoms: &[Atom],
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    for atom in atoms {
        collect_atom_free_names(atom, out, bound);
    }
}

fn collect_expr_free_names(expr: &MExpr, out: &mut HashSet<String>, bound: &HashSet<String>) {
    match expr {
        MExpr::Pure(atom) => collect_atom_free_names(atom, out, bound),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            collect_atom_list_free_names(args, out, bound);
        }
        MExpr::Bind {
            var, value, body, ..
        }
        | MExpr::Let { var, value, body } => {
            collect_expr_free_names(value, out, bound);
            let mut scoped = bound.clone();
            scoped.insert(var.name.clone());
            collect_expr_free_names(body, out, &scoped);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_expr_free_names(body, out, bound);
            collect_expr_free_names(cleanup, out, bound);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_free_names(scrutinee, out, bound);
            for arm in arms {
                let mut scoped = bound.clone();
                scoped.extend(bound_names_in_pat(&arm.pattern));
                if let Some(guard) = &arm.guard {
                    collect_expr_free_names(guard, out, &scoped);
                }
                collect_expr_free_names(&arm.body, out, &scoped);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_free_names(cond, out, bound);
            collect_expr_free_names(then_branch, out, bound);
            collect_expr_free_names(else_branch, out, bound);
        }
        MExpr::App { head, args, .. } => {
            collect_atom_free_names(head, out, bound);
            collect_atom_list_free_names(args, out, bound);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_free_names(handler, out, bound);
            collect_expr_free_names(body, out, bound);
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => collect_atom_free_names(value, out, bound),
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_free_names(record, out, bound);
            for (_, atom) in fields {
                collect_atom_free_names(atom, out, bound);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_free_names(left, out, bound);
            collect_atom_free_names(right, out, bound);
        }
        MExpr::BitString { segments, .. } => {
            for seg in segments {
                collect_atom_free_names(&seg.value, out, bound);
                if let Some(size) = &seg.size {
                    collect_atom_free_names(size, out, bound);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                let mut scoped = bound.clone();
                scoped.extend(bound_names_in_pat(&arm.pattern));
                if let Some(guard) = &arm.guard {
                    collect_expr_free_names(guard, out, &scoped);
                }
                collect_expr_free_names(&arm.body, out, &scoped);
            }
            if let Some((timeout, body)) = after {
                collect_atom_free_names(timeout, out, bound);
                collect_expr_free_names(body, out, bound);
            }
        }
        MExpr::LetFun {
            name,
            params,
            body,
            rest,
            ..
        } => {
            let mut body_scope = bound.clone();
            body_scope.insert(name.clone());
            body_scope.extend(bound_names_in_pats(params));
            collect_expr_free_names(body, out, &body_scope);

            let mut rest_scope = bound.clone();
            rest_scope.insert(name.clone());
            collect_expr_free_names(rest, out, &rest_scope);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_free_names(arm, out, bound);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_free_names(arm, out, bound);
            }
        }
    }
}

fn collect_handler_free_names(
    handler: &MHandler,
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_free_names(arm, out, bound);
            }
            if let Some(arm) = return_clause {
                collect_handler_arm_free_names(arm, out, bound);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_free_names(handler, out, bound);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_free_names(op_tuple, out, bound);
            if let Some(atom) = return_lambda {
                collect_atom_free_names(atom, out, bound);
            }
        }
    }
}

fn collect_handler_arm_free_names(
    arm: &MHandlerArm,
    out: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    let mut scoped = bound.clone();
    scoped.extend(bound_names_in_pats(&arm.params));
    collect_expr_free_names(&arm.body, out, &scoped);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_free_names(finally_block, out, &scoped);
    }
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
        Atom::BackendSpawnThunk { callback, .. } => collect_atom_var_names(callback, out),
        Atom::QualifiedRef { name, .. } => {
            // Reachability cleanup uses this collector too. A same-module
            // function may survive in monadic IR as a QualifiedRef, so count
            // the short name conservatively rather than deleting a callee that
            // the lowerer will still emit as a local call.
            out.insert(name.clone());
        }
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
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
                    pat_has_nonbinding_ref(&arm.pattern, &target.name)
                        || !pat_binds_name(&arm.pattern, &target.name)
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
                pat_has_nonbinding_ref(&arm.pattern, &target.name)
                    || !pat_binds_name(&arm.pattern, &target.name)
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
        Atom::BackendSpawnThunk { callback, .. } => atom_contains_target(callback, target),
        Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
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
mod tests;
