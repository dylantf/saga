//! Lightweight structural counters for monadic IR inspection.
//!
//! These numbers are diagnostics only. They are useful for seeing whether an
//! optimizer pass removed `Yield`/`Bind` scaffolding or introduced direct
//! `ForeignCall`s, but they are not a semantic metric.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::codegen::monadic::ir::{Atom, MArm, MDecl, MExpr, MHandler, MHandlerArm, MProgram};
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};

fn is_generated_variant_name(name: &str) -> bool {
    name.starts_with("__saga_native_variant") || name.starts_with("__saga_static_variant")
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Stats {
    pub decls: usize,
    pub source_decls: usize,
    pub generated_decls: usize,
    pub exprs: usize,
    pub atoms: usize,
    pub pure: usize,
    pub yield_: usize,
    pub bind: usize,
    pub let_: usize,
    pub ensure: usize,
    pub app: usize,
    pub foreign_call: usize,
    pub with: usize,
    pub resume: usize,
    pub case: usize,
    pub if_: usize,
    pub receive: usize,
    pub letfun: usize,
    pub handler_value: usize,
    pub lambda_atoms: usize,
    pub handler_arms: usize,
    pub finally_blocks: usize,
    pub static_handlers: usize,
    pub native_handlers: usize,
    pub dynamic_handlers: usize,
    pub composite_handlers: usize,
    pub yield_ops: BTreeMap<String, usize>,
    pub foreign_calls: BTreeMap<String, usize>,
}

impl Stats {
    pub fn collect_program(program: &MProgram) -> Self {
        let mut stats = Self::default();
        for decl in program {
            stats.visit_decl(decl);
        }
        stats
    }

    pub fn collect_reachable_program(program: &MProgram, roots: &[&str]) -> Self {
        let decls: BTreeMap<&str, &MDecl> = program
            .iter()
            .filter_map(|decl| match decl {
                MDecl::FunBinding(f) => Some((f.name.as_str(), decl)),
                MDecl::Val(v) => Some((v.name.as_str(), decl)),
                MDecl::DictConstructor(d) => Some((d.name.as_str(), decl)),
                MDecl::Passthrough(_) => None,
            })
            .collect();

        let mut stats = Self::default();
        let mut seen = BTreeSet::new();
        let mut worklist = roots
            .iter()
            .filter(|root| decls.contains_key(**root))
            .map(|root| (*root).to_string())
            .collect::<Vec<_>>();

        while let Some(name) = worklist.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let Some(decl) = decls.get(name.as_str()) else {
                continue;
            };
            stats.visit_decl(decl);

            let mut calls = BTreeSet::new();
            collect_decl_calls(decl, &mut calls);
            for call in calls {
                if decls.contains_key(call.as_str()) && !seen.contains(&call) {
                    worklist.push(call);
                }
            }
        }

        stats
    }

    fn visit_decl(&mut self, decl: &MDecl) {
        self.decls += 1;
        if decl_is_optimizer_generated(decl) {
            self.generated_decls += 1;
        } else {
            self.source_decls += 1;
        }
        match decl {
            MDecl::FunBinding(f) => {
                if let Some(guard) = &f.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&f.body);
            }
            MDecl::Val(v) => self.visit_expr(&v.value),
            MDecl::DictConstructor(d) => {
                for method in &d.methods {
                    self.visit_expr(method);
                }
            }
            MDecl::Passthrough(_) => {}
        }
    }

    fn add_assign(&mut self, other: &Self) {
        self.decls += other.decls;
        self.source_decls += other.source_decls;
        self.generated_decls += other.generated_decls;
        self.exprs += other.exprs;
        self.atoms += other.atoms;
        self.pure += other.pure;
        self.yield_ += other.yield_;
        self.bind += other.bind;
        self.let_ += other.let_;
        self.ensure += other.ensure;
        self.app += other.app;
        self.foreign_call += other.foreign_call;
        self.with += other.with;
        self.resume += other.resume;
        self.case += other.case;
        self.if_ += other.if_;
        self.receive += other.receive;
        self.letfun += other.letfun;
        self.handler_value += other.handler_value;
        self.lambda_atoms += other.lambda_atoms;
        self.handler_arms += other.handler_arms;
        self.finally_blocks += other.finally_blocks;
        self.static_handlers += other.static_handlers;
        self.native_handlers += other.native_handlers;
        self.dynamic_handlers += other.dynamic_handlers;
        self.composite_handlers += other.composite_handlers;
        for (op, count) in &other.yield_ops {
            *self.yield_ops.entry(op.clone()).or_default() += count;
        }
        for (call, count) in &other.foreign_calls {
            *self.foreign_calls.entry(call.clone()).or_default() += count;
        }
    }

    fn visit_expr(&mut self, expr: &MExpr) {
        self.exprs += 1;
        match expr {
            MExpr::Pure(atom) => {
                self.pure += 1;
                self.visit_atom(atom);
            }
            MExpr::Yield { op, args, .. } => {
                self.yield_ += 1;
                *self
                    .yield_ops
                    .entry(format!("{}::{}", op.effect, op.op))
                    .or_default() += 1;
                self.visit_atoms(args);
            }
            MExpr::Bind { value, body, .. } => {
                self.bind += 1;
                self.visit_expr(value);
                self.visit_expr(body);
            }
            MExpr::Let { value, body, .. } => {
                self.let_ += 1;
                self.visit_expr(value);
                self.visit_expr(body);
            }
            MExpr::Ensure { body, cleanup } => {
                self.ensure += 1;
                self.visit_expr(body);
                self.visit_expr(cleanup);
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.case += 1;
                self.visit_atom(scrutinee);
                for arm in arms {
                    self.visit_arm(arm);
                }
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.if_ += 1;
                self.visit_atom(cond);
                self.visit_expr(then_branch);
                self.visit_expr(else_branch);
            }
            MExpr::App { head, args, .. } => {
                self.app += 1;
                self.visit_atom(head);
                self.visit_atoms(args);
            }
            MExpr::With { handler, body, .. } => {
                self.with += 1;
                self.visit_handler(handler);
                self.visit_expr(body);
            }
            MExpr::Resume { value, .. } => {
                self.resume += 1;
                self.visit_atom(value);
            }
            MExpr::FieldAccess { record, .. } => self.visit_atom(record),
            MExpr::RecordUpdate { record, fields, .. } => {
                self.visit_atom(record);
                for (_, atom) in fields {
                    self.visit_atom(atom);
                }
            }
            MExpr::DictMethodAccess { dict, .. } => self.visit_atom(dict),
            MExpr::ForeignCall {
                module, func, args, ..
            } => {
                self.foreign_call += 1;
                *self
                    .foreign_calls
                    .entry(format!("{module}:{func}"))
                    .or_default() += 1;
                self.visit_atoms(args);
            }
            MExpr::BinOp { left, right, .. } => {
                self.visit_atom(left);
                self.visit_atom(right);
            }
            MExpr::UnaryMinus { value, .. } => self.visit_atom(value),
            MExpr::BitString { segments, .. } => {
                for segment in segments {
                    self.visit_atom(&segment.value);
                    if let Some(size) = &segment.size {
                        self.visit_atom(size);
                    }
                }
            }
            MExpr::Receive { arms, after, .. } => {
                self.receive += 1;
                for arm in arms {
                    self.visit_arm(arm);
                }
                if let Some((timeout, body)) = after {
                    self.visit_atom(timeout);
                    self.visit_expr(body);
                }
            }
            MExpr::LetFun { body, rest, .. } => {
                self.letfun += 1;
                self.visit_expr(body);
                self.visit_expr(rest);
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                self.handler_value += 1;
                for arm in arms {
                    self.visit_handler_arm(arm);
                }
                if let Some(return_clause) = return_clause {
                    self.visit_handler_arm(return_clause);
                }
            }
        }
    }

    fn visit_atom(&mut self, atom: &Atom) {
        self.atoms += 1;
        match atom {
            Atom::Ctor { args, .. } => self.visit_atoms(args),
            Atom::Tuple { elements, .. } => self.visit_atoms(elements),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                for (_, atom) in fields {
                    self.visit_atom(atom);
                }
            }
            Atom::Lambda { body, .. } => {
                self.lambda_atoms += 1;
                self.visit_expr(body);
            }
            Atom::BackendSpawnThunk { callback, .. } => self.visit_atom(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => {}
        }
    }

    fn visit_atoms(&mut self, atoms: &[Atom]) {
        for atom in atoms {
            self.visit_atom(atom);
        }
    }

    fn visit_arm(&mut self, arm: &MArm) {
        if let Some(guard) = &arm.guard {
            self.visit_expr(guard);
        }
        self.visit_expr(&arm.body);
    }

    fn visit_handler(&mut self, handler: &MHandler) {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                self.static_handlers += 1;
                for arm in arms {
                    self.visit_handler_arm(arm);
                }
                if let Some(return_clause) = return_clause {
                    self.visit_handler_arm(return_clause);
                }
            }
            MHandler::Native { .. } => self.native_handlers += 1,
            MHandler::Composite { handlers, .. } => {
                self.composite_handlers += 1;
                for handler in handlers {
                    self.visit_handler(handler);
                }
            }
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                self.dynamic_handlers += 1;
                self.visit_atom(op_tuple);
                if let Some(return_lambda) = return_lambda {
                    self.visit_atom(return_lambda);
                }
            }
        }
    }

    fn visit_handler_arm(&mut self, arm: &MHandlerArm) {
        self.handler_arms += 1;
        self.visit_expr(&arm.body);
        if let Some(finally_block) = &arm.finally_block {
            self.finally_blocks += 1;
            self.visit_expr(finally_block);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatsDiff {
    before: Stats,
    after: Stats,
}

impl StatsDiff {
    pub fn new(before: Stats, after: Stats) -> Self {
        Self { before, after }
    }

    pub fn before(&self) -> &Stats {
        &self.before
    }

    pub fn after(&self) -> &Stats {
        &self.after
    }

    fn fmt_with_title(&self, f: &mut fmt::Formatter<'_>, title: &str) -> fmt::Result {
        writeln!(f, "{title}")?;
        writeln!(f, "metric                before    after    delta")?;
        writeln!(f, "----------------------------------------------")?;
        for (name, before, after) in rows(&self.before, &self.after) {
            writeln!(
                f,
                "{name:<20} {before:>6} {after:>8} {delta:>+8}",
                delta = after as isize - before as isize
            )?;
        }
        write_breakdown(
            f,
            "Yield ops",
            &self.before.yield_ops,
            &self.after.yield_ops,
        )?;
        write_breakdown(
            f,
            "Foreign calls",
            &self.before.foreign_calls,
            &self.after.foreign_calls,
        )?;
        Ok(())
    }
}

impl fmt::Display for StatsDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_title(f, "monadic IR stats")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CallRef {
    module: Option<String>,
    name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DeclGraphStats {
    stats: Stats,
    calls: BTreeSet<CallRef>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ModuleGraphStats {
    decls: BTreeMap<String, DeclGraphStats>,
}

impl ModuleGraphStats {
    fn collect_program(program: &MProgram, resolution: &ResolutionMap) -> Self {
        let mut decls = BTreeMap::new();
        for decl in program {
            let Some(name) = decl_name(decl) else {
                continue;
            };
            let mut stats = Stats::default();
            stats.visit_decl(decl);
            let mut calls = BTreeSet::new();
            collect_decl_call_refs(decl, resolution, &mut calls);
            decls.insert(name.to_string(), DeclGraphStats { stats, calls });
        }
        Self { decls }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModuleGraphStatsDiff {
    before: ModuleGraphStats,
    after: ModuleGraphStats,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatsReport {
    whole: StatsDiff,
    reachable: Option<StatsDiff>,
    graph: Option<ModuleGraphStatsDiff>,
}

impl StatsReport {
    pub fn new(whole: StatsDiff, reachable: Option<StatsDiff>) -> Self {
        Self {
            whole,
            reachable,
            graph: None,
        }
    }

    pub fn with_module_graph(
        whole: StatsDiff,
        reachable: Option<StatsDiff>,
        before_program: &MProgram,
        after_program: &MProgram,
        resolution: &ResolutionMap,
    ) -> Self {
        Self {
            whole,
            reachable,
            graph: Some(ModuleGraphStatsDiff {
                before: ModuleGraphStats::collect_program(before_program, resolution),
                after: ModuleGraphStats::collect_program(after_program, resolution),
            }),
        }
    }

    pub fn whole(&self) -> &StatsDiff {
        &self.whole
    }

    pub fn reachable(&self) -> Option<&StatsDiff> {
        self.reachable.as_ref()
    }

    pub fn summary(&self, module_name: &str) -> String {
        let mut lines = Vec::new();
        lines.push(format!("{}: {}", module_name, summarize_diff(&self.whole)));
        if let Some(reachable) = &self.reachable {
            lines.push(format!("  entry-reachable: {}", summarize_diff(reachable)));
            if let Some(residual) = residual_yield_summary(reachable.after(), 5) {
                lines.push(format!("  residual yields: {residual}"));
            }
        } else if let Some(residual) = residual_yield_summary(self.whole.after(), 5) {
            lines.push(format!("  residual yields: {residual}"));
        }
        lines.join("\n")
    }

    pub fn whole_app_summary(
        reports: &[(String, StatsReport)],
        entry_module: &str,
        entry_decl: &str,
    ) -> Option<String> {
        let before = collect_whole_app_reachable(reports, entry_module, entry_decl, false)?;
        let after = collect_whole_app_reachable(reports, entry_module, entry_decl, true)?;
        if before.decls == 0 && after.decls == 0 {
            return None;
        }
        let diff = StatsDiff::new(before, after);
        let mut lines = vec![format!(
            "whole-app entry-reachable from {entry_module}.{entry_decl}: {}",
            summarize_diff(&diff)
        )];
        if let Some(residual) = residual_yield_summary(diff.after(), 10) {
            lines.push(format!("  residual yields: {residual}"));
        }
        Some(lines.join("\n"))
    }
}

impl fmt::Display for StatsReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.whole.fmt_with_title(f, "monadic IR stats")?;
        if let Some(reachable) = &self.reachable {
            writeln!(f)?;
            reachable.fmt_with_title(f, "entry-reachable monadic IR stats")?;
        }
        Ok(())
    }
}

fn collect_decl_calls(decl: &MDecl, out: &mut BTreeSet<String>) {
    match decl {
        MDecl::FunBinding(f) => {
            if let Some(guard) = &f.guard {
                collect_expr_calls(guard, out);
            }
            collect_expr_calls(&f.body, out);
        }
        MDecl::Val(v) => collect_expr_calls(&v.value, out),
        MDecl::DictConstructor(d) => {
            for method in &d.methods {
                collect_expr_calls(method, out);
            }
        }
        MDecl::Passthrough(_) => {}
    }
}

fn decl_name(decl: &MDecl) -> Option<&str> {
    match decl {
        MDecl::FunBinding(f) => Some(&f.name),
        MDecl::Val(v) => Some(&v.name),
        MDecl::DictConstructor(d) => Some(&d.name),
        MDecl::Passthrough(_) => None,
    }
}

fn collect_whole_app_reachable(
    reports: &[(String, StatsReport)],
    entry_module: &str,
    entry_decl: &str,
    after: bool,
) -> Option<Stats> {
    let modules: BTreeMap<&str, &ModuleGraphStats> = reports
        .iter()
        .filter_map(|(module, report)| {
            let graph = report.graph.as_ref()?;
            Some((
                module.as_str(),
                if after { &graph.after } else { &graph.before },
            ))
        })
        .collect();
    if modules.is_empty() {
        return None;
    }

    let mut stats = Stats::default();
    let mut seen = BTreeSet::new();
    let mut worklist = vec![(entry_module.to_string(), entry_decl.to_string())];

    while let Some((module, name)) = worklist.pop() {
        if !seen.insert((module.clone(), name.clone())) {
            continue;
        }
        let Some(module_stats) = modules.get(module.as_str()) else {
            continue;
        };
        let Some(decl) = module_stats.decls.get(name.as_str()) else {
            continue;
        };

        stats.add_assign(&decl.stats);
        for call in &decl.calls {
            let target_module = call.module.as_deref().unwrap_or(module.as_str());
            if modules
                .get(target_module)
                .is_some_and(|m| m.decls.contains_key(call.name.as_str()))
            {
                worklist.push((target_module.to_string(), call.name.clone()));
            }
        }
    }

    Some(stats)
}

fn collect_decl_call_refs(decl: &MDecl, resolution: &ResolutionMap, out: &mut BTreeSet<CallRef>) {
    match decl {
        MDecl::FunBinding(f) => {
            if let Some(guard) = &f.guard {
                collect_expr_call_refs(guard, resolution, out);
            }
            collect_expr_call_refs(&f.body, resolution, out);
        }
        MDecl::Val(v) => collect_expr_call_refs(&v.value, resolution, out),
        MDecl::DictConstructor(d) => {
            for method in &d.methods {
                collect_expr_call_refs(method, resolution, out);
            }
        }
        MDecl::Passthrough(_) => {}
    }
}

fn collect_expr_call_refs(expr: &MExpr, resolution: &ResolutionMap, out: &mut BTreeSet<CallRef>) {
    match expr {
        MExpr::App { head, args, .. } => {
            if let Some(call) = call_ref_for_head(head, resolution) {
                out.insert(call);
            }
            collect_atom_call_refs(head, resolution, out);
            for arg in args {
                collect_atom_call_refs(arg, resolution, out);
            }
        }
        MExpr::Pure(atom)
        | MExpr::Resume { value: atom, .. }
        | MExpr::FieldAccess { record: atom, .. }
        | MExpr::DictMethodAccess { dict: atom, .. }
        | MExpr::UnaryMinus { value: atom, .. } => collect_atom_call_refs(atom, resolution, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            for arg in args {
                collect_atom_call_refs(arg, resolution, out);
            }
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_expr_call_refs(value, resolution, out);
            collect_expr_call_refs(body, resolution, out);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_expr_call_refs(body, resolution, out);
            collect_expr_call_refs(cleanup, resolution, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_call_refs(scrutinee, resolution, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_call_refs(guard, resolution, out);
                }
                collect_expr_call_refs(&arm.body, resolution, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_call_refs(cond, resolution, out);
            collect_expr_call_refs(then_branch, resolution, out);
            collect_expr_call_refs(else_branch, resolution, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_call_refs(handler, resolution, out);
            collect_expr_call_refs(body, resolution, out);
        }
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_call_refs(record, resolution, out);
            for (_, atom) in fields {
                collect_atom_call_refs(atom, resolution, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_call_refs(left, resolution, out);
            collect_atom_call_refs(right, resolution, out);
        }
        MExpr::BitString { segments, .. } => {
            for segment in segments {
                collect_atom_call_refs(&segment.value, resolution, out);
                if let Some(size) = &segment.size {
                    collect_atom_call_refs(size, resolution, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_call_refs(guard, resolution, out);
                }
                collect_expr_call_refs(&arm.body, resolution, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_call_refs(timeout, resolution, out);
                collect_expr_call_refs(body, resolution, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_expr_call_refs(body, resolution, out);
            collect_expr_call_refs(rest, resolution, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_call_refs(arm, resolution, out);
            }
            if let Some(return_clause) = return_clause {
                collect_handler_arm_call_refs(return_clause, resolution, out);
            }
        }
    }
}

fn collect_atom_call_refs(atom: &Atom, resolution: &ResolutionMap, out: &mut BTreeSet<CallRef>) {
    match atom {
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            for arg in args {
                collect_atom_call_refs(arg, resolution, out);
            }
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_call_refs(atom, resolution, out);
            }
        }
        Atom::Lambda { body, .. } => collect_expr_call_refs(body, resolution, out),
        Atom::BackendSpawnThunk { callback, .. } => {
            collect_atom_call_refs(callback, resolution, out)
        }
        Atom::DictRef { .. } => {
            if let Some(call) = call_ref_for_atom(atom, resolution) {
                out.insert(call);
            }
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

fn collect_handler_call_refs(
    handler: &MHandler,
    resolution: &ResolutionMap,
    out: &mut BTreeSet<CallRef>,
) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_call_refs(arm, resolution, out);
            }
            if let Some(return_clause) = return_clause {
                collect_handler_arm_call_refs(return_clause, resolution, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_call_refs(handler, resolution, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_call_refs(op_tuple, resolution, out);
            if let Some(return_lambda) = return_lambda {
                collect_atom_call_refs(return_lambda, resolution, out);
            }
        }
    }
}

fn collect_handler_arm_call_refs(
    arm: &MHandlerArm,
    resolution: &ResolutionMap,
    out: &mut BTreeSet<CallRef>,
) {
    collect_expr_call_refs(&arm.body, resolution, out);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_call_refs(finally_block, resolution, out);
    }
}

fn call_ref_for_head(atom: &Atom, resolution: &ResolutionMap) -> Option<CallRef> {
    call_ref_for_atom(atom, resolution)
}

fn call_ref_for_atom(atom: &Atom, resolution: &ResolutionMap) -> Option<CallRef> {
    let source = match atom {
        Atom::Var { source, .. }
        | Atom::QualifiedRef { source, .. }
        | Atom::DictRef { source, .. } => *source,
        _ => return None,
    };
    if let Some(symbol) = resolution.get(&source) {
        if !matches!(
            symbol.kind,
            ResolvedCodegenKind::BeamFunction { .. } | ResolvedCodegenKind::ExternalFunction { .. }
        ) {
            return None;
        }
        return Some(CallRef {
            module: symbol.source_module.clone(),
            name: symbol
                .canonical_name
                .rsplit('.')
                .next()
                .unwrap_or(&symbol.name)
                .to_string(),
        });
    }

    match atom {
        Atom::Var { name, .. } => Some(CallRef {
            module: None,
            name: name.name.clone(),
        }),
        Atom::DictRef { name, .. } => Some(CallRef {
            module: None,
            name: name.clone(),
        }),
        Atom::QualifiedRef { module, name, .. } => Some(CallRef {
            module: Some(module.clone()),
            name: name.clone(),
        }),
        _ => None,
    }
}

fn collect_expr_calls(expr: &MExpr, out: &mut BTreeSet<String>) {
    match expr {
        MExpr::App { head, args, .. } => {
            if let Atom::Var { name, .. } = head {
                out.insert(name.name.clone());
            }
            collect_atom_calls(head, out);
            for arg in args {
                collect_atom_calls(arg, out);
            }
        }
        MExpr::Pure(atom)
        | MExpr::Resume { value: atom, .. }
        | MExpr::FieldAccess { record: atom, .. }
        | MExpr::DictMethodAccess { dict: atom, .. }
        | MExpr::UnaryMinus { value: atom, .. } => collect_atom_calls(atom, out),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            for arg in args {
                collect_atom_calls(arg, out);
            }
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            collect_expr_calls(value, out);
            collect_expr_calls(body, out);
        }
        MExpr::Ensure { body, cleanup } => {
            collect_expr_calls(body, out);
            collect_expr_calls(cleanup, out);
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            collect_atom_calls(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_calls(guard, out);
                }
                collect_expr_calls(&arm.body, out);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_atom_calls(cond, out);
            collect_expr_calls(then_branch, out);
            collect_expr_calls(else_branch, out);
        }
        MExpr::With { handler, body, .. } => {
            collect_handler_calls(handler, out);
            collect_expr_calls(body, out);
        }
        MExpr::RecordUpdate { record, fields, .. } => {
            collect_atom_calls(record, out);
            for (_, atom) in fields {
                collect_atom_calls(atom, out);
            }
        }
        MExpr::BinOp { left, right, .. } => {
            collect_atom_calls(left, out);
            collect_atom_calls(right, out);
        }
        MExpr::BitString { segments, .. } => {
            for segment in segments {
                collect_atom_calls(&segment.value, out);
                if let Some(size) = &segment.size {
                    collect_atom_calls(size, out);
                }
            }
        }
        MExpr::Receive { arms, after, .. } => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_calls(guard, out);
                }
                collect_expr_calls(&arm.body, out);
            }
            if let Some((timeout, body)) = after {
                collect_atom_calls(timeout, out);
                collect_expr_calls(body, out);
            }
        }
        MExpr::LetFun { body, rest, .. } => {
            collect_expr_calls(body, out);
            collect_expr_calls(rest, out);
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_calls(arm, out);
            }
            if let Some(return_clause) = return_clause {
                collect_handler_arm_calls(return_clause, out);
            }
        }
    }
}

fn collect_atom_calls(atom: &Atom, out: &mut BTreeSet<String>) {
    match atom {
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
            for arg in args {
                collect_atom_calls(arg, out);
            }
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            for (_, atom) in fields {
                collect_atom_calls(atom, out);
            }
        }
        Atom::Lambda { body, .. } => collect_expr_calls(body, out),
        Atom::BackendSpawnThunk { callback, .. } => collect_atom_calls(callback, out),
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => {}
    }
}

fn collect_handler_calls(handler: &MHandler, out: &mut BTreeSet<String>) {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            for arm in arms {
                collect_handler_arm_calls(arm, out);
            }
            if let Some(return_clause) = return_clause {
                collect_handler_arm_calls(return_clause, out);
            }
        }
        MHandler::Native { .. } => {}
        MHandler::Composite { handlers, .. } => {
            for handler in handlers {
                collect_handler_calls(handler, out);
            }
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            collect_atom_calls(op_tuple, out);
            if let Some(return_lambda) = return_lambda {
                collect_atom_calls(return_lambda, out);
            }
        }
    }
}

fn collect_handler_arm_calls(arm: &MHandlerArm, out: &mut BTreeSet<String>) {
    collect_expr_calls(&arm.body, out);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_calls(finally_block, out);
    }
}

fn write_breakdown(
    f: &mut fmt::Formatter<'_>,
    title: &str,
    before: &BTreeMap<String, usize>,
    after: &BTreeMap<String, usize>,
) -> fmt::Result {
    let keys: BTreeSet<_> = before.keys().chain(after.keys()).collect();
    if keys.is_empty() {
        return Ok(());
    }

    writeln!(f)?;
    writeln!(f, "{title}")?;
    writeln!(
        f,
        "item                              before    after    delta"
    )?;
    writeln!(
        f,
        "----------------------------------------------------------"
    )?;
    for key in keys {
        let before = before.get(key).copied().unwrap_or_default();
        let after = after.get(key).copied().unwrap_or_default();
        writeln!(
            f,
            "{key:<32} {before:>6} {after:>8} {delta:>+8}",
            delta = after as isize - before as isize
        )?;
    }
    Ok(())
}

fn summarize_diff(diff: &StatsDiff) -> String {
    format!(
        "Yield {} -> {}, Bind {} -> {}, decls {} -> {} (source {} -> {}, generated {} -> {})",
        diff.before.yield_,
        diff.after.yield_,
        diff.before.bind,
        diff.after.bind,
        diff.before.decls,
        diff.after.decls,
        diff.before.source_decls,
        diff.after.source_decls,
        diff.before.generated_decls,
        diff.after.generated_decls,
    )
}

fn residual_yield_summary(stats: &Stats, limit: usize) -> Option<String> {
    if stats.yield_ops.is_empty() {
        return None;
    }
    let mut ops = stats
        .yield_ops
        .iter()
        .map(|(op, count)| (op.as_str(), *count))
        .collect::<Vec<_>>();
    ops.sort_by(|(left_op, left_count), (right_op, right_count)| {
        right_count
            .cmp(left_count)
            .then_with(|| left_op.cmp(right_op))
    });
    Some(
        ops.into_iter()
            .take(limit)
            .map(|(op, count)| format!("{op}={count}"))
            .collect::<Vec<_>>()
            .join(", "),
    )
}

fn rows(before: &Stats, after: &Stats) -> [(&'static str, usize, usize); 26] {
    [
        ("decls", before.decls, after.decls),
        ("source decls", before.source_decls, after.source_decls),
        (
            "generated decls",
            before.generated_decls,
            after.generated_decls,
        ),
        ("exprs", before.exprs, after.exprs),
        ("atoms", before.atoms, after.atoms),
        ("Pure", before.pure, after.pure),
        ("Yield", before.yield_, after.yield_),
        ("Bind", before.bind, after.bind),
        ("Let", before.let_, after.let_),
        ("Ensure", before.ensure, after.ensure),
        ("App", before.app, after.app),
        ("ForeignCall", before.foreign_call, after.foreign_call),
        ("With", before.with, after.with),
        ("Resume", before.resume, after.resume),
        ("Case", before.case, after.case),
        ("If", before.if_, after.if_),
        ("Receive", before.receive, after.receive),
        ("LetFun", before.letfun, after.letfun),
        ("HandlerValue", before.handler_value, after.handler_value),
        ("lambda atoms", before.lambda_atoms, after.lambda_atoms),
        ("handler arms", before.handler_arms, after.handler_arms),
        (
            "finally blocks",
            before.finally_blocks,
            after.finally_blocks,
        ),
        (
            "static handlers",
            before.static_handlers,
            after.static_handlers,
        ),
        (
            "native handlers",
            before.native_handlers,
            after.native_handlers,
        ),
        (
            "dynamic handlers",
            before.dynamic_handlers,
            after.dynamic_handlers,
        ),
        (
            "composite handlers",
            before.composite_handlers,
            after.composite_handlers,
        ),
    ]
}

fn decl_is_optimizer_generated(decl: &MDecl) -> bool {
    match decl {
        MDecl::FunBinding(f) => is_optimizer_generated_decl_name(&f.name),
        MDecl::Val(_) | MDecl::DictConstructor(_) | MDecl::Passthrough(_) => false,
    }
}

fn is_optimizer_generated_decl_name(name: &str) -> bool {
    is_generated_variant_name(name)
}

#[cfg(test)]
mod tests {
    use crate::ast::{Lit, NodeId};
    use crate::codegen::monadic::ir::{Atom, BindMode, MDecl, MExpr, MFunBinding, MVar};
    use crate::codegen::resolve::ResolutionMap;
    use crate::token::Span;

    use super::{Stats, StatsDiff, StatsReport};

    fn span() -> Span {
        Span { start: 0, end: 0 }
    }

    fn fun(name: &str, id: u32, body: MExpr) -> MDecl {
        MDecl::FunBinding(MFunBinding {
            id: NodeId(id),
            public: false,
            name: name.to_string(),
            name_span: span(),
            params: vec![],
            guard: None,
            body,
            span: span(),
        })
    }

    fn yield_expr(effect: &str, op: &str, source: u32) -> MExpr {
        MExpr::Yield {
            op: crate::codegen::monadic::ir::EffectOpRef {
                effect: effect.to_string(),
                op: op.to_string(),
                op_index: 1,
            },
            args: vec![],
            source: NodeId(source),
        }
    }

    #[test]
    fn counts_basic_monadic_shapes() {
        let program = vec![MDecl::FunBinding(MFunBinding {
            id: NodeId(1),
            public: false,
            name: "main".into(),
            name_span: span(),
            params: vec![],
            guard: None,
            body: MExpr::Bind {
                var: MVar {
                    name: "x".into(),
                    id: 1,
                },
                value: Box::new(MExpr::Yield {
                    op: crate::codegen::monadic::ir::EffectOpRef {
                        effect: "E".into(),
                        op: "op".into(),
                        op_index: 1,
                    },
                    args: vec![],
                    source: NodeId(2),
                }),
                body: Box::new(MExpr::Pure(Atom::Lit {
                    value: Lit::Unit,
                    source: NodeId(3),
                })),
                mode: BindMode::Sequence,
            },
            span: span(),
        })];

        let stats = Stats::collect_program(&program);

        assert_eq!(stats.decls, 1);
        assert_eq!(stats.source_decls, 1);
        assert_eq!(stats.generated_decls, 0);
        assert_eq!(stats.exprs, 3);
        assert_eq!(stats.bind, 1);
        assert_eq!(stats.yield_, 1);
        assert_eq!(stats.pure, 1);
        assert_eq!(stats.yield_ops.get("E::op"), Some(&1));
    }

    #[test]
    fn counts_optimizer_generated_decls_separately() {
        let source = MDecl::FunBinding(MFunBinding {
            id: NodeId(40),
            public: false,
            name: "worker".into(),
            name_span: span(),
            params: vec![],
            guard: None,
            body: MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: NodeId(41),
            }),
            span: span(),
        });
        let generated = MDecl::FunBinding(MFunBinding {
            id: NodeId(42),
            public: false,
            name: "__saga_native_variant__worker__native_beam_actor".into(),
            name_span: span(),
            params: vec![],
            guard: None,
            body: MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: NodeId(43),
            }),
            span: span(),
        });

        let stats = Stats::collect_program(&vec![source, generated]);

        assert_eq!(stats.decls, 2);
        assert_eq!(stats.source_decls, 1);
        assert_eq!(stats.generated_decls, 1);
    }

    #[test]
    fn reachable_stats_follow_calls_from_entry_roots() {
        let helper = fun("helper", 10, yield_expr("E", "op", 11));
        let unused = fun("unused", 20, yield_expr("Unused", "op", 21));
        let main = fun(
            "main",
            30,
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: "helper".into(),
                        id: 31,
                    },
                    source: NodeId(31),
                },
                args: vec![],
                source: NodeId(32),
            },
        );
        let program = vec![helper, unused, main];

        let stats = Stats::collect_reachable_program(&program, &["main"]);

        assert_eq!(stats.decls, 2);
        assert_eq!(stats.yield_, 1);
        assert_eq!(stats.yield_ops.get("E::op"), Some(&1));
        assert_eq!(stats.yield_ops.get("Unused::op"), None);
    }

    #[test]
    fn whole_app_summary_follows_cross_module_calls() {
        let main_program = vec![fun(
            "main",
            1,
            MExpr::App {
                head: Atom::QualifiedRef {
                    module: "Lib".to_string(),
                    name: "worker".to_string(),
                    source: NodeId(2),
                },
                args: vec![],
                source: NodeId(3),
            },
        )];
        let lib_program = vec![
            fun("worker", 10, yield_expr("E", "op", 11)),
            fun("unused", 20, yield_expr("Unused", "op", 21)),
        ];
        let resolution = ResolutionMap::new();
        let reports = vec![
            (
                "Main".to_string(),
                StatsReport::with_module_graph(
                    StatsDiff::new(
                        Stats::collect_program(&main_program),
                        Stats::collect_program(&main_program),
                    ),
                    None,
                    &main_program,
                    &main_program,
                    &resolution,
                ),
            ),
            (
                "Lib".to_string(),
                StatsReport::with_module_graph(
                    StatsDiff::new(
                        Stats::collect_program(&lib_program),
                        Stats::collect_program(&lib_program),
                    ),
                    None,
                    &lib_program,
                    &lib_program,
                    &resolution,
                ),
            ),
        ];

        let summary = StatsReport::whole_app_summary(&reports, "Main", "main")
            .expect("whole-app summary should be available");

        assert!(summary.contains("whole-app entry-reachable from Main.main"));
        assert!(summary.contains("Yield 1 -> 1"));
        assert!(summary.contains("E::op=1"));
        assert!(!summary.contains("Unused::op"));
    }
}
