//! Lightweight structural counters for monadic IR inspection.
//!
//! These numbers are diagnostics only. They are useful for seeing whether an
//! optimizer pass removed `Yield`/`Bind` scaffolding or introduced direct
//! `ForeignCall`s, but they are not a semantic metric.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::codegen::monadic::ir::{Atom, MArm, MDecl, MExpr, MHandler, MHandlerArm, MProgram};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Stats {
    pub decls: usize,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatsReport {
    whole: StatsDiff,
    reachable: Option<StatsDiff>,
}

impl StatsReport {
    pub fn new(whole: StatsDiff, reachable: Option<StatsDiff>) -> Self {
        Self { whole, reachable }
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

fn rows(before: &Stats, after: &Stats) -> [(&'static str, usize, usize); 24] {
    [
        ("decls", before.decls, after.decls),
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

#[cfg(test)]
mod tests {
    use crate::ast::{Lit, NodeId};
    use crate::codegen::monadic::ir::{Atom, BindMode, MDecl, MExpr, MFunBinding, MVar};
    use crate::token::Span;

    use super::Stats;

    fn span() -> Span {
        Span { start: 0, end: 0 }
    }

    #[test]
    fn counts_basic_monadic_shapes() {
        let program = vec![MDecl::FunBinding(MFunBinding {
            id: NodeId(1),
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
        assert_eq!(stats.exprs, 3);
        assert_eq!(stats.bind, 1);
        assert_eq!(stats.yield_, 1);
        assert_eq!(stats.pure, 1);
        assert_eq!(stats.yield_ops.get("E::op"), Some(&1));
    }

    #[test]
    fn reachable_stats_follow_calls_from_entry_roots() {
        let helper = MDecl::FunBinding(MFunBinding {
            id: NodeId(10),
            name: "helper".into(),
            name_span: span(),
            params: vec![],
            guard: None,
            body: MExpr::Yield {
                op: crate::codegen::monadic::ir::EffectOpRef {
                    effect: "E".into(),
                    op: "op".into(),
                    op_index: 1,
                },
                args: vec![],
                source: NodeId(11),
            },
            span: span(),
        });
        let unused = MDecl::FunBinding(MFunBinding {
            id: NodeId(20),
            name: "unused".into(),
            name_span: span(),
            params: vec![],
            guard: None,
            body: MExpr::Yield {
                op: crate::codegen::monadic::ir::EffectOpRef {
                    effect: "Unused".into(),
                    op: "op".into(),
                    op_index: 1,
                },
                args: vec![],
                source: NodeId(21),
            },
            span: span(),
        });
        let main = MDecl::FunBinding(MFunBinding {
            id: NodeId(30),
            name: "main".into(),
            name_span: span(),
            params: vec![],
            guard: None,
            body: MExpr::App {
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
            span: span(),
        });
        let program = vec![helper, unused, main];

        let stats = Stats::collect_reachable_program(&program, &["main"]);

        assert_eq!(stats.decls, 2);
        assert_eq!(stats.yield_, 1);
        assert_eq!(stats.yield_ops.get("E::op"), Some(&1));
        assert_eq!(stats.yield_ops.get("Unused::op"), None);
    }
}
