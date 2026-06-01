//! Experimental direct-first lowerer for the selective-uniform spike.
//!
//! This module is intentionally incomplete. It lowers only the closed,
//! non-effectful subset needed to inspect direct `/N` function shape. Effects,
//! handlers, lambdas, dictionaries, partial application, and cross-module
//! adaptation should fail loudly here until they are deliberately reintroduced.

use std::collections::{HashMap, HashSet};

use crate::ast::{BinOp as AstBinOp, Lit, NodeId, Pat};
use crate::codegen::CodegenContext;
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use crate::codegen::lower::util::{core_var, lower_lit_atom, mangle_ctor_atom};
use crate::codegen::monadic::ir::{Atom, EffectInfo, MArm, MDecl, MExpr, MFunBinding, MProgram};
use crate::codegen::resolve::{ConstructorAtoms, ResolutionMap, ResolvedCodegenKind};
use crate::codegen::runtime_shape::RuntimeFunctionShape;
use crate::intrinsics::IntrinsicId;

pub fn lower_module(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    effect_info: &EffectInfo<'_>,
) -> CModule {
    let mut lowerer = DirectLowerer::new(resolution, ctors, module_ctx, effect_info);
    lowerer.lower_module(module_name, program)
}

struct DirectLowerer<'a, 'info> {
    resolution: &'a ResolutionMap,
    ctors: &'a ConstructorAtoms,
    module_ctx: &'a CodegenContext,
    effect_info: &'a EffectInfo<'info>,
    current_module: String,
    direct_shapes: HashMap<String, RuntimeFunctionShape>,
    direct_values: HashSet<String>,
    direct_functions: HashSet<String>,
    supporting_fun: Option<String>,
    locals: Vec<HashSet<String>>,
    method_values: Vec<HashSet<String>>,
}

#[derive(Clone)]
struct DirectCallable {
    module: Option<String>,
    name: String,
    arity: usize,
}

impl<'a, 'info> DirectLowerer<'a, 'info> {
    fn new(
        resolution: &'a ResolutionMap,
        ctors: &'a ConstructorAtoms,
        module_ctx: &'a CodegenContext,
        effect_info: &'a EffectInfo<'info>,
    ) -> Self {
        Self {
            resolution,
            ctors,
            module_ctx,
            effect_info,
            current_module: String::new(),
            direct_shapes: HashMap::new(),
            direct_values: HashSet::new(),
            direct_functions: HashSet::new(),
            supporting_fun: None,
            locals: vec![HashSet::new()],
            method_values: vec![HashSet::new()],
        }
    }

    fn lower_module(&mut self, module_name: &str, program: &MProgram) -> CModule {
        self.current_module = module_name.to_string();
        self.classify_program(program);
        self.compute_direct_functions(program);
        self.assert_no_unlowered_direct_functions(program);

        let pub_names: Option<HashSet<String>> =
            self.module_ctx.modules.get(module_name).map(|m| {
                m.codegen_info
                    .exports
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect()
            });
        let is_public =
            |name: &str| -> bool { pub_names.as_ref().is_none_or(|s| s.contains(name)) };

        let mut exports = Vec::new();
        let mut funs = Vec::new();
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    if !self.direct_functions.contains(&fb.name) {
                        continue;
                    }
                    if is_public(&fb.name) {
                        exports.push((fb.name.clone(), fb.params.len()));
                    }
                    funs.push(self.lower_fun_binding(fb));
                }
                MDecl::Val(v) => {
                    if !self.direct_values.contains(&v.name) {
                        continue;
                    }
                    if v.public {
                        exports.push((v.name.clone(), 0));
                    }
                    let body = self.lower_expr(&v.value);
                    funs.push(CFunDef {
                        name: v.name.clone(),
                        arity: 0,
                        body: CExpr::Fun(vec![], Box::new(body)),
                    });
                }
                MDecl::DictConstructor(_) => self.unsupported("dict constructors"),
                MDecl::Passthrough(_) => {}
            }
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }

    fn classify_program(&mut self, program: &MProgram) {
        self.direct_shapes.clear();
        self.direct_values.clear();
        self.direct_functions.clear();
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    let shape = match self.effect_info.fun_effects.get(&fb.name) {
                        Some(effects) if effects.is_empty() => RuntimeFunctionShape::Pure,
                        Some(effects) => {
                            RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                                static_effects: effects.iter().cloned().collect(),
                                is_open_row: false,
                            })
                        }
                        None => {
                            RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                                static_effects: vec![],
                                is_open_row: true,
                            })
                        }
                    };
                    self.direct_shapes.insert(fb.name.clone(), shape);
                }
                MDecl::Val(v) => {
                    if self.expr_is_direct_subset(&v.value) {
                        self.direct_values.insert(v.name.clone());
                    }
                }
                MDecl::DictConstructor(_) | MDecl::Passthrough(_) => {}
            }
        }
    }

    fn compute_direct_functions(&mut self, program: &MProgram) {
        let funs: Vec<&MFunBinding> = program
            .iter()
            .filter_map(|decl| match decl {
                MDecl::FunBinding(fb) => Some(fb),
                _ => None,
            })
            .collect();

        let mut changed = true;
        while changed {
            changed = false;
            for fb in &funs {
                if self.direct_functions.contains(&fb.name) {
                    continue;
                }
                if self.can_lower_fun_binding(fb) {
                    self.direct_functions.insert(fb.name.clone());
                    changed = true;
                }
            }
        }
    }

    fn assert_no_unlowered_direct_functions(&self, program: &MProgram) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if matches!(
                self.direct_shapes.get(&fb.name),
                Some(RuntimeFunctionShape::Pure)
            ) && !self.direct_functions.contains(&fb.name)
            {
                self.unsupported(&format!(
                    "direct function '{}' is outside the current direct subset",
                    fb.name
                ));
            }
        }
    }

    fn can_lower_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if !matches!(
            self.direct_shapes.get(&fb.name),
            Some(RuntimeFunctionShape::Pure)
        ) || fb.guard.is_some()
            || fb.params.iter().any(|p| !direct_param_supported(p))
        {
            return false;
        }

        let prev_supporting = self.supporting_fun.replace(fb.name.clone());
        self.push_scope();
        for pat in &fb.params {
            collect_pat_binders(pat, self.current_scope_mut());
        }
        let supported = self.expr_is_direct_subset(&fb.body);
        self.pop_scope();
        self.supporting_fun = prev_supporting;
        supported
    }

    fn lower_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);
        self.push_scope();
        for pat in &fb.params {
            collect_pat_binders(pat, self.current_scope_mut());
        }
        let body = self.lower_expr(&fb.body);
        self.pop_scope();
        CFunDef {
            name: fb.name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_expr(&mut self, expr: &MExpr) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_atom(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let is_dict_method_value = matches!(value.as_ref(), MExpr::DictMethodAccess { .. });
                let value = self.lower_expr(value);
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if is_dict_method_value {
                    self.current_method_scope_mut().insert(var.name.clone());
                }
                let body = self.lower_expr(body);
                self.pop_scope();
                CExpr::Let(core_var(&var.name), Box::new(value), Box::new(body))
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => CExpr::Case(
                Box::new(self.lower_atom(cond)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: self.lower_expr(then_branch),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_expr(else_branch),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter().map(|arm| self.lower_arm(arm)).collect(),
            ),
            MExpr::App { head, args, .. } => self.lower_app(head, args),
            MExpr::BinOp {
                op, left, right, ..
            } => binop_atoms(op, self.lower_atom(left), self.lower_atom(right)),
            MExpr::UnaryMinus { value, .. } => CExpr::Call(
                "erlang".to_string(),
                "-".to_string(),
                vec![CExpr::Lit(CLit::Int(0)), self.lower_atom(value)],
            ),
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self.lower_field_access(record, field, record_name.as_deref(), anon_fields),
            MExpr::RecordUpdate { .. } | MExpr::ForeignCall { .. } | MExpr::BitString { .. } => {
                self.unsupported_expr(expr)
            }
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => {
                let dict = self.lower_atom(dict);
                CExpr::Call(
                    "erlang".to_string(),
                    "element".to_string(),
                    vec![CExpr::Lit(CLit::Int(*method_index as i64 + 1)), dict],
                )
            }
            MExpr::Yield { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => self.unsupported_expr(expr),
        }
    }

    fn lower_arm(&mut self, arm: &MArm) -> CArm {
        self.push_scope();
        collect_pat_binders(&arm.pattern, self.current_scope_mut());
        let body = self.lower_expr(&arm.body);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }

    fn lower_field_access(
        &mut self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        anon_fields: &Option<Vec<String>>,
    ) -> CExpr {
        let order = self.record_field_order(record_name, anon_fields.as_deref());
        let index = order
            .iter()
            .position(|candidate| candidate == field)
            .unwrap_or_else(|| {
                panic!(
                    "selective-uniform direct lowerer TODO: field '{}' not found in {:?}",
                    field, order
                )
            }) as i64
            + 2;
        CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(index)), self.lower_atom(record)],
        )
    }

    fn record_field_order(
        &self,
        record_name: Option<&str>,
        anon_fields: Option<&[String]>,
    ) -> Vec<String> {
        if let Some(fields) = anon_fields {
            return fields.to_vec();
        }
        let Some(name) = record_name else {
            self.unsupported("field access without record field metadata");
        };
        self.effect_info
            .records
            .get(name)
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info.records.get(bare)
            })
            .map(|info| info.fields.iter().map(|(field, _)| field.clone()).collect())
            .unwrap_or_else(|| {
                panic!(
                    "selective-uniform direct lowerer TODO: unknown record '{}'",
                    name
                )
            })
    }

    fn lower_app(&mut self, head: &Atom, args: &[Atom]) -> CExpr {
        if let Some(intrinsic) = self.direct_intrinsic(head) {
            return self.lower_intrinsic_app(intrinsic, args);
        }
        if let Some(dict) = self.direct_dict_constructor(head) {
            if args.len() != dict.arity {
                self.unsupported(&format!(
                    "partial/oversaturated dict constructor '{}' with {} args; expected {}",
                    dict.name,
                    args.len(),
                    dict.arity
                ));
            }
            return self.apply_direct_callable(dict, args);
        }
        if let Some(callable) = self.same_module_direct_callable(head) {
            if args.len() != callable.arity {
                self.unsupported(&format!(
                    "partial/oversaturated direct call to '{}' with {} args; expected {}",
                    callable.name,
                    args.len(),
                    callable.arity
                ));
            }
            return self.apply_direct_callable(callable, args);
        }
        if let Atom::Var { name, .. } = head
            && self.is_method_value(&name.name)
        {
            return CExpr::Apply(
                Box::new(CExpr::Var(core_var(&name.name))),
                args.iter().map(|arg| self.lower_atom(arg)).collect(),
            );
        }
        self.unsupported_expr(&MExpr::App {
            head: head.clone(),
            args: args.to_vec(),
            source: NodeId::fresh(),
        })
    }

    fn apply_direct_callable(&mut self, callable: DirectCallable, args: &[Atom]) -> CExpr {
        let lowered_args = args.iter().map(|arg| self.lower_atom(arg)).collect();
        match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        }
    }

    fn direct_intrinsic(&self, head: &Atom) -> Option<IntrinsicId> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::Intrinsic { id, .. } = resolved.kind else {
            return None;
        };
        Some(id)
    }

    fn lower_intrinsic_app(&mut self, intrinsic: IntrinsicId, args: &[Atom]) -> CExpr {
        match intrinsic {
            IntrinsicId::PrintStdout => self.lower_print_intrinsic(args, false),
            IntrinsicId::PrintStderr => self.lower_print_intrinsic(args, true),
            IntrinsicId::Dbg => self.lower_dbg_intrinsic(args),
            IntrinsicId::CatchPanic => {
                self.unsupported("intrinsic outside the current direct subset")
            }
        }
    }

    fn lower_print_intrinsic(&mut self, args: &[Atom], stderr: bool) -> CExpr {
        if args.len() != 1 {
            self.unsupported(&format!(
                "print intrinsic with {} args; expected 1",
                args.len()
            ));
        }
        let mut fmt_args = vec![
            CExpr::Lit(CLit::Str("~ts".to_string())),
            CExpr::Cons(Box::new(self.lower_atom(&args[0])), Box::new(CExpr::Nil)),
        ];
        if stderr {
            fmt_args.insert(0, CExpr::Lit(CLit::Atom("standard_error".to_string())));
        }
        CExpr::Let(
            "_PrintResult".to_string(),
            Box::new(CExpr::Call(
                "io".to_string(),
                "format".to_string(),
                fmt_args,
            )),
            Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
        )
    }

    fn lower_dbg_intrinsic(&mut self, args: &[Atom]) -> CExpr {
        if args.len() != 2 {
            self.unsupported(&format!(
                "dbg intrinsic with {} args; expected 2",
                args.len()
            ));
        }
        let debug_fn_var = "_DebugFn".to_string();
        let str_var = "_DebugStr".to_string();
        let print_result_var = "_DebugPrintResult".to_string();
        let extract = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(1)), self.lower_atom(&args[0])],
        );
        let debug_call = CExpr::Apply(
            Box::new(CExpr::Var(debug_fn_var.clone())),
            vec![self.lower_atom(&args[1])],
        );
        let print = CExpr::Call(
            "io".to_string(),
            "format".to_string(),
            vec![
                CExpr::Lit(CLit::Atom("standard_error".to_string())),
                CExpr::Lit(CLit::Str("~ts~n".to_string())),
                CExpr::Cons(Box::new(CExpr::Var(str_var.clone())), Box::new(CExpr::Nil)),
            ],
        );
        CExpr::Let(
            debug_fn_var,
            Box::new(extract),
            Box::new(CExpr::Let(
                str_var,
                Box::new(debug_call),
                Box::new(CExpr::Let(
                    print_result_var,
                    Box::new(print),
                    Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
                )),
            )),
        )
    }

    fn direct_dict_constructor(&self, head: &Atom) -> Option<DirectCallable> {
        let source = match head {
            Atom::DictRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        if !effects.is_empty() {
            return None;
        }
        Some(DirectCallable {
            module: erlang_mod.clone(),
            name: name.clone(),
            arity: *arity,
        })
    }

    fn same_module_direct_callable(&self, head: &Atom) -> Option<DirectCallable> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        if !effects.is_empty() {
            return None;
        }
        if erlang_mod
            .as_ref()
            .is_some_and(|module| module != &self.current_module)
        {
            return None;
        }
        if !self.direct_functions.contains(name) {
            return None;
        }
        let shape = self.direct_shapes.get(name)?;
        if !matches!(shape, RuntimeFunctionShape::Pure) {
            return None;
        }
        if shape.expanded_arity(*arity) != *arity {
            return None;
        }
        Some(DirectCallable {
            module: None,
            name: name.clone(),
            arity: *arity,
        })
    }

    fn same_module_function_ref(&self, head: &Atom) -> Option<DirectCallable> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        if !effects.is_empty() {
            return None;
        }
        if erlang_mod
            .as_ref()
            .is_some_and(|module| module != &self.current_module)
        {
            return None;
        }
        let shape = self.direct_shapes.get(name)?;
        if !matches!(shape, RuntimeFunctionShape::Pure) {
            return None;
        }
        if shape.expanded_arity(*arity) != *arity {
            return None;
        }
        Some(DirectCallable {
            module: None,
            name: name.clone(),
            arity: *arity,
        })
    }

    fn supported_direct_call(&self, head: &Atom) -> Option<DirectCallable> {
        let callable = self.same_module_function_ref(head)?;
        let recursive_self = self
            .supporting_fun
            .as_ref()
            .is_some_and(|current| current == &callable.name);
        if recursive_self || self.direct_functions.contains(&callable.name) {
            Some(callable)
        } else {
            None
        }
    }

    fn lower_atom(&mut self, atom: &Atom) -> CExpr {
        match atom {
            Atom::Var { name, source } => {
                if self.is_local(&name.name) {
                    CExpr::Var(core_var(&name.name))
                } else if let Some(callable) = self.same_module_direct_callable(atom) {
                    let resolved = self
                        .resolution
                        .get(source)
                        .expect("resolved direct function");
                    debug_assert_eq!(resolved.name, callable.name);
                    CExpr::FunRef(callable.name, callable.arity)
                } else if self.direct_values.contains(&name.name) {
                    CExpr::Apply(Box::new(CExpr::FunRef(name.name.clone(), 0)), vec![])
                } else {
                    self.unsupported(&format!("non-local atom '{}'", name.name))
                }
            }
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Ctor { name, args, .. } => self.lower_ctor_atom(name, args),
            Atom::Tuple { elements, .. } => {
                CExpr::Tuple(elements.iter().map(|arg| self.lower_atom(arg)).collect())
            }
            Atom::AnonRecord { fields, .. } => self.lower_anon_record_atom(fields),
            Atom::Record { name, fields, .. } => self.lower_record_atom(name, fields),
            Atom::Symbol { symbol, .. } => {
                crate::codegen::lower::util::lower_string_to_binary(symbol)
            }
            Atom::QualifiedRef { .. }
            | Atom::DictRef { .. }
            | Atom::Lambda { .. }
            | Atom::BackendAtom { .. }
            | Atom::BackendSpawnThunk { .. } => self.unsupported_atom(atom),
        }
    }

    fn lower_ctor_atom(&mut self, name: &str, args: &[Atom]) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            return CExpr::Cons(
                Box::new(self.lower_atom(&args[0])),
                Box::new(self.lower_atom(&args[1])),
            );
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(args.iter().map(|arg| self.lower_atom(arg)));
        CExpr::Tuple(elems)
    }

    fn lower_anon_record_atom(&mut self, fields: &[(String, Atom)]) -> CExpr {
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(sorted.into_iter().map(|(_, atom)| self.lower_atom(atom)));
        CExpr::Tuple(elems)
    }

    fn lower_record_atom(&mut self, name: &str, fields: &[(String, Atom)]) -> CExpr {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(fields.iter().map(|(_, atom)| self.lower_atom(atom)));
        CExpr::Tuple(elems)
    }

    fn lower_pat(&self, pat: &Pat) -> CPat {
        match pat {
            Pat::Wildcard { .. } => CPat::Wildcard,
            Pat::Var { name, .. } => CPat::Var(core_var(name)),
            Pat::Lit { value, .. } => match value {
                Lit::String(s, _) => CPat::Lit(CLit::Str(s.clone())),
                _ => CPat::Lit(lower_lit_pat(value)),
            },
            Pat::Tuple { elements, .. } => {
                CPat::Tuple(elements.iter().map(|p| self.lower_pat(p)).collect())
            }
            _ => self.unsupported("patterns beyond var/lit/tuple"),
        }
    }

    fn is_local(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|scope| scope.contains(name))
    }

    fn is_method_value(&self, name: &str) -> bool {
        self.method_values
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
    }

    fn push_scope(&mut self) {
        self.locals.push(HashSet::new());
        self.method_values.push(HashSet::new());
    }

    fn pop_scope(&mut self) {
        self.locals.pop();
        self.method_values.pop();
    }

    fn current_scope_mut(&mut self) -> &mut HashSet<String> {
        self.locals.last_mut().expect("direct lowerer has a scope")
    }

    fn current_method_scope_mut(&mut self) -> &mut HashSet<String> {
        self.method_values
            .last_mut()
            .expect("direct lowerer has a method-value scope")
    }

    fn expr_is_direct_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => self.atom_is_direct_subset(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let is_dict_method_value = matches!(value.as_ref(), MExpr::DictMethodAccess { .. });
                if !self.expr_is_direct_subset(value) {
                    return false;
                }
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if is_dict_method_value {
                    self.current_method_scope_mut().insert(var.name.clone());
                }
                let supported = self.expr_is_direct_subset(body);
                self.pop_scope();
                supported
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.expr_is_direct_subset(then_branch)
                    && self.expr_is_direct_subset(else_branch)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    self.push_scope();
                    collect_pat_binders(&arm.pattern, self.current_scope_mut());
                    let supported = self.expr_is_direct_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::App { head, args, .. } => {
                let direct_call_supported = self
                    .supported_direct_call(head)
                    .is_some_and(|callable| callable.arity == args.len())
                    || self
                        .direct_dict_constructor(head)
                        .is_some_and(|callable| callable.arity == args.len())
                    || self
                        .direct_intrinsic(head)
                        .is_some_and(|intrinsic| match intrinsic {
                            IntrinsicId::PrintStdout | IntrinsicId::PrintStderr => args.len() == 1,
                            IntrinsicId::Dbg => args.len() == 2,
                            IntrinsicId::CatchPanic => false,
                        })
                    || matches!(head, Atom::Var { name, .. } if self.is_method_value(&name.name));
                direct_call_supported && args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            MExpr::BinOp { left, right, .. } => {
                self.atom_is_direct_subset(left) && self.atom_is_direct_subset(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_is_direct_subset(value),
            MExpr::FieldAccess { record, .. } => self.atom_is_direct_subset(record),
            MExpr::RecordUpdate { .. }
            | MExpr::ForeignCall { .. }
            | MExpr::BitString { .. }
            | MExpr::Yield { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
            MExpr::DictMethodAccess { dict, .. } => self.atom_is_direct_subset(dict),
        }
    }

    fn atom_is_direct_subset(&self, atom: &Atom) -> bool {
        match atom {
            Atom::Var { name, .. } => {
                self.is_local(&name.name)
                    || self.direct_values.contains(&name.name)
                    || self.supported_direct_call(atom).is_some()
            }
            Atom::Lit { .. } | Atom::Symbol { .. } => true,
            Atom::Ctor { args, .. } => args.iter().all(|arg| self.atom_is_direct_subset(arg)),
            Atom::Tuple { elements, .. } => {
                elements.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .all(|(_, arg)| self.atom_is_direct_subset(arg)),
            Atom::QualifiedRef { .. }
            | Atom::Lambda { .. }
            | Atom::BackendAtom { .. }
            | Atom::BackendSpawnThunk { .. } => false,
            Atom::DictRef { .. } => self.direct_dict_constructor(atom).is_some(),
        }
    }

    fn unsupported(&self, what: &str) -> ! {
        panic!("selective-uniform direct lowerer TODO: {what}")
    }

    fn unsupported_expr(&self, expr: &MExpr) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO: unsupported MExpr {:?}",
            std::mem::discriminant(expr)
        )
    }

    fn unsupported_atom(&self, atom: &Atom) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO: unsupported Atom {:?}",
            std::mem::discriminant(atom)
        )
    }
}

fn lower_param_names(params: &[Pat]) -> Vec<String> {
    params
        .iter()
        .enumerate()
        .map(|(i, pat)| match pat {
            Pat::Var { name, .. } => core_var(name),
            Pat::Lit {
                value: Lit::Unit, ..
            } => format!("_Arg{i}"),
            _ => format!("_Arg{i}"),
        })
        .collect()
}

fn direct_param_supported(pat: &Pat) -> bool {
    matches!(
        pat,
        Pat::Var { .. }
            | Pat::Lit {
                value: Lit::Unit,
                ..
            }
    )
}

fn collect_pat_binders(pat: &Pat, out: &mut HashSet<String>) {
    match pat {
        Pat::Var { name, .. } => {
            out.insert(name.clone());
        }
        Pat::Tuple { elements, .. } => {
            for pat in elements {
                collect_pat_binders(pat, out);
            }
        }
        _ => {}
    }
}

fn binop_atoms(op: &AstBinOp, l: CExpr, r: CExpr) -> CExpr {
    use AstBinOp::*;
    let call = |name: &str| {
        CExpr::Call(
            "erlang".to_string(),
            name.to_string(),
            vec![l.clone(), r.clone()],
        )
    };
    match op {
        Add => call("+"),
        Sub => call("-"),
        Mul => call("*"),
        FloatDiv => call("/"),
        IntDiv => call("div"),
        Mod => call("rem"),
        FloatMod => CExpr::Call("math".to_string(), "fmod".to_string(), vec![l, r]),
        Eq => call("=:="),
        NotEq => call("=/="),
        Lt => call("<"),
        Gt => call(">"),
        LtEq => call("=<"),
        GtEq => call(">="),
        Concat => CExpr::Binary(vec![
            crate::codegen::cerl::CBinSeg::BinaryAll(l),
            crate::codegen::cerl::CBinSeg::BinaryAll(r),
        ]),
        And => call("and"),
        Or => call("or"),
    }
}

fn lower_lit_pat(lit: &Lit) -> CLit {
    match lit {
        Lit::Int(_, value) => CLit::Int(*value),
        Lit::Float(_, value) => CLit::Float(*value),
        Lit::String(value, _) => CLit::Str(value.clone()),
        Lit::Bool(value) => CLit::Atom(value.to_string()),
        Lit::Unit => CLit::Atom("unit".to_string()),
    }
}
