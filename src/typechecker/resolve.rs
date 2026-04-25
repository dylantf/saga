//! Front-end name resolution: records semantic identity for source AST nodes
//! without rewriting source spelling in place.
//!
//! Runs after imports are processed (scope_map is complete), before inference.
//! The output is an authoritative `ResolutionResult` keyed by source identity.

use std::collections::{HashMap, HashSet};

use super::ScopeMap;
use crate::ast::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalBindingId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedValue {
    Local {
        binding_id: LocalBindingId,
        name: String,
    },
    Global {
        /// Exact lookup key to use in the checker env/constructor/handler maps.
        lookup_name: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedEffectOp {
    pub effect: String,
    pub op: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedTraitMethod {
    pub trait_name: String,
    pub method: String,
}

#[derive(Debug, Clone, Default)]
pub struct ResolutionResult {
    pub values: HashMap<NodeId, ResolvedValue>,
    pub constructors: HashMap<NodeId, String>,
    pub record_types: HashMap<NodeId, String>,
    pub types: HashMap<NodeId, String>,
    pub traits: HashMap<NodeId, String>,
    pub impl_traits: HashMap<NodeId, String>,
    pub impl_target_types: HashMap<NodeId, String>,
    pub effects: HashMap<NodeId, String>,
    pub handlers: HashMap<NodeId, ResolvedValue>,
    pub effect_calls: HashMap<NodeId, ResolvedEffectOp>,
    pub handler_arms: HashMap<NodeId, ResolvedEffectOp>,
    pub trait_methods: HashMap<NodeId, ResolvedTraitMethod>,
}

impl ResolutionResult {
    pub fn value(&self, node_id: NodeId) -> Option<&ResolvedValue> {
        self.values.get(&node_id)
    }

    pub fn constructor(&self, node_id: NodeId) -> Option<&str> {
        self.constructors.get(&node_id).map(|s| s.as_str())
    }

    pub fn record_type(&self, node_id: NodeId) -> Option<&str> {
        self.record_types.get(&node_id).map(|s| s.as_str())
    }

    pub fn type_ref(&self, id: NodeId) -> Option<&str> {
        self.types.get(&id).map(|s| s.as_str())
    }

    pub fn trait_ref(&self, id: NodeId) -> Option<&str> {
        self.traits.get(&id).map(|s| s.as_str())
    }

    pub fn impl_trait_ref(&self, node_id: NodeId) -> Option<&str> {
        self.impl_traits.get(&node_id).map(|s| s.as_str())
    }

    pub fn impl_target_type_ref(&self, node_id: NodeId) -> Option<&str> {
        self.impl_target_types.get(&node_id).map(|s| s.as_str())
    }

    pub fn effect_ref(&self, id: NodeId) -> Option<&str> {
        self.effects.get(&id).map(|s| s.as_str())
    }

    pub fn handler_ref(&self, node_id: NodeId) -> Option<&ResolvedValue> {
        self.handlers.get(&node_id)
    }

    pub fn effect_call(&self, node_id: NodeId) -> Option<&ResolvedEffectOp> {
        self.effect_calls.get(&node_id)
    }

    pub fn handler_arm(&self, node_id: NodeId) -> Option<&ResolvedEffectOp> {
        self.handler_arms.get(&node_id)
    }

    pub fn trait_method(&self, node_id: NodeId) -> Option<&ResolvedTraitMethod> {
        self.trait_methods.get(&node_id)
    }
}

#[derive(Default)]
struct LocalModuleNames {
    top_level_values: HashSet<String>,
    constructors: HashSet<String>,
    types: HashMap<String, String>,
    traits: HashMap<String, String>,
    effects: HashMap<String, String>,
    effect_ops: HashMap<String, HashSet<String>>,
    /// Bare trait method name -> canonical traits in the current module that
    /// expose that method. Trait methods are no longer treated as ordinary
    /// top-level values: their visibility tracks their owning trait.
    trait_methods: HashMap<String, HashSet<String>>,
    handlers: HashSet<String>,
}

impl LocalModuleNames {
    fn collect(program: &[Decl], current_module: Option<&str>) -> Self {
        let mut out = Self::default();

        let qualify = |name: &str| -> String {
            current_module
                .map(|m| format!("{}.{}", m, name))
                .unwrap_or_else(|| name.to_string())
        };

        for decl in program {
            match decl {
                Decl::FunBinding { name, .. }
                | Decl::FunSignature { name, .. }
                | Decl::Val { name, .. }
                | Decl::Let { name, .. } => {
                    out.top_level_values.insert(name.clone());
                }
                Decl::TraitDef { name, methods, .. } => {
                    let canonical = qualify(name);
                    out.traits.insert(name.clone(), canonical.clone());
                    for method in methods {
                        out.trait_methods
                            .entry(method.node.name.clone())
                            .or_default()
                            .insert(canonical.clone());
                    }
                }
                Decl::TypeDef { name, variants, .. } => {
                    out.types.insert(name.clone(), qualify(name));
                    for variant in variants {
                        out.constructors.insert(variant.node.name.clone());
                    }
                }
                Decl::RecordDef { name, .. } => {
                    out.types.insert(name.clone(), qualify(name));
                    out.constructors.insert(name.clone());
                }
                Decl::EffectDef {
                    name, operations, ..
                } => {
                    let canonical = qualify(name);
                    out.effects.insert(name.clone(), canonical.clone());
                    for op in operations {
                        out.effect_ops
                            .entry(op.node.name.clone())
                            .or_default()
                            .insert(canonical.clone());
                    }
                }
                Decl::HandlerDef { name, .. } => {
                    out.handlers.insert(name.clone());
                    out.top_level_values.insert(name.clone());
                }
                _ => {}
            }
        }

        out
    }
}

struct Resolver<'a> {
    scope: &'a ScopeMap,
    locals: LocalModuleNames,
    result: ResolutionResult,
    value_scopes: Vec<HashMap<String, ResolvedValue>>,
    next_binding_id: u32,
}

impl<'a> Resolver<'a> {
    fn new(scope: &'a ScopeMap, locals: LocalModuleNames) -> Self {
        Self {
            scope,
            locals,
            result: ResolutionResult::default(),
            value_scopes: Vec::new(),
            next_binding_id: 0,
        }
    }

    fn into_result(self) -> ResolutionResult {
        self.result
    }

    fn push_value_scope(&mut self) {
        self.value_scopes.push(HashMap::new());
    }

    fn pop_value_scope(&mut self) {
        self.value_scopes.pop();
    }

    fn bind_local_name(&mut self, name: String) {
        let binding = ResolvedValue::Local {
            binding_id: LocalBindingId(self.next_binding_id),
            name: name.clone(),
        };
        self.next_binding_id += 1;
        if let Some(scope) = self.value_scopes.last_mut() {
            scope.insert(name, binding);
        }
    }

    fn bind_pattern(&mut self, pat: &Pat) {
        match pat {
            Pat::Wildcard { .. } | Pat::Lit { .. } => {}
            Pat::Var { name, .. } => self.bind_local_name(name.clone()),
            Pat::Constructor { args, .. } => {
                for arg in args {
                    self.bind_pattern(arg);
                }
            }
            Pat::Record {
                fields, as_name, ..
            } => {
                for (field_name, alias) in fields {
                    if let Some(pat) = alias {
                        self.bind_pattern(pat);
                    } else {
                        self.bind_local_name(field_name.clone());
                    }
                }
                if let Some(name) = as_name {
                    self.bind_local_name(name.clone());
                }
            }
            Pat::AnonRecord { fields, .. } => {
                for (field_name, alias) in fields {
                    if let Some(pat) = alias {
                        self.bind_pattern(pat);
                    } else {
                        self.bind_local_name(field_name.clone());
                    }
                }
            }
            Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
                for pat in elements {
                    self.bind_pattern(pat);
                }
            }
            Pat::StringPrefix { rest, .. } => self.bind_pattern(rest),
            Pat::BitStringPat { segments, .. } => {
                for seg in segments {
                    self.bind_pattern(&seg.value);
                }
            }
            Pat::ConsPat { head, tail, .. } => {
                self.bind_pattern(head);
                self.bind_pattern(tail);
            }
            Pat::Or { patterns, .. } => {
                if let Some(first) = patterns.first() {
                    self.bind_pattern(first);
                }
            }
        }
    }

    fn is_locally_bound(&self, name: &str) -> bool {
        self.value_scopes
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
    }

    fn resolve_value_name(&self, name: &str) -> Option<ResolvedValue> {
        for scope in self.value_scopes.iter().rev() {
            if let Some(resolved) = scope.get(name) {
                return Some(resolved.clone());
            }
        }
        if let Some(canonical_trait) = self.resolve_bare_trait_method_name(name) {
            return Some(ResolvedValue::Global {
                lookup_name: super::canonical_join(&canonical_trait, name),
            });
        }
        if self.locals.top_level_values.contains(name) {
            return Some(ResolvedValue::Global {
                lookup_name: name.to_string(),
            });
        }
        self.scope
            .resolve_value(name)
            .map(|lookup_name| ResolvedValue::Global {
                lookup_name: lookup_name.to_string(),
            })
    }

    /// Resolve a bare trait method name to its canonical trait when exactly
    /// one trait contributes that method into scope. Locally defined traits
    /// shadow imports — matches typical name resolution rules and lets test
    /// fixtures redefine `Show`, `Eq`, etc. without colliding with the
    /// prelude. Imports are consulted only when the current module has no
    /// local trait contributing the method. Returns None for "no candidate"
    /// and ">1 candidate within the chosen tier" so the typechecker can
    /// produce a single diagnostic.
    fn resolve_bare_trait_method_name(&self, method_name: &str) -> Option<String> {
        if let Some(local_traits) = self.locals.trait_methods.get(method_name) {
            if local_traits.len() == 1 {
                return local_traits.iter().next().cloned();
            }
            return None;
        }
        if let Some(imported_traits) = self.scope.trait_methods.get(method_name)
            && imported_traits.len() == 1
        {
            return imported_traits.iter().next().cloned();
        }
        None
    }

    fn resolve_handler_name(&self, name: &str) -> Option<ResolvedValue> {
        if let Some(local) = self.resolve_value_name(name) {
            return Some(local);
        }
        if self.locals.handlers.contains(name) {
            return Some(ResolvedValue::Global {
                lookup_name: name.to_string(),
            });
        }
        self.scope
            .resolve_handler(name)
            .map(|lookup_name| ResolvedValue::Global {
                lookup_name: lookup_name.to_string(),
            })
    }

    fn resolve_constructor_name(&self, name: &str) -> Option<String> {
        if self.locals.constructors.contains(name) {
            return Some(name.to_string());
        }
        self.scope.resolve_constructor(name).map(|s| s.to_string())
    }

    fn resolve_type_name(&self, name: &str) -> Option<String> {
        if let Some(local) = self.locals.types.get(name) {
            return Some(local.clone());
        }
        if let Some(imported) = self.scope.resolve_type(name) {
            return Some(imported.to_string());
        }
        let builtin = super::canonicalize_type_name(name);
        if builtin != name || super::is_builtin_canonical(name) || name.contains('.') {
            return Some(builtin.to_string());
        }
        None
    }

    fn resolve_trait_name(&self, name: &str) -> Option<String> {
        if let Some(local) = self.locals.traits.get(name) {
            return Some(local.clone());
        }
        if let Some(imported) = self.scope.resolve_trait(name) {
            return Some(imported.to_string());
        }
        match name {
            "Num" | "Eq" => Some(name.to_string()),
            _ if name.contains('.') => Some(name.to_string()),
            _ => None,
        }
    }

    fn resolve_effect_name(&self, name: &str) -> Option<String> {
        if let Some(local) = self.locals.effects.get(name) {
            return Some(local.clone());
        }
        self.scope
            .resolve_effect(name)
            .map(|s| s.to_string())
            .or_else(|| name.contains('.').then(|| name.to_string()))
    }

    /// Resolve a bare effect op name to its canonical effect using
    /// tier-based shadowing: locally defined effects shadow imports. Within
    /// whichever tier wins, return Some only when there is exactly one
    /// candidate. None for "no candidate" and "ambiguous within the chosen
    /// tier" — the typechecker's [`Checker::lookup_effect_op`] re-derives
    /// the same tiers from `current_module` + `scope_map.effect_ops` to
    /// emit the proper Missing/Ambiguous diagnostic.
    fn resolve_bare_effect_op_name(&self, op_name: &str) -> Option<String> {
        if let Some(local_effects) = self.locals.effect_ops.get(op_name) {
            if local_effects.len() == 1 {
                return local_effects.iter().next().cloned();
            }
            return None;
        }
        if let Some(imported_effects) = self.scope.effect_ops.get(op_name)
            && imported_effects.len() == 1
        {
            return imported_effects.iter().next().cloned();
        }
        None
    }

    /// Decompose a canonical method-style lookup name (`Module.Trait.method`
    /// or `Trait.method`) and check whether the trait part names a known
    /// trait — locally defined or imported (regardless of exposing, since
    /// qualified access doesn't depend on bare visibility). Returns a
    /// `ResolvedTraitMethod` for the elaborator to dispatch on so qualified
    /// calls like `Module.Trait.method` get the same dictionary-method
    /// access path that bare unambiguous trait method calls do.
    fn qualified_trait_method(&self, canonical: &str) -> Option<ResolvedTraitMethod> {
        let (trait_canonical, method) = canonical.rsplit_once('.')?;
        let known_local = self
            .locals
            .traits
            .values()
            .any(|c| c == trait_canonical);
        let known_imported = self
            .scope
            .traits
            .values()
            .any(|c| c == trait_canonical);
        if !(known_local || known_imported) {
            return None;
        }
        Some(ResolvedTraitMethod {
            trait_name: trait_canonical.to_string(),
            method: method.to_string(),
        })
    }

    fn resolve_effect_op_name(
        &self,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Option<ResolvedEffectOp> {
        let effect = if let Some(qualifier) = qualifier {
            self.resolve_effect_name(qualifier)?
        } else {
            self.resolve_bare_effect_op_name(op_name)?
        };
        Some(ResolvedEffectOp {
            effect,
            op: op_name.to_string(),
        })
    }

    fn record_type_ref(&mut self, id: NodeId, name: &str) {
        if let Some(resolved) = self.resolve_type_name(name) {
            self.result.types.insert(id, resolved);
        }
    }

    fn record_trait_ref(&mut self, id: NodeId, name: &str) {
        if let Some(resolved) = self.resolve_trait_name(name) {
            self.result.traits.insert(id, resolved);
        }
    }

    fn record_effect_ref(&mut self, effect_ref: &EffectRef) {
        if let Some(resolved) = self.resolve_effect_name(&effect_ref.name) {
            self.result.effects.insert(effect_ref.id, resolved);
        }
        for arg in &effect_ref.type_args {
            self.resolve_type_expr(arg);
        }
    }

    fn resolve_where_clause(&mut self, where_clause: &[TraitBound]) {
        for bound in where_clause {
            for tr in &bound.traits {
                self.record_trait_ref(tr.id, &tr.name);
                for arg in &tr.type_args {
                    self.resolve_type_expr(arg);
                }
            }
        }
    }

    fn resolve_type_expr(&mut self, texpr: &TypeExpr) {
        match texpr {
            TypeExpr::Named { id, name, .. } => self.record_type_ref(*id, name),
            TypeExpr::Var { .. } => {}
            TypeExpr::App { func, arg, .. } => {
                self.resolve_type_expr(func);
                self.resolve_type_expr(arg);
            }
            TypeExpr::Arrow {
                from, to, effects, ..
            } => {
                self.resolve_type_expr(from);
                self.resolve_type_expr(to);
                for effect_ref in effects {
                    self.record_effect_ref(effect_ref);
                }
            }
            TypeExpr::Record { fields, .. } => {
                for (_, field_ty) in fields {
                    self.resolve_type_expr(field_ty);
                }
            }
            TypeExpr::Labeled { inner, .. } => self.resolve_type_expr(inner),
        }
    }

    fn resolve_exprs(&mut self, exprs: &[Expr]) {
        for expr in exprs {
            self.resolve_expr(expr);
        }
    }

    fn resolve_scoped_pattern_body(&mut self, pattern: &Pat, guard: Option<&Expr>, body: &Expr) {
        self.resolve_pat(pattern);
        self.push_value_scope();
        self.bind_pattern(pattern);
        if let Some(guard) = guard {
            self.resolve_expr(guard);
        }
        self.resolve_expr(body);
        self.pop_value_scope();
    }

    fn resolve_scoped_params_body(
        &mut self,
        params: &[Pat],
        body: &Expr,
        finally_expr: Option<&Expr>,
    ) {
        self.push_value_scope();
        for pat in params {
            self.resolve_pat(pat);
            self.bind_pattern(pat);
        }
        self.resolve_expr(body);
        if let Some(finally_expr) = finally_expr {
            self.resolve_expr(finally_expr);
        }
        self.pop_value_scope();
    }

    fn resolve_case_arms(&mut self, arms: &[Annotated<CaseArm>]) {
        for arm in arms {
            self.resolve_scoped_pattern_body(
                &arm.node.pattern,
                arm.node.guard.as_ref(),
                &arm.node.body,
            );
        }
    }

    fn resolve_effect_call_expr(
        &mut self,
        expr_id: NodeId,
        op_name: &str,
        qualifier: Option<&str>,
        args: &[Expr],
    ) {
        if let Some(resolved) = self.resolve_effect_op_name(op_name, qualifier) {
            self.result.effect_calls.insert(expr_id, resolved);
        }
        self.resolve_exprs(args);
    }

    fn resolve_handler_item(&mut self, item: &HandlerItem) {
        match item {
            HandlerItem::Named(named) => {
                if let Some(resolved) = self.resolve_handler_name(&named.name) {
                    self.result.handlers.insert(named.id, resolved);
                }
            }
            HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                if let Some(resolved) =
                    self.resolve_effect_op_name(&arm.op_name, arm.qualifier.as_deref())
                {
                    self.result.handler_arms.insert(arm.id, resolved);
                }
                self.resolve_scoped_params_body(
                    &arm.params,
                    &arm.body,
                    arm.finally_block.as_deref(),
                );
            }
        }
    }

    fn resolve_with_handler(&mut self, handler: &Handler) {
        match handler {
            Handler::Named(named) => {
                if let Some(resolved) = self.resolve_handler_name(&named.name) {
                    self.result.handlers.insert(named.id, resolved);
                }
            }
            Handler::Inline { items, .. } => {
                for item in items {
                    self.resolve_handler_item(&item.node);
                }
            }
        }
    }

    fn resolve_handler_body(&mut self, body: &HandlerBody) {
        for effect_ref in &body.effects {
            self.record_effect_ref(effect_ref);
        }
        for effect_ref in &body.needs {
            self.record_effect_ref(effect_ref);
        }
        self.resolve_where_clause(&body.where_clause);

        for arm in &body.arms {
            self.resolve_handler_item(&HandlerItem::Arm(arm.node.clone()));
        }

        if let Some(ret) = &body.return_clause {
            self.resolve_scoped_params_body(&ret.params, &ret.body, None);
        }
    }

    fn resolve_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::FunSignature {
                params,
                return_type,
                effects,
                where_clause,
                ..
            } => {
                for (_, texpr) in params {
                    self.resolve_type_expr(texpr);
                }
                self.resolve_type_expr(return_type);
                for effect_ref in effects {
                    self.record_effect_ref(effect_ref);
                }
                self.resolve_where_clause(where_clause);
            }
            Decl::FunBinding {
                params,
                body,
                guard,
                ..
            } => {
                self.push_value_scope();
                for pat in params {
                    self.resolve_pat(pat);
                    self.bind_pattern(pat);
                }
                self.resolve_expr(body);
                if let Some(guard) = guard {
                    self.resolve_expr(guard);
                }
                self.pop_value_scope();
            }
            Decl::Let {
                annotation, value, ..
            } => {
                if let Some(annotation) = annotation {
                    self.resolve_type_expr(annotation);
                }
                self.resolve_expr(value);
            }
            Decl::Val { value, .. } => self.resolve_expr(value),
            Decl::TypeDef { variants, .. } => {
                for variant in variants {
                    for (_, texpr) in &variant.node.fields {
                        self.resolve_type_expr(texpr);
                    }
                }
            }
            Decl::RecordDef { fields, .. } => {
                for field in fields {
                    self.resolve_type_expr(&field.node.1);
                }
            }
            Decl::EffectDef { operations, .. } => {
                for op in operations {
                    for (_, texpr) in &op.node.params {
                        self.resolve_type_expr(texpr);
                    }
                    self.resolve_type_expr(&op.node.return_type);
                    for effect_ref in &op.node.effects {
                        self.record_effect_ref(effect_ref);
                    }
                }
            }
            Decl::HandlerDef { body, .. } => self.resolve_handler_body(body),
            Decl::TraitDef {
                id,
                name,
                supertraits,
                methods,
                ..
            } => {
                self.record_trait_ref(*id, name);
                for tr in supertraits {
                    self.record_trait_ref(tr.id, &tr.name);
                }
                for method in methods {
                    for (_, texpr) in &method.node.params {
                        self.resolve_type_expr(texpr);
                    }
                    self.resolve_type_expr(&method.node.return_type);
                }
            }
            Decl::ImplDef {
                id,
                trait_name,
                target_type,
                where_clause,
                needs,
                methods,
                ..
            } => {
                if let Some(resolved) = self.resolve_trait_name(trait_name) {
                    self.result.impl_traits.insert(*id, resolved);
                }
                if let Some(resolved) = self.resolve_type_name(target_type) {
                    self.result.impl_target_types.insert(*id, resolved);
                }
                self.record_trait_ref(*id, trait_name);
                self.record_type_ref(*id, target_type);
                self.resolve_where_clause(where_clause);
                for effect_ref in needs {
                    self.record_effect_ref(effect_ref);
                }
                for method in methods {
                    self.push_value_scope();
                    for pat in &method.node.params {
                        self.resolve_pat(pat);
                        self.bind_pattern(pat);
                    }
                    self.resolve_expr(&method.node.body);
                    self.pop_value_scope();
                }
            }
            Decl::DictConstructor { methods, .. } => {
                for method in methods {
                    self.resolve_expr(method);
                }
            }
            Decl::Import { .. } | Decl::ModuleDecl { .. } => {}
        }
    }

    fn resolve_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit { .. } => {}
            ExprKind::Var { name } => {
                if !self.is_locally_bound(name)
                    && let Some(canonical_trait) = self.resolve_bare_trait_method_name(name)
                {
                    self.result.trait_methods.insert(
                        expr.id,
                        ResolvedTraitMethod {
                            trait_name: canonical_trait.clone(),
                            method: name.clone(),
                        },
                    );
                }
                if let Some(resolved) = self.resolve_value_name(name) {
                    self.result.values.insert(expr.id, resolved);
                }
            }
            ExprKind::Constructor { name } => {
                if let Some(resolved) = self.resolve_constructor_name(name) {
                    self.result.constructors.insert(expr.id, resolved);
                }
            }
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{}.{}", module, name);
                if let Some(resolved) = self.scope.resolve_value(&qualified) {
                    let canonical = resolved.to_string();
                    if let Some(trait_method) = self.qualified_trait_method(&canonical) {
                        self.result.trait_methods.insert(expr.id, trait_method);
                    }
                    self.result.values.insert(
                        expr.id,
                        ResolvedValue::Global {
                            lookup_name: canonical,
                        },
                    );
                }
            }
            ExprKind::App { func, arg } => {
                self.resolve_expr(func);
                self.resolve_expr(arg);
            }
            ExprKind::BinOp { left, right, .. } => {
                self.resolve_expr(left);
                self.resolve_expr(right);
            }
            ExprKind::UnaryMinus { expr, .. } => self.resolve_expr(expr),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.resolve_expr(cond);
                self.resolve_expr(then_branch);
                self.resolve_expr(else_branch);
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.resolve_expr(scrutinee);
                self.resolve_case_arms(arms);
            }
            ExprKind::Block { stmts, .. } => {
                self.push_value_scope();
                for stmt in stmts {
                    self.resolve_stmt(&stmt.node);
                }
                self.pop_value_scope();
            }
            ExprKind::Lambda { params, body } => {
                self.resolve_scoped_params_body(params, body, None);
            }
            ExprKind::FieldAccess { expr, .. } => self.resolve_expr(expr),
            ExprKind::RecordCreate { name, fields } => {
                if let Some(resolved) = self.resolve_type_name(name) {
                    self.result.record_types.insert(expr.id, resolved);
                }
                for (_, _, field_expr) in fields {
                    self.resolve_expr(field_expr);
                }
            }
            ExprKind::AnonRecordCreate { fields } => fields
                .iter()
                .for_each(|(_, _, field_expr)| self.resolve_expr(field_expr)),
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.resolve_expr(record);
                for (_, _, field_expr) in fields {
                    self.resolve_expr(field_expr);
                }
            }
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => self.resolve_effect_call_expr(expr.id, name, qualifier.as_deref(), args),
            ExprKind::With {
                expr: inner,
                handler,
            } => {
                self.resolve_expr(inner);
                self.resolve_with_handler(handler);
            }
            ExprKind::Resume { value } => self.resolve_expr(value),
            ExprKind::Tuple { elements } => self.resolve_exprs(elements),
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                self.push_value_scope();
                for (pat, value) in bindings {
                    self.resolve_pat(pat);
                    self.resolve_expr(value);
                    self.bind_pattern(pat);
                }
                self.resolve_expr(success);
                self.pop_value_scope();
                self.resolve_case_arms(else_arms);
            }
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                self.resolve_case_arms(arms);
                if let Some((timeout, body)) = after_clause {
                    self.resolve_expr(timeout);
                    self.resolve_expr(body);
                }
            }
            ExprKind::BitString { segments } => {
                for seg in segments {
                    self.resolve_expr(&seg.value);
                    if let Some(size) = &seg.size {
                        self.resolve_expr(size);
                    }
                }
            }
            ExprKind::Ascription { expr, type_expr } => {
                self.resolve_expr(expr);
                self.resolve_type_expr(type_expr);
            }
            ExprKind::HandlerExpr { body } => self.resolve_handler_body(body),
            ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {
                unreachable!("surface syntax should be desugared before resolution")
            }
            ExprKind::DictMethodAccess { dict, .. } => self.resolve_expr(dict),
            ExprKind::DictRef { .. } | ExprKind::ForeignCall { .. } => {}
        }
    }

    fn resolve_pat(&mut self, pat: &Pat) {
        match pat {
            Pat::Constructor { id, name, args, .. } => {
                if let Some(resolved) = self.resolve_constructor_name(name) {
                    self.result.constructors.insert(*id, resolved);
                }
                for arg in args {
                    self.resolve_pat(arg);
                }
            }
            Pat::Record { name, fields, .. } => {
                if let Some(resolved) = self.resolve_type_name(name) {
                    self.result.record_types.insert(pat.id(), resolved);
                }
                for (_, alias) in fields {
                    if let Some(alias) = alias {
                        self.resolve_pat(alias);
                    }
                }
            }
            Pat::AnonRecord { fields, .. } => {
                for (_, alias) in fields {
                    if let Some(alias) = alias {
                        self.resolve_pat(alias);
                    }
                }
            }
            Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
                for pat in elements {
                    self.resolve_pat(pat);
                }
            }
            Pat::StringPrefix { rest, .. } => self.resolve_pat(rest),
            Pat::BitStringPat { segments, .. } => {
                for seg in segments {
                    self.resolve_pat(&seg.value);
                    if let Some(size) = &seg.size {
                        self.resolve_expr(size);
                    }
                }
            }
            Pat::ConsPat { head, tail, .. } => {
                self.resolve_pat(head);
                self.resolve_pat(tail);
            }
            Pat::Or { patterns, .. } => {
                for pat in patterns {
                    self.resolve_pat(pat);
                }
            }
            Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => {}
        }
    }

    fn resolve_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(expr) => self.resolve_expr(expr),
            Stmt::Let {
                pattern,
                annotation,
                value,
                ..
            } => {
                if let Some(annotation) = annotation {
                    self.resolve_type_expr(annotation);
                }
                self.resolve_pat(pattern);
                self.resolve_expr(value);
                self.bind_pattern(pattern);
            }
            Stmt::LetFun {
                name,
                params,
                body,
                guard,
                ..
            } => {
                self.bind_local_name(name.clone());
                self.push_value_scope();
                for pat in params {
                    self.resolve_pat(pat);
                    self.bind_pattern(pat);
                }
                if let Some(guard) = guard {
                    self.resolve_expr(guard);
                }
                self.resolve_expr(body);
                self.pop_value_scope();
            }
        }
    }
}

/// Resolve names in a source program using the import/global scope and local
/// module declarations, returning an authoritative resolution map.
pub(crate) fn resolve_names(
    program: &[Decl],
    scope_map: &ScopeMap,
    current_module: Option<&str>,
) -> ResolutionResult {
    let locals = LocalModuleNames::collect(program, current_module);
    let mut resolver = Resolver::new(scope_map, locals);
    for decl in program {
        resolver.resolve_decl(decl);
    }
    resolver.into_result()
}
