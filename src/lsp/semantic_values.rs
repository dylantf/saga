use std::collections::{HashMap, HashSet};

use saga::{ast, typechecker};

pub(super) fn semantic_value_references_for_program(
    check: &typechecker::CheckResult,
    program: &[ast::Decl],
) -> HashMap<ast::NodeId, ast::NodeId> {
    let local_definitions = collect_local_value_binding_definitions(program);
    let mut references = check.references.clone();
    for (usage_id, binding_id) in check.local_value_references() {
        if let Some(definition_id) = local_definitions.get(&binding_id) {
            references.insert(usage_id, *definition_id);
        }
    }
    references
}

fn collect_local_value_binding_definitions(program: &[ast::Decl]) -> HashMap<u32, ast::NodeId> {
    let mut collector = LocalBindingDefinitionCollector::default();
    collector.collect_program(program);
    collector.definitions
}

#[derive(Default)]
struct LocalBindingDefinitionCollector {
    next_binding_id: u32,
    definitions: HashMap<u32, ast::NodeId>,
}

impl LocalBindingDefinitionCollector {
    fn collect_program(&mut self, program: &[ast::Decl]) {
        for decl in program {
            self.collect_decl(decl);
        }
    }

    fn bind_node(&mut self, node_id: ast::NodeId) {
        self.definitions.insert(self.next_binding_id, node_id);
        self.next_binding_id += 1;
    }

    fn collect_decl(&mut self, decl: &ast::Decl) {
        match decl {
            ast::Decl::FunSignature {
                params,
                return_type,
                effects,
                where_clause,
                ..
            } => {
                let _ = (params, return_type, effects, where_clause);
            }
            ast::Decl::FunBinding {
                params,
                body,
                guard,
                ..
            } => {
                for param in params {
                    self.bind_pattern(param);
                }
                self.collect_expr(body);
                if let Some(guard) = guard {
                    self.collect_expr(guard);
                }
            }
            ast::Decl::Let { value, .. } => self.collect_expr(value),
            ast::Decl::HandlerDef { body, .. } => self.collect_handler_body(body),
            ast::Decl::ImplDef { methods, .. } => {
                for method in methods {
                    for param in &method.node.params {
                        self.bind_pattern(param);
                    }
                    self.collect_expr(&method.node.body);
                }
            }
            ast::Decl::DictConstructor { methods, .. } => {
                for method in methods {
                    self.collect_expr(method);
                }
            }
            _ => {}
        }
    }

    fn bind_pattern(&mut self, pat: &ast::Pat) {
        match pat {
            ast::Pat::Var { id, .. } => self.bind_node(*id),
            ast::Pat::Constructor { args, .. } => {
                for arg in args {
                    self.bind_pattern(arg);
                }
            }
            ast::Pat::Record {
                fields, as_name, ..
            } => {
                for (_, alias) in fields {
                    if let Some(alias) = alias {
                        self.bind_pattern(alias);
                    } else {
                        self.bind_node(pat.id());
                    }
                }
                if as_name.is_some() {
                    self.bind_node(pat.id());
                }
            }
            ast::Pat::AnonRecord { fields, .. } => {
                for (_, alias) in fields {
                    if let Some(alias) = alias {
                        self.bind_pattern(alias);
                    } else {
                        self.bind_node(pat.id());
                    }
                }
            }
            ast::Pat::Tuple { elements, .. } | ast::Pat::ListPat { elements, .. } => {
                for element in elements {
                    self.bind_pattern(element);
                }
            }
            ast::Pat::StringPrefix { rest, .. } => self.bind_pattern(rest),
            ast::Pat::BitStringPat { segments, .. } => {
                for segment in segments {
                    self.bind_pattern(&segment.value);
                }
            }
            ast::Pat::ConsPat { head, tail, .. } => {
                self.bind_pattern(head);
                self.bind_pattern(tail);
            }
            ast::Pat::Or { patterns, .. } => {
                if let Some(first) = patterns.first() {
                    self.bind_pattern(first);
                }
            }
            ast::Pat::Wildcard { .. } | ast::Pat::Lit { .. } => {}
        }
    }

    fn collect_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Expr(expr) => self.collect_expr(expr),
            ast::Stmt::Let { pattern, value, .. } => {
                self.collect_expr(value);
                self.bind_pattern(pattern);
            }
            ast::Stmt::LetFun {
                id,
                params,
                guard,
                body,
                ..
            } => {
                self.bind_node(*id);
                for param in params {
                    self.bind_pattern(param);
                }
                if let Some(guard) = guard {
                    self.collect_expr(guard);
                }
                self.collect_expr(body);
            }
        }
    }

    fn collect_expr(&mut self, expr: &ast::Expr) {
        match &expr.kind {
            ast::ExprKind::Lit { .. }
            | ast::ExprKind::Var { .. }
            | ast::ExprKind::Constructor { .. }
            | ast::ExprKind::QualifiedName { .. }
            | ast::ExprKind::DictRef { .. } => {}
            ast::ExprKind::App { func, arg } => {
                self.collect_expr(func);
                self.collect_expr(arg);
            }
            ast::ExprKind::BinOp { left, right, .. } => {
                self.collect_expr(left);
                self.collect_expr(right);
            }
            ast::ExprKind::UnaryMinus { expr } => self.collect_expr(expr),
            ast::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_expr(cond);
                self.collect_expr(then_branch);
                self.collect_expr(else_branch);
            }
            ast::ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.collect_expr(scrutinee);
                for arm in arms {
                    self.bind_pattern(&arm.node.pattern);
                    if let Some(guard) = &arm.node.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.node.body);
                }
            }
            ast::ExprKind::Block { stmts, .. } => {
                for stmt in stmts {
                    self.collect_stmt(&stmt.node);
                }
            }
            ast::ExprKind::Lambda { params, body } => {
                for param in params {
                    self.bind_pattern(param);
                }
                self.collect_expr(body);
            }
            ast::ExprKind::FieldAccess { expr, .. } => self.collect_expr(expr),
            ast::ExprKind::RecordCreate { fields, .. }
            | ast::ExprKind::AnonRecordCreate { fields, .. }
            | ast::ExprKind::RecordBuild { fields, .. } => {
                for (_, _, value) in fields {
                    self.collect_expr(value);
                }
            }
            ast::ExprKind::RecordUpdate { record, fields, .. } => {
                self.collect_expr(record);
                for (_, _, value) in fields {
                    self.collect_expr(value);
                }
            }
            ast::ExprKind::EffectCall { args, .. } => {
                for arg in args {
                    self.collect_expr(arg);
                }
            }
            ast::ExprKind::With { expr, handler } => {
                self.collect_expr(expr);
                self.collect_handler(handler);
            }
            ast::ExprKind::Resume { value } => self.collect_expr(value),
            ast::ExprKind::Tuple { elements } | ast::ExprKind::ListLit { elements } => {
                for element in elements {
                    self.collect_expr(element);
                }
            }
            ast::ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                for (pattern, value) in bindings {
                    self.collect_expr(value);
                    self.bind_pattern(pattern);
                }
                self.collect_expr(success);
                for arm in else_arms {
                    self.bind_pattern(&arm.node.pattern);
                    if let Some(guard) = &arm.node.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.node.body);
                }
            }
            ast::ExprKind::Receive {
                arms, after_clause, ..
            } => {
                for arm in arms {
                    self.bind_pattern(&arm.node.pattern);
                    if let Some(guard) = &arm.node.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.node.body);
                }
                if let Some((timeout, body)) = after_clause {
                    self.collect_expr(timeout);
                    self.collect_expr(body);
                }
            }
            ast::ExprKind::BitString { segments } => {
                for segment in segments {
                    self.collect_expr(&segment.value);
                    if let Some(size) = &segment.size {
                        self.collect_expr(size);
                    }
                }
            }
            ast::ExprKind::Ascription { expr, .. } => self.collect_expr(expr),
            ast::ExprKind::HandlerExpr { body } => self.collect_handler_body(body),
            ast::ExprKind::Pipe { segments, .. }
            | ast::ExprKind::BinOpChain { segments, .. }
            | ast::ExprKind::PipeBack { segments }
            | ast::ExprKind::ComposeForward { segments } => {
                for segment in segments {
                    self.collect_expr(&segment.node);
                }
            }
            ast::ExprKind::Cons { head, tail } => {
                self.collect_expr(head);
                self.collect_expr(tail);
            }
            ast::ExprKind::StringInterp { parts, .. } => {
                for part in parts {
                    if let ast::StringPart::Expr(expr) = part {
                        self.collect_expr(expr);
                    }
                }
            }
            ast::ExprKind::ListComprehension { body, qualifiers } => {
                self.collect_expr(body);
                for qualifier in qualifiers {
                    match qualifier {
                        ast::ComprehensionQualifier::Generator(pattern, value)
                        | ast::ComprehensionQualifier::Let(pattern, value) => {
                            self.collect_expr(value);
                            self.bind_pattern(pattern);
                        }
                        ast::ComprehensionQualifier::Guard(value) => self.collect_expr(value),
                    }
                }
            }
            ast::ExprKind::DictMethodAccess { dict, .. }
            | ast::ExprKind::DictSuperAccess { dict, .. } => self.collect_expr(dict),
            ast::ExprKind::ForeignCall { args, .. } => {
                for arg in args {
                    self.collect_expr(arg);
                }
            }
        }
    }

    fn collect_handler_body(&mut self, body: &ast::HandlerBody) {
        for arm in &body.arms {
            self.collect_handler_arm(&arm.node);
        }
        if let Some(return_clause) = &body.return_clause {
            for param in &return_clause.params {
                self.bind_pattern(param);
            }
            self.collect_expr(&return_clause.body);
        }
    }

    fn collect_handler(&mut self, handler: &ast::Handler) {
        match handler {
            ast::Handler::Named(_) => {}
            ast::Handler::Inline { items, .. } => {
                for item in items {
                    match &item.node {
                        ast::HandlerItem::Named(_) => {}
                        ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                            self.collect_handler_arm(arm);
                        }
                    }
                }
            }
        }
    }

    fn collect_handler_arm(&mut self, arm: &ast::HandlerArm) {
        for param in &arm.params {
            self.bind_pattern(param);
        }
        self.collect_expr(&arm.body);
        if let Some(finally_block) = &arm.finally_block {
            self.collect_expr(finally_block);
        }
    }
}

pub(super) fn collect_value_definition_nodes(program: &[ast::Decl]) -> HashSet<ast::NodeId> {
    let mut definition_nodes = HashSet::new();
    collect_value_definition_nodes_into(program, &mut definition_nodes);
    definition_nodes
}

pub(super) fn collect_value_definition_nodes_into(
    program: &[ast::Decl],
    out: &mut HashSet<ast::NodeId>,
) {
    for decl in program {
        collect_decl_value_definition_nodes(decl, out);
    }
}

fn collect_decl_value_definition_nodes(decl: &ast::Decl, out: &mut HashSet<ast::NodeId>) {
    match decl {
        ast::Decl::FunSignature { id, .. }
        | ast::Decl::FunBinding { id, .. }
        | ast::Decl::Let { id, .. }
        | ast::Decl::HandlerDef { id, .. }
        | ast::Decl::DictConstructor { id, .. } => {
            out.insert(*id);
        }
        _ => {}
    }

    match decl {
        ast::Decl::FunBinding {
            params,
            guard,
            body,
            ..
        } => {
            for param in params {
                collect_pat_value_definition_nodes(param, out);
            }
            if let Some(guard) = guard {
                collect_expr_value_definition_nodes(guard, out);
            }
            collect_expr_value_definition_nodes(body, out);
        }
        ast::Decl::Let { value, .. } => collect_expr_value_definition_nodes(value, out),
        ast::Decl::HandlerDef { body, .. } => {
            collect_handler_body_value_definition_nodes(body, out);
        }
        ast::Decl::ImplDef { methods, .. } => {
            for method in methods {
                for param in &method.node.params {
                    collect_pat_value_definition_nodes(param, out);
                }
                collect_expr_value_definition_nodes(&method.node.body, out);
            }
        }
        ast::Decl::DictConstructor { methods, .. } => {
            for method in methods {
                collect_expr_value_definition_nodes(method, out);
            }
        }
        _ => {}
    }
}

fn collect_pat_value_definition_nodes(pat: &ast::Pat, out: &mut HashSet<ast::NodeId>) {
    match pat {
        ast::Pat::Var { id, .. } => {
            out.insert(*id);
        }
        ast::Pat::Constructor { args, .. } | ast::Pat::Tuple { elements: args, .. } => {
            for arg in args {
                collect_pat_value_definition_nodes(arg, out);
            }
        }
        ast::Pat::Record {
            fields, as_name, ..
        } => {
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    collect_pat_value_definition_nodes(field_pat, out);
                }
            }
            if as_name.is_some() {
                out.insert(pat.id());
            }
        }
        ast::Pat::AnonRecord { fields, .. } => {
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    collect_pat_value_definition_nodes(field_pat, out);
                }
            }
        }
        ast::Pat::StringPrefix { rest, .. } => collect_pat_value_definition_nodes(rest, out),
        ast::Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                collect_pat_value_definition_nodes(&segment.value, out);
            }
        }
        ast::Pat::ListPat { elements, .. }
        | ast::Pat::Or {
            patterns: elements, ..
        } => {
            for element in elements {
                collect_pat_value_definition_nodes(element, out);
            }
        }
        ast::Pat::ConsPat { head, tail, .. } => {
            collect_pat_value_definition_nodes(head, out);
            collect_pat_value_definition_nodes(tail, out);
        }
        ast::Pat::Wildcard { .. } | ast::Pat::Lit { .. } => {}
    }
}

fn collect_stmt_value_definition_nodes(stmt: &ast::Stmt, out: &mut HashSet<ast::NodeId>) {
    match stmt {
        ast::Stmt::Let { pattern, value, .. } => {
            collect_pat_value_definition_nodes(pattern, out);
            collect_expr_value_definition_nodes(value, out);
        }
        ast::Stmt::LetFun {
            id,
            params,
            guard,
            body,
            ..
        } => {
            out.insert(*id);
            for param in params {
                collect_pat_value_definition_nodes(param, out);
            }
            if let Some(guard) = guard {
                collect_expr_value_definition_nodes(guard, out);
            }
            collect_expr_value_definition_nodes(body, out);
        }
        ast::Stmt::Expr(expr) => collect_expr_value_definition_nodes(expr, out),
    }
}

fn collect_expr_value_definition_nodes(expr: &ast::Expr, out: &mut HashSet<ast::NodeId>) {
    match &expr.kind {
        ast::ExprKind::Lit { .. }
        | ast::ExprKind::Var { .. }
        | ast::ExprKind::Constructor { .. }
        | ast::ExprKind::QualifiedName { .. }
        | ast::ExprKind::DictRef { .. } => {}
        ast::ExprKind::App { func, arg } => {
            collect_expr_value_definition_nodes(func, out);
            collect_expr_value_definition_nodes(arg, out);
        }
        ast::ExprKind::BinOp { left, right, .. } => {
            collect_expr_value_definition_nodes(left, out);
            collect_expr_value_definition_nodes(right, out);
        }
        ast::ExprKind::UnaryMinus { expr } => collect_expr_value_definition_nodes(expr, out),
        ast::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_value_definition_nodes(cond, out);
            collect_expr_value_definition_nodes(then_branch, out);
            collect_expr_value_definition_nodes(else_branch, out);
        }
        ast::ExprKind::Case {
            scrutinee, arms, ..
        } => {
            collect_expr_value_definition_nodes(scrutinee, out);
            for arm in arms {
                collect_pat_value_definition_nodes(&arm.node.pattern, out);
                if let Some(guard) = &arm.node.guard {
                    collect_expr_value_definition_nodes(guard, out);
                }
                collect_expr_value_definition_nodes(&arm.node.body, out);
            }
        }
        ast::ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                collect_stmt_value_definition_nodes(&stmt.node, out);
            }
        }
        ast::ExprKind::Lambda { params, body } => {
            for param in params {
                collect_pat_value_definition_nodes(param, out);
            }
            collect_expr_value_definition_nodes(body, out);
        }
        ast::ExprKind::FieldAccess { expr, .. } => {
            collect_expr_value_definition_nodes(expr, out);
        }
        ast::ExprKind::RecordCreate { fields, .. }
        | ast::ExprKind::AnonRecordCreate { fields, .. }
        | ast::ExprKind::RecordBuild { fields, .. } => {
            for (_, _, value) in fields {
                collect_expr_value_definition_nodes(value, out);
            }
        }
        ast::ExprKind::RecordUpdate { record, fields, .. } => {
            collect_expr_value_definition_nodes(record, out);
            for (_, _, value) in fields {
                collect_expr_value_definition_nodes(value, out);
            }
        }
        ast::ExprKind::EffectCall { args, .. } => {
            for arg in args {
                collect_expr_value_definition_nodes(arg, out);
            }
        }
        ast::ExprKind::With { expr, handler } => {
            collect_expr_value_definition_nodes(expr, out);
            collect_handler_value_definition_nodes(handler, out);
        }
        ast::ExprKind::Resume { value } => collect_expr_value_definition_nodes(value, out),
        ast::ExprKind::Tuple { elements } | ast::ExprKind::ListLit { elements } => {
            for element in elements {
                collect_expr_value_definition_nodes(element, out);
            }
        }
        ast::ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pattern, value) in bindings {
                collect_pat_value_definition_nodes(pattern, out);
                collect_expr_value_definition_nodes(value, out);
            }
            collect_expr_value_definition_nodes(success, out);
            for arm in else_arms {
                collect_pat_value_definition_nodes(&arm.node.pattern, out);
                if let Some(guard) = &arm.node.guard {
                    collect_expr_value_definition_nodes(guard, out);
                }
                collect_expr_value_definition_nodes(&arm.node.body, out);
            }
        }
        ast::ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                collect_pat_value_definition_nodes(&arm.node.pattern, out);
                if let Some(guard) = &arm.node.guard {
                    collect_expr_value_definition_nodes(guard, out);
                }
                collect_expr_value_definition_nodes(&arm.node.body, out);
            }
            if let Some((timeout, body)) = after_clause {
                collect_expr_value_definition_nodes(timeout, out);
                collect_expr_value_definition_nodes(body, out);
            }
        }
        ast::ExprKind::BitString { segments } => {
            for segment in segments {
                collect_expr_value_definition_nodes(&segment.value, out);
                if let Some(size) = &segment.size {
                    collect_expr_value_definition_nodes(size, out);
                }
            }
        }
        ast::ExprKind::Ascription { expr, .. } => {
            collect_expr_value_definition_nodes(expr, out);
        }
        ast::ExprKind::HandlerExpr { body } => {
            collect_handler_body_value_definition_nodes(body, out);
        }
        ast::ExprKind::Pipe { segments, .. }
        | ast::ExprKind::BinOpChain { segments, .. }
        | ast::ExprKind::PipeBack { segments }
        | ast::ExprKind::ComposeForward { segments } => {
            for segment in segments {
                collect_expr_value_definition_nodes(&segment.node, out);
            }
        }
        ast::ExprKind::Cons { head, tail } => {
            collect_expr_value_definition_nodes(head, out);
            collect_expr_value_definition_nodes(tail, out);
        }
        ast::ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(expr) = part {
                    collect_expr_value_definition_nodes(expr, out);
                }
            }
        }
        ast::ExprKind::ListComprehension { body, qualifiers } => {
            collect_expr_value_definition_nodes(body, out);
            for qualifier in qualifiers {
                match qualifier {
                    ast::ComprehensionQualifier::Generator(pattern, value)
                    | ast::ComprehensionQualifier::Let(pattern, value) => {
                        collect_pat_value_definition_nodes(pattern, out);
                        collect_expr_value_definition_nodes(value, out);
                    }
                    ast::ComprehensionQualifier::Guard(value) => {
                        collect_expr_value_definition_nodes(value, out);
                    }
                }
            }
        }
        ast::ExprKind::DictMethodAccess { dict, .. }
        | ast::ExprKind::DictSuperAccess { dict, .. } => {
            collect_expr_value_definition_nodes(dict, out);
        }
        ast::ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                collect_expr_value_definition_nodes(arg, out);
            }
        }
    }
}

fn collect_handler_body_value_definition_nodes(
    body: &ast::HandlerBody,
    out: &mut HashSet<ast::NodeId>,
) {
    for arm in &body.arms {
        collect_handler_arm_value_definition_nodes(&arm.node, out);
    }
    if let Some(return_clause) = &body.return_clause {
        collect_handler_arm_value_definition_nodes(return_clause, out);
    }
}

fn collect_handler_value_definition_nodes(handler: &ast::Handler, out: &mut HashSet<ast::NodeId>) {
    match handler {
        ast::Handler::Named(_) => {}
        ast::Handler::Inline { items, .. } => {
            for item in items {
                match &item.node {
                    ast::HandlerItem::Named(_) => {}
                    ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                        collect_handler_arm_value_definition_nodes(arm, out);
                    }
                }
            }
        }
    }
}

fn collect_handler_arm_value_definition_nodes(
    arm: &ast::HandlerArm,
    out: &mut HashSet<ast::NodeId>,
) {
    for param in &arm.params {
        collect_pat_value_definition_nodes(param, out);
    }
    collect_expr_value_definition_nodes(&arm.body, out);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_value_definition_nodes(finally_block, out);
    }
}
