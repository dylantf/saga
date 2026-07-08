use std::collections::HashMap;

use saga::ast::{self, Decl, Expr, ExprKind, Pat, Stmt};
use saga::typechecker::{CheckResult, ModuleExports, Scheme};
use tower_lsp::lsp_types::*;

use super::hover::{
    effect_operation_signature_in_check, effect_operation_signature_in_exports,
    trait_method_signature_in_check, trait_method_signature_in_exports,
};
use super::state::ProjectSemanticStore;
use super::{DocumentState, SemanticSnapshot};

pub(super) fn signature_help_at(
    document: &DocumentState,
    semantic: &SemanticSnapshot,
    position: Position,
    project: Option<(&ProjectSemanticStore, &Option<std::path::PathBuf>)>,
) -> Option<SignatureHelp> {
    let parse = document.parse.as_ref()?;
    let offset = parse.line_index.position_to_offset(position, &parse.source);
    if !is_signature_context(&parse.source, offset) {
        return None;
    }

    let active_call = find_active_call(&parse.program, offset)
        .or_else(|| find_call_near(&parse.program, &parse.source, offset))
        .or_else(|| ident_before_spaces(&parse.source, offset).map(ActiveCall::plain_start))?;

    let module_exports =
        project.map(|(projects, project_root)| projects.module_exports_for_project(project_root));
    let mut signature = build_signature(
        &active_call,
        &parse.program,
        &semantic.check,
        module_exports.as_ref(),
    )?;
    signature.active_parameter = Some(active_call.active_parameter as u32);

    Some(SignatureHelp {
        signatures: vec![signature],
        active_signature: Some(0),
        active_parameter: None,
    })
}

fn is_signature_context(source: &str, offset: usize) -> bool {
    if offset == 0 {
        return false;
    }
    let bytes = source.as_bytes();
    let mut pos = offset.min(source.len()).saturating_sub(1);
    while pos > 0 && bytes[pos].is_ascii_whitespace() {
        pos -= 1;
    }
    let prev = bytes[pos];
    prev.is_ascii_alphanumeric() || matches!(prev, b'_' | b'\'' | b')' | b',' | b'(')
}

fn ident_before_spaces(source: &str, offset: usize) -> Option<String> {
    if offset == 0 {
        return None;
    }
    let bytes = source.as_bytes();
    let mut pos = offset.min(source.len()).saturating_sub(1);
    while pos > 0 && bytes[pos].is_ascii_whitespace() {
        pos -= 1;
    }
    if bytes.get(pos).is_some_and(u8::is_ascii_whitespace) {
        return None;
    }
    let end = pos + 1;
    while pos > 0
        && (bytes[pos - 1].is_ascii_alphanumeric() || matches!(bytes[pos - 1], b'_' | b'\'' | b'.'))
    {
        pos -= 1;
    }
    let name = &source[pos..end];
    if name.is_empty() || !name.as_bytes()[0].is_ascii_alphabetic() {
        return None;
    }
    Some(name.to_string())
}

#[derive(Clone)]
struct ActiveCall {
    name: String,
    node_id: Option<ast::NodeId>,
    active_parameter: usize,
    kind: ActiveCallKind,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ActiveCallKind {
    Ordinary,
    EffectOperation,
}

impl ActiveCall {
    fn plain_start(name: String) -> Self {
        Self {
            name,
            node_id: None,
            active_parameter: 0,
            kind: ActiveCallKind::Ordinary,
        }
    }

    fn ordinary(name: String, node_id: Option<ast::NodeId>, active_parameter: usize) -> Self {
        Self {
            name,
            node_id,
            active_parameter,
            kind: ActiveCallKind::Ordinary,
        }
    }

    fn effect_operation(name: String, node_id: ast::NodeId, active_parameter: usize) -> Self {
        Self {
            name,
            node_id: Some(node_id),
            active_parameter,
            kind: ActiveCallKind::EffectOperation,
        }
    }
}

fn find_call_near(program: &[Decl], source: &str, offset: usize) -> Option<ActiveCall> {
    let bytes = source.as_bytes();
    let mut pos = offset.min(source.len());
    while pos > 0 && bytes[pos - 1].is_ascii_whitespace() {
        pos -= 1;
    }
    if pos == offset || pos == 0 {
        return None;
    }
    find_active_call(program, pos - 1).map(|mut call| {
        call.active_parameter += 1;
        call
    })
}

fn find_active_call(program: &[Decl], offset: usize) -> Option<ActiveCall> {
    for decl in program {
        if let Some(result) = find_call_in_decl(decl, offset) {
            return Some(result);
        }
    }
    None
}

fn contains(span: &saga::token::Span, offset: usize) -> bool {
    offset >= span.start && offset <= span.end
}

fn find_call_in_decl(decl: &Decl, offset: usize) -> Option<ActiveCall> {
    match decl {
        Decl::FunBinding {
            params, body, span, ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for pat in params {
                if let Some(result) = find_call_in_pat(pat, offset) {
                    return Some(result);
                }
            }
            find_call_in_expr(body, offset)
        }
        Decl::ImplDef { methods, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            for method in methods {
                let ast::ImplMethod { params, body, .. } = &method.node;
                for pat in params {
                    if let Some(result) = find_call_in_pat(pat, offset) {
                        return Some(result);
                    }
                }
                if let Some(result) = find_call_in_expr(body, offset) {
                    return Some(result);
                }
            }
            None
        }
        Decl::Let { value, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            find_call_in_expr(value, offset)
        }
        _ => None,
    }
}

fn find_call_in_pat(_pat: &Pat, _offset: usize) -> Option<ActiveCall> {
    None
}

fn find_call_in_stmt(stmt: &Stmt, offset: usize) -> Option<ActiveCall> {
    match stmt {
        Stmt::Let { value, .. } => find_call_in_expr(value, offset),
        Stmt::LetFun { body, .. } => find_call_in_expr(body, offset),
        Stmt::Expr(expr) => find_call_in_expr(expr, offset),
    }
}

fn find_call_in_expr(expr: &Expr, offset: usize) -> Option<ActiveCall> {
    if !contains(&expr.span, offset) {
        return None;
    }

    match &expr.kind {
        ExprKind::App { .. } => {
            let (func, args) = unwrap_app_chain(expr);
            for arg in &args {
                if contains(&arg.span, offset)
                    && let Some(inner) = find_call_in_expr(arg, offset)
                {
                    return Some(inner);
                }
            }
            Some(callable_call(func, active_param_index(&args, offset))?)
        }
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                if let Some(result) = find_call_in_stmt(&stmt.node, offset) {
                    return Some(result);
                }
            }
            None
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_call_in_expr(cond, offset)
            .or_else(|| find_call_in_expr(then_branch, offset))
            .or_else(|| find_call_in_expr(else_branch, offset)),
        ExprKind::Case {
            scrutinee, arms, ..
        } => find_call_in_expr(scrutinee, offset).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.node
                    .guard
                    .as_ref()
                    .and_then(|guard| find_call_in_expr(guard, offset))
                    .or_else(|| find_call_in_expr(&arm.node.body, offset))
            })
        }),
        ExprKind::Lambda { body, .. } => find_call_in_expr(body, offset),
        ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => elements
            .iter()
            .find_map(|expr| find_call_in_expr(expr, offset)),
        ExprKind::BinOp { left, right, .. } => {
            find_call_in_expr(left, offset).or_else(|| find_call_in_expr(right, offset))
        }
        ExprKind::BinOpChain { segments, .. }
        | ExprKind::Pipe { segments, .. }
        | ExprKind::PipeBack { segments }
        | ExprKind::ComposeForward { segments } => segments
            .iter()
            .find_map(|segment| find_call_in_expr(&segment.node, offset)),
        ExprKind::With { expr, .. } => find_call_in_expr(expr, offset),
        ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => fields
            .iter()
            .find_map(|(_, _, expr)| find_call_in_expr(expr, offset)),
        ExprKind::RecordUpdate { record, fields, .. } => {
            find_call_in_expr(record, offset).or_else(|| {
                fields
                    .iter()
                    .find_map(|(_, _, expr)| find_call_in_expr(expr, offset))
            })
        }
        ExprKind::FieldAccess { expr, .. } => find_call_in_expr(expr, offset),
        ExprKind::Do {
            bindings, success, ..
        } => bindings
            .iter()
            .find_map(|(_, expr)| find_call_in_expr(expr, offset))
            .or_else(|| find_call_in_expr(success, offset)),
        ExprKind::Receive {
            arms, after_clause, ..
        } => arms
            .iter()
            .find_map(|arm| {
                arm.node
                    .guard
                    .as_ref()
                    .and_then(|guard| find_call_in_expr(guard, offset))
                    .or_else(|| find_call_in_expr(&arm.node.body, offset))
            })
            .or_else(|| {
                after_clause.as_ref().and_then(|(timeout, body)| {
                    find_call_in_expr(timeout, offset).or_else(|| find_call_in_expr(body, offset))
                })
            }),
        ExprKind::BitString { segments } => segments
            .iter()
            .find_map(|segment| find_call_in_expr(&segment.value, offset)),
        ExprKind::Ascription { expr, .. }
        | ExprKind::Resume { value: expr }
        | ExprKind::UnaryMinus { expr }
        | ExprKind::Cons { head: expr, .. } => find_call_in_expr(expr, offset),
        ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            for arg in args {
                if contains(&arg.span, offset)
                    && let Some(inner) = find_call_in_expr(arg, offset)
                {
                    return Some(inner);
                }
            }
            let display = qualifier
                .as_ref()
                .map(|qualifier| format!("{qualifier}.{name}"))
                .unwrap_or_else(|| name.clone());
            Some(ActiveCall::effect_operation(
                display,
                expr.id,
                active_param_index(&args.iter().collect::<Vec<&Expr>>(), offset),
            ))
        }
        ExprKind::HandlerExpr { body } => find_call_in_handler_body(body, offset),
        _ => None,
    }
}

fn find_call_in_handler_body(body: &ast::HandlerBody, offset: usize) -> Option<ActiveCall> {
    body.return_clause
        .as_ref()
        .and_then(|clause| find_call_in_expr(&clause.body, offset))
        .or_else(|| {
            body.arms
                .iter()
                .find_map(|arm| find_call_in_expr(&arm.node.body, offset))
        })
}

fn unwrap_app_chain(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func.as_ref();
    }
    args.reverse();
    (current, args)
}

fn callable_call(expr: &Expr, active_parameter: usize) -> Option<ActiveCall> {
    match &expr.kind {
        ExprKind::Var { name } | ExprKind::Constructor { name } => Some(ActiveCall::ordinary(
            name.clone(),
            Some(expr.id),
            active_parameter,
        )),
        ExprKind::QualifiedName { module, name, .. } => Some(ActiveCall::ordinary(
            format!("{module}.{name}"),
            Some(expr.id),
            active_parameter,
        )),
        ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            let display = qualifier
                .as_ref()
                .map(|qualifier| format!("{qualifier}.{name}"))
                .unwrap_or_else(|| name.clone());
            Some(ActiveCall::effect_operation(
                display,
                expr.id,
                args.len() + active_parameter,
            ))
        }
        _ => None,
    }
}

fn active_param_index(args: &[&Expr], offset: usize) -> usize {
    for (index, arg) in args.iter().enumerate() {
        if offset <= arg.span.end {
            return index;
        }
    }
    args.len()
}

fn build_signature(
    call: &ActiveCall,
    program: &[Decl],
    result: &CheckResult,
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
) -> Option<SignatureInformation> {
    build_from_semantic_call(call, result, project_exports)
        .or_else(|| build_from_annotation(&call.name, program))
        .or_else(|| {
            scheme_for_name(&call.name, result, project_exports)
                .and_then(|scheme| build_from_scheme(scheme, result))
        })
        .or_else(|| build_from_member_name(&call.name, result, project_exports))
}

fn build_from_semantic_call(
    call: &ActiveCall,
    result: &CheckResult,
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
) -> Option<SignatureInformation> {
    let node_id = call.node_id?;
    if call.kind == ActiveCallKind::EffectOperation
        && let Some((effect_name, op_name)) =
            result.resolved_effect_operation_for_call_node(node_id)
    {
        return signature_from_label(
            effect_operation_signature_in_check(result, effect_name, op_name).or_else(|| {
                effect_operation_signature_in_project(project_exports, effect_name, op_name)
            })?,
        );
    }
    if let Some((trait_name, method_name)) = result.resolved_trait_method_for_node(node_id) {
        return signature_from_label(
            trait_method_signature_in_check(result, trait_name, method_name).or_else(|| {
                trait_method_signature_in_project(project_exports, trait_name, method_name)
            })?,
        );
    }
    None
}

fn build_from_member_name(
    name: &str,
    result: &CheckResult,
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
) -> Option<SignatureInformation> {
    if let Some((owner, member)) = name.rsplit_once('.') {
        return trait_method_signature_in_check(result, owner, member)
            .or_else(|| trait_method_signature_in_project(project_exports, owner, member))
            .or_else(|| effect_operation_signature_in_check(result, owner, member))
            .or_else(|| effect_operation_signature_in_project(project_exports, owner, member))
            .and_then(signature_from_label);
    }

    trait_method_signature_for_member_in_check(result, name)
        .or_else(|| trait_method_signature_for_member_in_project(project_exports, name))
        .or_else(|| effect_operation_signature_for_member_in_check(result, name))
        .or_else(|| effect_operation_signature_for_member_in_project(project_exports, name))
        .and_then(signature_from_label)
}

fn trait_method_signature_for_member_in_check(
    check: &CheckResult,
    method_name: &str,
) -> Option<String> {
    check
        .traits
        .iter()
        .find_map(|(trait_name, info)| {
            info.methods
                .iter()
                .any(|method| method.name == method_name)
                .then(|| trait_method_signature_in_check(check, trait_name, method_name))
                .flatten()
        })
        .or_else(|| {
            check
                .module_check_results()
                .values()
                .find_map(|module| trait_method_signature_for_member_in_check(module, method_name))
        })
}

fn effect_operation_signature_for_member_in_check(
    check: &CheckResult,
    op_name: &str,
) -> Option<String> {
    check
        .effects
        .iter()
        .find_map(|(effect_name, info)| {
            info.ops
                .iter()
                .any(|op| op.name == op_name)
                .then(|| effect_operation_signature_in_check(check, effect_name, op_name))
                .flatten()
        })
        .or_else(|| {
            check
                .module_check_results()
                .values()
                .find_map(|module| effect_operation_signature_for_member_in_check(module, op_name))
        })
}

fn trait_method_signature_in_project(
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
    trait_name: &str,
    method_name: &str,
) -> Option<String> {
    project_exports?
        .values()
        .find_map(|exports| trait_method_signature_in_exports(exports, trait_name, method_name))
}

fn effect_operation_signature_in_project(
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
    effect_name: &str,
    op_name: &str,
) -> Option<String> {
    project_exports?
        .values()
        .find_map(|exports| effect_operation_signature_in_exports(exports, effect_name, op_name))
}

fn trait_method_signature_for_member_in_project(
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
    method_name: &str,
) -> Option<String> {
    project_exports?.values().find_map(|exports| {
        exports.traits.iter().find_map(|(surface_name, info)| {
            info.methods
                .iter()
                .any(|method| method.name == method_name)
                .then(|| {
                    let origin = exports
                        .trait_origins
                        .get(surface_name)
                        .map(String::as_str)
                        .unwrap_or(surface_name);
                    trait_method_signature_in_exports(exports, origin, method_name)
                })
                .flatten()
        })
    })
}

fn effect_operation_signature_for_member_in_project(
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
    op_name: &str,
) -> Option<String> {
    project_exports?.values().find_map(|exports| {
        exports.effects.iter().find_map(|(surface_name, info)| {
            info.ops
                .iter()
                .any(|op| op.name == op_name)
                .then(|| {
                    let origin = exports
                        .effect_origins
                        .get(surface_name)
                        .map(String::as_str)
                        .unwrap_or(surface_name);
                    effect_operation_signature_in_exports(exports, origin, op_name)
                })
                .flatten()
        })
    })
}

fn build_from_annotation(name: &str, program: &[Decl]) -> Option<SignatureInformation> {
    let bare_name = name.rsplit('.').next().unwrap_or(name);
    for decl in program {
        if let Decl::FunSignature {
            name: fn_name,
            params,
            return_type,
            effects,
            ..
        } = decl
        {
            if fn_name != bare_name {
                continue;
            }
            let param_infos = params
                .iter()
                .map(|(label, ty)| {
                    let label = if label.starts_with('_') {
                        format_type_expr(ty)
                    } else {
                        format!("{}: {}", label, format_type_expr(ty))
                    };
                    ParameterInformation {
                        label: ParameterLabel::Simple(label),
                        documentation: None,
                    }
                })
                .collect::<Vec<_>>();
            let params_display = params
                .iter()
                .map(|(label, ty)| {
                    if label.starts_with('_') {
                        format_type_expr(ty)
                    } else {
                        format!("({}: {})", label, format_type_expr(ty))
                    }
                })
                .collect::<Vec<_>>();
            let mut label = if params_display.is_empty() {
                format_type_expr(return_type)
            } else {
                format!(
                    "{} -> {}",
                    params_display.join(" -> "),
                    format_type_expr(return_type)
                )
            };
            if !effects.is_empty() {
                let effects = effects
                    .iter()
                    .map(format_effect_ref)
                    .collect::<Vec<_>>()
                    .join(", ");
                label.push_str(&format!(" needs {{{effects}}}"));
            }
            return Some(SignatureInformation {
                label,
                documentation: None,
                parameters: Some(param_infos),
                active_parameter: None,
            });
        }
    }
    None
}

fn scheme_for_name(
    name: &str,
    result: &CheckResult,
    project_exports: Option<&HashMap<String, std::sync::Arc<ModuleExports>>>,
) -> Option<Scheme> {
    if let Some(scheme) = result
        .env
        .get(name)
        .or_else(|| result.constructors.get(name))
    {
        return Some(scheme.clone());
    }
    let (module, member) = name.rsplit_once('.')?;
    result
        .module_exports()
        .get(module)
        .or_else(|| {
            result
                .module_exports()
                .iter()
                .find(|(module_name, _)| module_name.rsplit('.').next() == Some(module))
                .map(|(_, exports)| exports)
        })
        .or_else(|| {
            project_exports.and_then(|exports| {
                exports.get(module).or_else(|| {
                    exports
                        .iter()
                        .find(|(module_name, _)| module_name.rsplit('.').next() == Some(module))
                        .map(|(_, exports)| exports)
                })
            })
        })
        .and_then(|exports| scheme_from_exports(exports, member))
}

fn scheme_from_exports(exports: &ModuleExports, member: &str) -> Option<Scheme> {
    exports
        .bindings
        .iter()
        .find(|(name, _)| name == member)
        .map(|(_, scheme)| scheme.clone())
}

fn build_from_scheme(scheme: Scheme, result: &CheckResult) -> Option<SignatureInformation> {
    let label = scheme.display_with_constraints(&result.sub);
    let parts = split_arrow_type(&label);
    if parts.len() < 2 {
        return None;
    }
    let parameters = parts[..parts.len() - 1]
        .iter()
        .map(|part| ParameterInformation {
            label: ParameterLabel::Simple((*part).to_string()),
            documentation: None,
        })
        .collect();
    Some(SignatureInformation {
        label,
        documentation: None,
        parameters: Some(parameters),
        active_parameter: None,
    })
}

fn signature_from_label(label: String) -> Option<SignatureInformation> {
    let type_part = label
        .split_once(" : ")
        .map(|(_, ty)| ty)
        .unwrap_or(label.as_str());
    let parts = split_arrow_type(type_part);
    if parts.len() < 2 {
        return None;
    }
    let parameters = parts[..parts.len() - 1]
        .iter()
        .map(|part| ParameterInformation {
            label: ParameterLabel::Simple((*part).to_string()),
            documentation: None,
        })
        .collect();
    Some(SignatureInformation {
        label,
        documentation: None,
        parameters: Some(parameters),
        active_parameter: None,
    })
}

fn split_arrow_type(label: &str) -> Vec<&str> {
    label.split(" -> ").collect()
}

fn format_type_expr(ty: &ast::TypeExpr) -> String {
    match ty {
        ast::TypeExpr::Var { name, .. } | ast::TypeExpr::Named { name, .. } => name.clone(),
        ast::TypeExpr::App { .. } => {
            let mut args = Vec::new();
            let mut current = ty;
            while let ast::TypeExpr::App { func, arg, .. } = current {
                args.push(format_type_expr(arg));
                current = func;
            }
            args.reverse();
            format!("{} {}", format_type_expr(current), args.join(" "))
        }
        ast::TypeExpr::Arrow {
            from,
            to,
            effects,
            effect_row_var,
            ..
        } => {
            let mut rendered = format!("{} -> {}", format_type_expr(from), format_type_expr(to));
            if !effects.is_empty() || !effect_row_var.is_empty() {
                let mut entries = effects.iter().map(format_effect_ref).collect::<Vec<_>>();
                for (row, _) in effect_row_var {
                    entries.push(format!("..{row}"));
                }
                rendered.push_str(&format!(" needs {{{}}}", entries.join(", ")));
            }
            rendered
        }
        ast::TypeExpr::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", format_type_expr(ty)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        ast::TypeExpr::Labeled { label, inner, .. } => {
            format!("({}: {})", label, format_type_expr(inner))
        }
    }
}

fn format_effect_ref(effect: &ast::EffectRef) -> String {
    if effect.type_args.is_empty() {
        effect.name.clone()
    } else {
        let args = effect
            .type_args
            .iter()
            .map(format_type_expr)
            .collect::<Vec<_>>()
            .join(" ");
        format!("{} {}", effect.name, args)
    }
}
