use std::collections::HashSet;

use crate::ast::{BinOp as AstBinOp, Lit, Pat};
use crate::codegen::cerl::{CBinSeg, CExpr, CLit};
use crate::codegen::lower::util::core_var;
use crate::codegen::monadic::ir::MFunBinding;
use crate::codegen::runtime_shape::RuntimeFunctionShape;
use crate::intrinsics::IntrinsicId;

#[derive(Clone, Debug)]
pub(super) struct FunctionEntryInfo {
    pub(super) source_arity: usize,
    pub(super) callable_type_shape: RuntimeFunctionShape,
    pub(super) direct_entry_arity: Option<usize>,
    pub(super) cps_adapter_entry_arity: Option<usize>,
}

impl FunctionEntryInfo {
    pub(super) fn from_fun_binding(
        fb: &MFunBinding,
        callable_type_shape: RuntimeFunctionShape,
        has_direct_body: bool,
        has_cps_body: bool,
    ) -> Self {
        let source_arity = fb.params.len();
        let direct_entry_arity = has_direct_body.then_some(source_arity);
        let cps_adapter_entry_arity = (has_direct_body || has_cps_body)
            .then_some(())
            .filter(|_| matches!(callable_type_shape, RuntimeFunctionShape::Cps(_)))
            .map(|_| source_arity + 2);
        Self {
            source_arity,
            callable_type_shape,
            direct_entry_arity,
            cps_adapter_entry_arity,
        }
    }

    pub(super) fn is_cps_typed(&self) -> bool {
        matches!(self.callable_type_shape, RuntimeFunctionShape::Cps(_))
    }
}

#[derive(Clone)]
pub(super) struct DirectCallable {
    pub(super) module: Option<String>,
    pub(super) name: String,
    pub(super) arity: usize,
}

#[derive(Clone)]
pub(super) enum CallShape {
    Intrinsic(IntrinsicId),
    Direct(DirectCallable),
    LocalCallable {
        name: String,
        arity: usize,
    },
    Cps {
        module: Option<String>,
        name: String,
        source_arity: usize,
        adapter_arity: usize,
        effects: Vec<String>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum LocalValueShape {
    PureCallable { arity: usize },
    PureCallableFromUseType,
}

pub(super) fn lower_param_names(params: &[Pat]) -> Vec<String> {
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

pub(super) fn direct_param_supported(pat: &Pat) -> bool {
    direct_pat_supported(pat)
}

pub(super) fn direct_pat_supported(pat: &Pat) -> bool {
    match pat {
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => true,
        Pat::Tuple { elements, .. } => elements.iter().all(direct_param_supported),
        Pat::Constructor { args, .. } => args.iter().all(direct_param_supported),
        _ => false,
    }
}

pub(super) fn direct_intrinsic_arity(intrinsic: IntrinsicId) -> Option<usize> {
    match intrinsic {
        IntrinsicId::PrintStdout | IntrinsicId::PrintStderr => Some(1),
        IntrinsicId::Dbg => Some(2),
        IntrinsicId::CatchPanic => None,
    }
}

pub(super) fn source_arity_for_cps_resolved(adapter_arity: usize) -> usize {
    adapter_arity.saturating_sub(2)
}

pub(super) fn direct_entry_arity_matching_resolved(
    resolved_arity: usize,
    entries: &FunctionEntryInfo,
) -> Option<usize> {
    let direct_entry_arity = entries.direct_entry_arity?;
    if direct_entry_arity == resolved_arity
        || direct_entry_arity == source_arity_for_cps_resolved(resolved_arity)
    {
        Some(direct_entry_arity)
    } else {
        None
    }
}

pub(super) fn direct_entry_name_for(name: &str, entries: &FunctionEntryInfo) -> String {
    if entries.cps_adapter_entry_arity.is_some() {
        format!("__saga_direct_{name}")
    } else {
        name.to_string()
    }
}

pub(super) fn resolved_erlang_module_for_call(
    erlang_mod: &Option<String>,
    current_module: &str,
) -> Option<String> {
    erlang_mod
        .as_ref()
        .filter(|module| module.as_str() != current_module)
        .cloned()
}

pub(super) fn erlang_module_name(module_name: &str) -> String {
    module_name
        .split('.')
        .map(str::to_lowercase)
        .collect::<Vec<_>>()
        .join("_")
}

pub(super) fn collect_pat_binders(pat: &Pat, out: &mut HashSet<String>) {
    match pat {
        Pat::Var { name, .. } => {
            out.insert(name.clone());
        }
        Pat::Tuple { elements, .. } => {
            for pat in elements {
                collect_pat_binders(pat, out);
            }
        }
        Pat::Constructor { args, .. } => {
            for pat in args {
                collect_pat_binders(pat, out);
            }
        }
        _ => {}
    }
}

pub(super) fn binop_atoms(op: &AstBinOp, l: CExpr, r: CExpr) -> CExpr {
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
        Concat => CExpr::Binary(vec![CBinSeg::BinaryAll(l), CBinSeg::BinaryAll(r)]),
        And => call("and"),
        Or => call("or"),
    }
}

pub(super) fn lower_lit_pat(lit: &Lit) -> CLit {
    match lit {
        Lit::Int(_, value) => CLit::Int(*value),
        Lit::Float(_, value) => CLit::Float(*value),
        Lit::String(value, _) => CLit::Str(value.clone()),
        Lit::Bool(value) => CLit::Atom(value.to_string()),
        Lit::Unit => CLit::Atom("unit".to_string()),
    }
}
