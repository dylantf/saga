use crate::ast::{BinOp as AstBinOp, BitSegSpec, Expr, ExprKind, Lit, Pat};
use crate::codegen::cerl::{
    BinSegFlags, BinSegSize, BinSegType, CArm, CBinSeg, CExpr, CLit, CPat, Endianness,
};
use crate::codegen::lower::util::core_var;
use crate::codegen::monadic::ir::{Atom, MExpr, MFunBinding};
use crate::codegen::runtime_shape::RuntimeFunctionShape;
use crate::intrinsics::IntrinsicId;

pub(super) const ABORT_TAG: &str = "__saga_handler_abort";
pub(super) const VALUE_RESULT_TAG: &str = "__saga_value_result";

pub(super) fn marked_control_tuple(tag: &str, marker: CExpr, value: CExpr) -> CExpr {
    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(tag.to_string())), marker, value])
}

pub(super) fn marked_control_pattern(tag: &str, marker: CPat, value_var: String) -> CPat {
    CPat::Tuple(vec![
        CPat::Lit(CLit::Atom(tag.to_string())),
        marker,
        CPat::Var(value_var),
    ])
}

pub(super) fn marked_control_var_pattern(tag: &str, marker_var: String, value_var: String) -> CPat {
    marked_control_pattern(tag, CPat::Var(marker_var), value_var)
}

pub(super) fn propagate_marked_control_arm(
    tag: &str,
    marker_var: String,
    value_var: String,
) -> CArm {
    CArm {
        pat: marked_control_var_pattern(tag, marker_var.clone(), value_var.clone()),
        guard: None,
        body: marked_control_tuple(tag, CExpr::Var(marker_var), CExpr::Var(value_var)),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FunctionLoweringPlan {
    DirectBody,
    DirectBodyWithCpsIsland,
    CpsBody,
}

impl FunctionLoweringPlan {
    pub(super) fn has_direct_entry(self) -> bool {
        matches!(
            self,
            FunctionLoweringPlan::DirectBody | FunctionLoweringPlan::DirectBodyWithCpsIsland
        )
    }

    pub(super) fn has_cps_body(self) -> bool {
        matches!(self, FunctionLoweringPlan::CpsBody)
    }
}

#[derive(Clone, Debug)]
pub(super) struct FunctionEntryInfo {
    pub(super) source_arity: usize,
    pub(super) callable_type_shape: RuntimeFunctionShape,
    pub(super) direct_entry_arity: Option<usize>,
    pub(super) cps_adapter_entry_arity: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct HofDirectSpecialization {
    pub(super) entry_name: String,
    pub(super) source_arity: usize,
    pub(super) callback_params: Vec<HofCallbackParam>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct HofCallbackParam {
    pub(super) index: usize,
    pub(super) source_arity: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct KnownCpsLambda {
    pub(super) dict_bindings: Vec<(String, Atom)>,
    pub(super) params: Vec<Pat>,
    pub(super) body: Box<MExpr>,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct KnownDirectLambda {
    pub(super) dict_bindings: Vec<(String, Atom)>,
    pub(super) params: Vec<Pat>,
    pub(super) body: Box<MExpr>,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct KnownDictValue {
    pub(super) constructor_name: String,
    pub(super) methods_inlineable: bool,
    pub(super) dict_params: Vec<String>,
    pub(super) dict_args: Vec<Atom>,
    pub(super) methods: Vec<Atom>,
}

#[derive(Clone, Debug)]
pub(super) struct KnownToJsonFrame {
    pub(super) constructor_name: String,
    pub(super) value_size: usize,
}

#[derive(Clone, Debug)]
pub(super) enum KnownDirectValue {
    Atom(Atom),
    Ctor {
        name: String,
        args: Vec<KnownDirectValue>,
    },
    Tuple(Vec<KnownDirectValue>),
    AnonRecord(Vec<(String, KnownDirectValue)>),
    Record {
        name: String,
        fields: Vec<(String, KnownDirectValue)>,
    },
    Core(CExpr),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct KnownDictMethodKey {
    pub(super) constructor_name: String,
    pub(super) method_index: usize,
}

impl FunctionEntryInfo {
    pub(super) fn from_fun_binding(
        fb: &MFunBinding,
        callable_type_shape: RuntimeFunctionShape,
        plan: Option<FunctionLoweringPlan>,
    ) -> Self {
        let source_arity = fb.params.len();
        let has_direct_entry = plan.is_some_and(FunctionLoweringPlan::has_direct_entry);
        let has_cps_body = plan.is_some_and(FunctionLoweringPlan::has_cps_body);
        let direct_entry_arity = has_direct_entry.then_some(source_arity);
        let cps_adapter_entry_arity = (has_direct_entry || has_cps_body)
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
    LocalCpsCallable {
        name: String,
        source_arity: usize,
        adapter_arity: usize,
        effects: Vec<String>,
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
    PureCallable {
        arity: usize,
    },
    PureCallableFromUseType,
    CpsCallable {
        module: Option<String>,
        name: String,
        source_arity: usize,
        adapter_arity: usize,
        effects: Vec<String>,
        hof_direct_specialization: Option<HofDirectSpecialization>,
    },
    RuntimeCpsCallable {
        source_arity: usize,
        adapter_arity: usize,
        effects: Vec<String>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DirectHandlerKind {
    BeamActor,
    BeamRef,
    EtsRef,
    BeamVec,
    BeamSignal,
}

impl DirectHandlerKind {
    pub(super) fn from_handler_name(handler: &str) -> Option<Self> {
        match handler.rsplit('.').next().unwrap_or(handler) {
            "beam_actor" => Some(Self::BeamActor),
            "beam_ref" => Some(Self::BeamRef),
            "ets_ref" => Some(Self::EtsRef),
            "beam_vec" => Some(Self::BeamVec),
            "beam_signal" => Some(Self::BeamSignal),
            _ => None,
        }
    }
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

pub(super) fn core_expr_is_simple_value(expr: &CExpr) -> bool {
    matches!(expr, CExpr::Lit(_) | CExpr::Var(_) | CExpr::Nil | CExpr::FunRef(_, _))
}

pub(super) fn direct_param_supported(pat: &Pat) -> bool {
    direct_pat_supported(pat)
}

pub(super) fn direct_pat_supported(pat: &Pat) -> bool {
    match pat {
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => true,
        Pat::Tuple { elements, .. } => elements.iter().all(direct_param_supported),
        Pat::Constructor { args, .. } => args.iter().all(direct_param_supported),
        Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => fields
            .iter()
            .all(|(_, pat)| pat.as_ref().is_none_or(direct_param_supported)),
        Pat::StringPrefix { rest, .. } => direct_param_supported(rest),
        Pat::BitStringPat { segments, .. } => segments
            .iter()
            .all(|segment| direct_param_supported(&segment.value)),
        _ => false,
    }
}

pub(super) fn pat_binds_name(pat: &Pat, target: &str) -> bool {
    match pat {
        Pat::Var { name, .. } => name == target,
        Pat::Constructor { args, .. } => args.iter().any(|pat| pat_binds_name(pat, target)),
        Pat::Record {
            fields, as_name, ..
        } => {
            as_name.as_ref().is_some_and(|name| name == target)
                || fields.iter().any(|(field_name, pat)| match pat {
                    Some(pat) => pat_binds_name(pat, target),
                    None => field_name == target,
                })
        }
        Pat::AnonRecord { fields, .. } => fields.iter().any(|(field_name, pat)| match pat {
            Some(pat) => pat_binds_name(pat, target),
            None => field_name == target,
        }),
        Pat::Tuple { elements, .. } => elements.iter().any(|pat| pat_binds_name(pat, target)),
        Pat::StringPrefix { rest, .. } => pat_binds_name(rest, target),
        Pat::BitStringPat { segments, .. } => segments
            .iter()
            .any(|segment| pat_binds_name(&segment.value, target)),
        Pat::ListPat { elements, .. } => elements.iter().any(|pat| pat_binds_name(pat, target)),
        Pat::ConsPat { head, tail, .. } => {
            pat_binds_name(head, target) || pat_binds_name(tail, target)
        }
        Pat::Or { patterns, .. } => patterns.iter().any(|pat| pat_binds_name(pat, target)),
        Pat::Wildcard { .. } | Pat::Lit { .. } => false,
    }
}

pub(super) fn direct_intrinsic_arity(intrinsic: IntrinsicId) -> Option<usize> {
    match intrinsic {
        IntrinsicId::PrintStdout | IntrinsicId::PrintStderr => Some(1),
        IntrinsicId::Dbg => Some(2),
        IntrinsicId::CatchPanic => Some(1),
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

pub(super) fn merge_effect_rows(mut left: Vec<String>, right: Vec<String>) -> Vec<String> {
    for effect in right {
        if !left.contains(&effect) {
            left.push(effect);
        }
    }
    left
}

pub(super) fn remote_fun_value(module: String, name: String, arity: usize) -> CExpr {
    if arity == 0 {
        CExpr::Call(module, name, vec![])
    } else {
        CExpr::Call(
            "erlang".to_string(),
            "make_fun".to_string(),
            vec![
                CExpr::Lit(CLit::Atom(module)),
                CExpr::Lit(CLit::Atom(name)),
                CExpr::Lit(CLit::Int(arity as i64)),
            ],
        )
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

pub(super) fn process_string_escapes(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some('0') => out.push('\0'),
                Some('\\') => out.push('\\'),
                Some('"') => out.push('"'),
                Some('x') => {
                    let hi = chars.next().and_then(|c| c.to_digit(16));
                    let lo = chars.next().and_then(|c| c.to_digit(16));
                    if let (Some(h), Some(l)) = (hi, lo) {
                        out.push((h * 16 + l) as u8 as char);
                    }
                }
                Some(ch) => out.push(ch),
                None => {}
            }
        } else {
            out.push(ch);
        }
    }
    out
}

pub(super) fn resolve_bit_segment_meta(specs: &[BitSegSpec]) -> (BinSegType, i64, u8) {
    let has = |s: &BitSegSpec| specs.contains(s);
    if has(&BitSegSpec::Float) {
        (BinSegType::Float, 64, 1)
    } else if has(&BitSegSpec::Binary) {
        (BinSegType::Binary, 8, 8)
    } else if has(&BitSegSpec::Utf8) {
        (BinSegType::Utf8, 0, 0)
    } else {
        (BinSegType::Integer, 8, 1)
    }
}

pub(super) fn resolve_bit_segment_flags(specs: &[BitSegSpec]) -> BinSegFlags {
    let has = |s: &BitSegSpec| specs.contains(s);
    BinSegFlags {
        signed: has(&BitSegSpec::Signed),
        endianness: if has(&BitSegSpec::Little) {
            Endianness::Little
        } else if has(&BitSegSpec::Native) {
            Endianness::Native
        } else {
            Endianness::Big
        },
    }
}

pub(super) fn resolve_bit_segment_size(
    size: Option<CExpr>,
    type_name: &BinSegType,
    default_size: i64,
) -> BinSegSize {
    if matches!(type_name, BinSegType::Utf8) {
        BinSegSize::Utf8
    } else {
        match size {
            Some(size) => BinSegSize::Expr(size),
            None => BinSegSize::Expr(CExpr::Lit(CLit::Int(default_size))),
        }
    }
}

pub(super) fn lower_pat_size_expr(expr: &Expr) -> CExpr {
    match &expr.kind {
        ExprKind::Lit {
            value: Lit::Int(_, value),
            ..
        } => CExpr::Lit(CLit::Int(*value)),
        ExprKind::Var { name, .. } => CExpr::Var(core_var(name)),
        _ => unreachable!("bitstring segment size must be an integer literal or variable"),
    }
}
