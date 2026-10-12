use crate::codegen::lower::util;
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};
use crate::typechecker::{Scheme, Type};

/// Authoritative evidence convention for a Saga CPS callable or in-scope
/// evidence frame.
///
/// `static_effects` is the canonical, statically-known prefix of the effect
/// row. `is_open_row` means callers must forward their ambient evidence tail
/// in addition to that prefix.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EvidenceAbi {
    static_effects: Vec<String>,
    is_open_row: bool,
}

impl EvidenceAbi {
    pub fn new<I, S>(effects: I, is_open_row: bool) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut static_effects: Vec<String> = effects.into_iter().map(Into::into).collect();
        static_effects.sort();
        static_effects.dedup();
        Self {
            static_effects,
            is_open_row,
        }
    }

    pub fn closed<I, S>(effects: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self::new(effects, false)
    }

    pub fn static_slots(&self) -> &[String] {
        &self.static_effects
    }

    pub fn is_open(&self) -> bool {
        self.is_open_row
    }

    /// Record a handler installed into this frame's ABI: the installed effect
    /// joins the static prefix unless it is already there.
    fn install(&mut self, installed: String) {
        if !self.static_effects.contains(&installed) {
            self.static_effects.push(installed);
            self.static_effects.sort();
        }
    }

    /// Plan one handler installation and the ABI of the resulting frame.
    ///
    /// The runtime insertion operation and the compile-time target shape must
    /// be derived together: an open frame inserts into its known prefix while
    /// a closed frame may be rebuilt in canonical order.
    pub fn plan_install(&self, installed: impl Into<String>) -> EvidenceInstallPlan {
        let installed = installed.into();
        let kind = if self.is_open_row {
            EvidenceInstallKind::StaticPrefix {
                source_static_count: self.static_slots().len(),
            }
        } else {
            EvidenceInstallKind::Canonical
        };
        let mut target = self.clone();
        target.install(installed);
        EvidenceInstallPlan { target, kind }
    }

    /// Resolve an operation's effect against this frame's static prefix. An
    /// effect named there is positional; any other must be found by its
    /// runtime tag in the open tail.
    pub fn resolve_slot(&self, effect: &str) -> EvidenceSlotResolution {
        match self.static_slots().iter().position(|tag| tag == effect) {
            Some(index) => EvidenceSlotResolution::Static(index + 1),
            None => EvidenceSlotResolution::DynamicTag,
        }
    }

    /// Merge effect requirements observed within one implementation body.
    ///
    /// This is deliberately not callback-boundary adaptation. A callback's
    /// boundary ABI and implementation ABI must remain separate so an adapter
    /// can translate an open tagged tail into the implementation's positional
    /// prefix.
    pub fn merge_requirements(left: &Self, right: &Self) -> Self {
        Self::new(
            left.static_effects
                .iter()
                .chain(&right.static_effects)
                .cloned(),
            left.is_open_row || right.is_open_row,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvidenceInstallKind {
    Canonical,
    StaticPrefix { source_static_count: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceInstallPlan {
    pub target: EvidenceAbi,
    pub kind: EvidenceInstallKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvidenceSlotResolution {
    Static(usize),
    DynamicTag,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvidenceSelector {
    Position(usize),
    DynamicTag(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvidenceReframeKind {
    Identity,
    SelectClosed {
        selectors: Vec<EvidenceSelector>,
    },
    ReframeOpen {
        source_static_count: usize,
        forward_static_positions: Vec<usize>,
        selectors: Vec<EvidenceSelector>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceReframePlan {
    pub source: EvidenceAbi,
    pub target: EvidenceAbi,
    pub kind: EvidenceReframeKind,
}

impl EvidenceReframePlan {
    pub fn between(source: &EvidenceAbi, target: &EvidenceAbi) -> Self {
        let kind = if source == target {
            EvidenceReframeKind::Identity
        } else {
            let selectors = target
                .static_slots()
                .iter()
                .map(|effect| Self::selector_for(source, effect))
                .collect();
            if target.is_open_row {
                EvidenceReframeKind::ReframeOpen {
                    source_static_count: source.static_slots().len(),
                    // A closed caller has no pre-existing tail: its unselected
                    // static entries are precisely the target row variable's
                    // concrete contents. In an open caller, the target row
                    // variable denotes the already-tagged source tail; source
                    // declaration slots (for example Router.Skip) are not part
                    // of it and must not leak across the boundary.
                    forward_static_positions: if source.is_open() {
                        Vec::new()
                    } else {
                        (1..=source.static_slots().len()).collect()
                    },
                    selectors,
                }
            } else {
                EvidenceReframeKind::SelectClosed { selectors }
            }
        };
        let plan = Self {
            source: source.clone(),
            target: target.clone(),
            kind,
        };
        plan.assert_valid();
        plan
    }

    fn assert_valid(&self) {
        let (selectors, _forward_static_positions): (&[EvidenceSelector], &[usize]) = match &self
            .kind
        {
            EvidenceReframeKind::Identity => {
                assert_eq!(
                    self.source, self.target,
                    "internal ABI planning error: identity reframe requires equal ABIs"
                );
                return;
            }
            EvidenceReframeKind::SelectClosed { selectors } => (selectors, &[]),
            EvidenceReframeKind::ReframeOpen {
                source_static_count,
                forward_static_positions,
                selectors,
            } => {
                assert_eq!(
                    *source_static_count,
                    self.source.static_slots().len(),
                    "internal ABI planning error: reframe source prefix length disagrees with source ABI"
                );
                assert!(
                    self.target.is_open(),
                    "internal ABI planning error: open reframe requires an open target ABI"
                );
                assert!(
                    forward_static_positions
                        .windows(2)
                        .all(|positions| positions[0] < positions[1]),
                    "internal ABI planning error: forwarded static positions must be unique and ordered"
                );
                for position in forward_static_positions {
                    assert!(
                        (1..=*source_static_count).contains(position),
                        "internal ABI planning error: forwarded static position {position} is outside source prefix of {source_static_count}"
                    );
                }
                (selectors, forward_static_positions)
            }
        };

        assert_eq!(
            selectors.len(),
            self.target.static_slots().len(),
            "internal ABI planning error: selector count must equal target static-slot count"
        );

        let mut selected_static_positions = std::collections::BTreeSet::new();
        for selector in selectors {
            let position = match selector {
                EvidenceSelector::Position(position) => Some(*position),
                EvidenceSelector::DynamicTag(_) => None,
            };
            if let Some(position) = position {
                assert!(
                    (1..=self.source.static_slots().len()).contains(&position),
                    "internal ABI planning error: selector position {position} is outside source prefix"
                );
                assert!(
                    selected_static_positions.insert(position),
                    "internal ABI planning error: source static slot {position} selected for multiple target slots"
                );
            }
        }
    }

    fn selector_for(source: &EvidenceAbi, target: &str) -> EvidenceSelector {
        if let Some(index) = source.static_slots().iter().position(|tag| tag == target) {
            return EvidenceSelector::Position(index + 1);
        }
        assert!(
            source.is_open_row,
            "internal ABI planning error: closed evidence source {:?} cannot satisfy target slot {target}",
            source.static_slots()
        );
        EvidenceSelector::DynamicTag(target.to_string())
    }
}

/// Calling convention for one Saga callable.
///
/// `user_arity` never includes the evidence frame or success continuation.
/// Effectful callables have one `EvidenceAbi` and therefore exactly two
/// additional Core parameters. Intrinsics bypass this representation and are
/// classified directly by `ResolvedCodegenKind`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableAbi {
    pub user_arity: usize,
    pub evidence: Option<EvidenceAbi>,
}

impl Default for CallableAbi {
    fn default() -> Self {
        Self::pure(0)
    }
}

impl CallableAbi {
    pub fn pure(user_arity: usize) -> Self {
        Self {
            user_arity,
            evidence: None,
        }
    }

    pub fn cps(user_arity: usize, evidence: EvidenceAbi) -> Self {
        Self {
            user_arity,
            evidence: Some(evidence),
        }
    }

    pub fn from_parts(user_arity: usize, evidence: Option<EvidenceAbi>) -> Self {
        match evidence {
            Some(evidence) => Self::cps(user_arity, evidence),
            None => Self::pure(user_arity),
        }
    }

    pub fn from_type(
        ty: &Type,
        mut canonicalize_effects: impl FnMut(Vec<String>) -> Vec<String>,
    ) -> Self {
        if !matches!(ty, Type::Fun(..)) {
            return Self::pure(0);
        }
        let (user_arity, effects) = util::arity_and_effects_from_type(ty);
        let evidence =
            EvidenceAbi::new(canonicalize_effects(effects), util::has_open_effect_row(ty));
        if evidence.static_effects.is_empty() && !evidence.is_open_row {
            Self::pure(user_arity)
        } else {
            Self::cps(user_arity, evidence)
        }
    }

    /// Build a declaration ABI from its full scheme, including elaborated
    /// trait-dictionary parameters that are absent from the source function
    /// arrow count.
    pub fn from_scheme(
        scheme: &Scheme,
        canonicalize_effects: impl FnMut(Vec<String>) -> Vec<String>,
    ) -> Self {
        let mut abi = Self::from_type(&scheme.ty, canonicalize_effects);
        abi.user_arity += util::dict_param_count(&scheme.constraints);
        abi
    }

    pub fn expanded_arity(&self) -> usize {
        self.user_arity + usize::from(self.evidence.is_some()) * 2
    }

    pub fn cps_evidence(&self) -> Option<EvidenceAbi> {
        self.evidence.clone()
    }

    /// The declared ABI of a resolved callee. Effects an occurrence adds
    /// through the callee's open row stay in the forwarded tail, so the
    /// declaration's static prefix is used as is.
    pub fn from_resolved_symbol(resolved: &ResolvedSymbol) -> Self {
        match &resolved.kind {
            ResolvedCodegenKind::Intrinsic { arity, .. } => CallableAbi::pure(*arity),
            ResolvedCodegenKind::BeamFunction { abi, .. }
            | ResolvedCodegenKind::ExternalFunction { abi, .. } => abi.clone(),
        }
    }
}

/// How a value of a given type is represented at runtime, as far as calling
/// it is concerned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueRepr {
    /// Not a function value at all.
    NotAFunction,
    /// A bare Erlang fun taking the user arguments.
    Bare,
    /// `{'$saga_cps', Fun}`, where `Fun` takes the user arguments followed by
    /// evidence and a continuation.
    Tagged,
}

/// Decide a function value's representation from its own type.
///
/// A function is `Tagged` if any arrow in its curried chain carries effects
/// or an open row, and `Bare` only if every arrow is closed and empty. The
/// chain is followed through return types and ends at the first return type
/// that is not a function, including an unresolved type variable. Parameter
/// types and type-constructor arguments are not inspected: a pure function
/// that takes an effectful one is still `Bare`.
pub fn value_repr(ty: &Type) -> ValueRepr {
    if !matches!(ty, Type::Fun(..)) {
        return ValueRepr::NotAFunction;
    }
    let mut current = ty;
    while let Type::Fun(_param, ret, row) = current {
        if !row.effects.is_empty() || !row.tails.is_empty() {
            return ValueRepr::Tagged;
        }
        current = ret;
    }
    ValueRepr::Bare
}

#[cfg(test)]
mod tests {
    use super::{
        CallableAbi, EvidenceAbi, EvidenceInstallKind, EvidenceReframeKind, EvidenceReframePlan,
        EvidenceSelector, EvidenceSlotResolution, ValueRepr, value_repr,
    };
    use crate::typechecker::{EffectEntry, EffectRow, Type};

    fn int() -> Type {
        Type::Con("Int".to_string(), vec![])
    }

    fn fun(param: Type, ret: Type, row: EffectRow) -> Type {
        Type::Fun(Box::new(param), Box::new(ret), row)
    }

    fn pure_fun(param: Type, ret: Type) -> Type {
        fun(param, ret, EffectRow::empty())
    }

    fn skip_row() -> EffectRow {
        EffectRow::closed(vec![EffectEntry::unnamed("Skip".to_string(), vec![])])
    }

    fn open_row() -> EffectRow {
        EffectRow {
            effects: vec![],
            tails: vec![Type::Var(7)],
        }
    }

    #[test]
    fn value_repr_of_non_functions() {
        assert_eq!(value_repr(&int()), ValueRepr::NotAFunction);
        assert_eq!(value_repr(&Type::Var(0)), ValueRepr::NotAFunction);
        assert_eq!(
            value_repr(&Type::Record(vec![("f".to_string(), int())])),
            ValueRepr::NotAFunction
        );
    }

    #[test]
    fn value_repr_of_pure_functions_is_bare() {
        assert_eq!(value_repr(&pure_fun(int(), int())), ValueRepr::Bare);
        assert_eq!(
            value_repr(&pure_fun(int(), pure_fun(int(), int()))),
            ValueRepr::Bare
        );
    }

    #[test]
    fn value_repr_with_effects_on_the_innermost_arrow_is_tagged() {
        assert_eq!(
            value_repr(&fun(int(), int(), skip_row())),
            ValueRepr::Tagged
        );
        assert_eq!(
            value_repr(&pure_fun(int(), fun(int(), int(), skip_row()))),
            ValueRepr::Tagged
        );
    }

    #[test]
    fn value_repr_with_effects_on_an_outer_arrow_only_is_tagged() {
        assert_eq!(
            value_repr(&fun(int(), pure_fun(int(), int()), skip_row())),
            ValueRepr::Tagged
        );
    }

    #[test]
    fn value_repr_of_an_open_row_only_function_is_tagged() {
        assert_eq!(
            value_repr(&fun(int(), int(), open_row())),
            ValueRepr::Tagged
        );
        assert_eq!(
            value_repr(&pure_fun(int(), fun(int(), int(), open_row()))),
            ValueRepr::Tagged
        );
        assert_eq!(
            value_repr(&fun(int(), pure_fun(int(), int()), open_row())),
            ValueRepr::Tagged
        );
    }

    #[test]
    fn value_repr_ends_the_chain_at_a_type_variable() {
        assert_eq!(
            value_repr(&pure_fun(Type::Var(0), Type::Var(1))),
            ValueRepr::Bare
        );
    }

    #[test]
    fn value_repr_does_not_look_inside_parameters_or_constructor_arguments() {
        let effectful = fun(int(), int(), skip_row());
        let open = fun(int(), int(), open_row());
        // `(Int -> Int needs {Skip}) -> Int` is a pure function that takes an
        // effectful one.
        assert_eq!(
            value_repr(&pure_fun(effectful.clone(), int())),
            ValueRepr::Bare
        );
        assert_eq!(value_repr(&pure_fun(open, int())), ValueRepr::Bare);
        // `List (Int -> Int needs {Skip})` is not a function, and a function
        // returning one is pure.
        let list = Type::Con("List".to_string(), vec![effectful]);
        assert_eq!(value_repr(&list), ValueRepr::NotAFunction);
        assert_eq!(value_repr(&pure_fun(int(), list)), ValueRepr::Bare);
    }

    #[test]
    fn callable_abi_expands_only_cps_callables() {
        let pure = CallableAbi::pure(2);
        assert_eq!(pure.expanded_arity(), 2);
        assert_eq!(pure.cps_evidence(), None);

        let cps = CallableAbi::cps(2, EvidenceAbi::new(["Main.Repo"], true));
        assert_eq!(cps.expanded_arity(), 4);
        assert_eq!(
            cps.cps_evidence(),
            Some(EvidenceAbi::new(["Main.Repo"], true))
        );
    }

    #[test]
    fn reframe_plan_reuses_identical_abi() {
        let abi = EvidenceAbi::new(["Main.Fail"], true);
        assert_eq!(
            EvidenceReframePlan::between(&abi, &abi).kind,
            EvidenceReframeKind::Identity
        );
    }

    #[test]
    fn reframe_plan_distinguishes_closed_extras_from_an_open_source_prefix() {
        let target = EvidenceAbi::new(["Main.A"], true);
        let closed = EvidenceAbi::closed(["Main.A", "Main.B"]);
        let open = EvidenceAbi::new(["Main.A", "Main.B"], true);

        assert_eq!(
            EvidenceReframePlan::between(&closed, &target).kind,
            EvidenceReframeKind::ReframeOpen {
                source_static_count: 2,
                forward_static_positions: vec![1, 2],
                selectors: vec![EvidenceSelector::Position(1)],
            }
        );
        assert_eq!(
            EvidenceReframePlan::between(&open, &target).kind,
            EvidenceReframeKind::ReframeOpen {
                source_static_count: 2,
                forward_static_positions: vec![],
                selectors: vec![EvidenceSelector::Position(1)],
            }
        );
    }

    #[test]
    fn reframe_plan_uses_dynamic_tag_for_a_slot_missing_from_an_open_source() {
        let source = EvidenceAbi::new(["Main.Repo"], true);
        let target = EvidenceAbi::new(["Main.Fail"], true);
        assert_eq!(
            EvidenceReframePlan::between(&source, &target).kind,
            EvidenceReframeKind::ReframeOpen {
                source_static_count: 1,
                forward_static_positions: vec![],
                selectors: vec![EvidenceSelector::DynamicTag("Main.Fail".into())],
            }
        );
    }

    #[test]
    #[should_panic(expected = "closed evidence source")]
    fn reframe_plan_rejects_a_missing_slot_from_a_closed_source() {
        let source = EvidenceAbi::closed(["Main.A"]);
        let target = EvidenceAbi::closed(["Main.B"]);
        let _ = EvidenceReframePlan::between(&source, &target);
    }

    #[test]
    fn reframe_plan_closes_an_open_source_with_positional_selection() {
        let source = EvidenceAbi::new(["Main.Fail", "Main.Repo"], true);
        let target = EvidenceAbi::closed(["Main.Repo"]);
        assert_eq!(
            EvidenceReframePlan::between(&source, &target).kind,
            EvidenceReframeKind::SelectClosed {
                selectors: vec![EvidenceSelector::Position(2)]
            }
        );
    }

    #[test]
    fn reframe_plan_projects_first_middle_and_last_closed_slots() {
        let source = EvidenceAbi::closed(["Main.A", "Main.B", "Main.C"]);
        for (target, expected_position) in [
            (EvidenceAbi::closed(["Main.A"]), 1),
            (EvidenceAbi::closed(["Main.B"]), 2),
            (EvidenceAbi::closed(["Main.C"]), 3),
        ] {
            assert_eq!(
                EvidenceReframePlan::between(&source, &target).kind,
                EvidenceReframeKind::SelectClosed {
                    selectors: vec![EvidenceSelector::Position(expected_position)]
                }
            );
        }
    }

    #[test]
    fn installation_plan_couples_runtime_strategy_and_target_abi() {
        let open = EvidenceAbi::new(["Main.Fail"], true);
        let open_plan = open.plan_install("Main.Repo");
        assert_eq!(
            open_plan.kind,
            EvidenceInstallKind::StaticPrefix {
                source_static_count: 1
            }
        );
        assert_eq!(
            open_plan.target,
            EvidenceAbi::new(["Main.Fail", "Main.Repo"], true)
        );

        let closed = EvidenceAbi::closed(["Main.Repo"]);
        let closed_plan = closed.plan_install("Main.Fail");
        assert_eq!(closed_plan.kind, EvidenceInstallKind::Canonical);
        assert_eq!(
            closed_plan.target,
            EvidenceAbi::closed(["Main.Fail", "Main.Repo"])
        );
    }

    #[test]
    fn slot_resolution_is_positional_only_for_a_named_static_slot() {
        let abi = EvidenceAbi::new(["Main.Fail", "Main.Repo"], true);
        assert_eq!(
            abi.resolve_slot("Main.Repo"),
            EvidenceSlotResolution::Static(2)
        );
        assert_eq!(
            abi.resolve_slot("Main.Log"),
            EvidenceSlotResolution::DynamicTag
        );
    }

    #[test]
    fn merged_requirements_union_static_slots() {
        let expected = EvidenceAbi::new(["Main.Repo", "Main.Rollback"], true);
        let inferred = EvidenceAbi::closed(["Main.Rollback"]);
        assert_eq!(
            EvidenceAbi::merge_requirements(&expected, &inferred),
            expected
        );

        let other = EvidenceAbi::closed(["Main.Log"]);
        assert_eq!(
            EvidenceAbi::merge_requirements(&expected, &other),
            EvidenceAbi::new(["Main.Log", "Main.Repo", "Main.Rollback"], true)
        );
    }
}
