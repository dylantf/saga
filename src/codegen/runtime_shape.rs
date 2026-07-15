use crate::codegen::lower::util;
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};
use crate::typechecker::{Scheme, Type};

#[derive(Clone, Copy)]
struct EffectSlotIdentity<'a> {
    family: &'a str,
    placeholder: bool,
}

impl<'a> EffectSlotIdentity<'a> {
    fn new(tag: &'a str) -> Self {
        Self {
            family: crate::typechecker::applied_effect_family(tag),
            // Bare family names and applications containing a compiler type
            // variable are the two generalized runtime spellings.
            placeholder: !tag.contains('<') || tag.contains('$'),
        }
    }

    fn same_family(self, other: Self) -> bool {
        self.family == other.family
    }
}

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

    /// Specialize the statically declared slots at one use site without
    /// folding effects supplied by an open row variable into that prefix.
    ///
    /// A callee compiled as `{A, B, ..e}` always addresses A and B as its
    /// first two slots. If an occurrence instantiates `..e` with Z, the call
    /// frame must remain `{A, B | Z}`, even when the fully instantiated set
    /// would sort as `{Z, A, B}` by canonical module name.
    fn specialize_declared_slots(&self, occurrence: &Self) -> Self {
        let static_effects = self
            .static_effects
            .iter()
            .map(|declared| {
                if occurrence.static_effects.contains(declared) {
                    return declared.clone();
                }
                let declared_identity = EffectSlotIdentity::new(declared);
                let family_matches = occurrence
                    .static_effects
                    .iter()
                    .filter(|candidate| {
                        declared_identity.same_family(EffectSlotIdentity::new(candidate))
                    })
                    .collect::<Vec<_>>();
                if let [candidate] = family_matches.as_slice()
                    && (declared_identity.placeholder
                        || EffectSlotIdentity::new(candidate).placeholder)
                {
                    (*candidate).clone()
                } else {
                    declared.clone()
                }
            })
            .collect();
        Self {
            static_effects,
            is_open_row: self.is_open_row,
        }
    }

    /// Record a handler installed into this frame's ABI.
    ///
    /// An open frame may carry one bare/generalized family placeholder for a
    /// caller-specialized applied effect. Installing the concrete application
    /// specializes that unique placeholder. Closed frames describe actual
    /// runtime entries, so only exact identities replace.
    fn install(&mut self, installed: String) {
        if self.static_effects.contains(&installed) {
            return;
        }

        if self.is_open_row {
            let installed_identity = EffectSlotIdentity::new(&installed);
            let same_family = self
                .static_effects
                .iter()
                .enumerate()
                .filter(|(_, effect)| {
                    installed_identity.same_family(EffectSlotIdentity::new(effect))
                })
                .map(|(idx, _)| idx)
                .collect::<Vec<_>>();

            if same_family.len() == 1
                && EffectSlotIdentity::new(&self.static_effects[same_family[0]]).placeholder
                && !installed_identity.placeholder
            {
                self.static_effects[same_family[0]] = installed;
            } else {
                self.static_effects.push(installed);
            }
        } else {
            self.static_effects.push(installed);
        }

        self.static_effects.sort();
        self.static_effects.dedup();
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

    /// Resolve an operation's effect identity against this frame's static
    /// prefix. Exact identities are positional. A unique generic family slot
    /// is also positional, but a distinct concrete sibling must be found by
    /// its runtime tag (normally in an open tail).
    pub fn resolve_slot(&self, effect: &str) -> EvidenceSlotResolution {
        if let Some(index) = self.static_slots().iter().position(|tag| tag == effect) {
            return EvidenceSlotResolution::Static(index + 1);
        }

        let requested = EffectSlotIdentity::new(effect);
        let family_matches = self
            .static_slots()
            .iter()
            .enumerate()
            .filter(|(_, tag)| requested.same_family(EffectSlotIdentity::new(tag)))
            .collect::<Vec<_>>();
        if let [(index, tag)] = family_matches.as_slice()
            && (EffectSlotIdentity::new(tag).placeholder || requested.placeholder)
        {
            EvidenceSlotResolution::Static(*index + 1)
        } else {
            EvidenceSlotResolution::DynamicTag
        }
    }

    /// Derive the runtime shape of a lambda placed into an expected callback
    /// slot. The expected type defines the positional ABI; the inferred type
    /// contributes effects absorbed by an open tail.
    pub fn for_lambda_boundary(expected: &Self, inferred: &Self) -> Self {
        let mut static_effects = expected.static_effects.clone();
        for inferred_effect in &inferred.static_effects {
            if static_effects
                .iter()
                .any(|effect| effect == inferred_effect)
            {
                continue;
            }
            let inferred_identity = EffectSlotIdentity::new(inferred_effect);
            let same_family = static_effects
                .iter()
                .enumerate()
                .filter(|(_, effect)| {
                    inferred_identity.same_family(EffectSlotIdentity::new(effect))
                })
                .map(|(idx, _)| idx)
                .collect::<Vec<_>>();
            if same_family.len() == 1
                && (EffectSlotIdentity::new(&static_effects[same_family[0]]).placeholder
                    || inferred_identity.placeholder)
            {
                // A generic and concrete spelling of the same applied effect
                // describe one positional slot. Prefer the concrete spelling
                // when available, but never mint a second slot for the type
                // variable spelling.
                if !inferred_identity.placeholder {
                    static_effects[same_family[0]] = inferred_effect.clone();
                }
            } else {
                // Distinct concrete applications of one effect family are
                // independent slots and must coexist.
                static_effects.push(inferred_effect.clone());
            }
        }
        static_effects.sort();
        static_effects.dedup();
        Self {
            static_effects,
            is_open_row: expected.is_open_row || inferred.is_open_row,
        }
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
    Relabel { position: usize, target: String },
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
                .map(|effect| Self::selector_for(source, target, effect))
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
                EvidenceSelector::Position(position)
                | EvidenceSelector::Relabel { position, .. } => Some(*position),
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

    fn selector_for(
        source: &EvidenceAbi,
        target_abi: &EvidenceAbi,
        target: &str,
    ) -> EvidenceSelector {
        if let Some(index) = source.static_slots().iter().position(|tag| tag == target) {
            return EvidenceSelector::Position(index + 1);
        }
        let target_identity = EffectSlotIdentity::new(target);
        let family_matches = source
            .static_slots()
            .iter()
            .enumerate()
            .filter(|(_, tag)| target_identity.same_family(EffectSlotIdentity::new(tag)))
            .map(|(index, _)| index + 1)
            .collect::<Vec<_>>();
        if (!source.is_open_row || target_abi.is_open_row)
            && let [position] = family_matches.as_slice()
            && (EffectSlotIdentity::new(&source.static_slots()[*position - 1]).placeholder
                || target_identity.placeholder)
        {
            EvidenceSelector::Relabel {
                position: *position,
                target: target.to_string(),
            }
        } else {
            assert!(
                source.is_open_row,
                "internal ABI planning error: closed evidence source {:?} cannot satisfy target slot {target}",
                source.static_slots()
            );
            EvidenceSelector::DynamicTag(target.to_string())
        }
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

    pub fn from_resolved_symbol(
        resolved: &ResolvedSymbol,
        fallback_ty: Option<&Type>,
        mut canonicalize_effects: impl FnMut(Vec<String>) -> Vec<String>,
    ) -> Self {
        match &resolved.kind {
            ResolvedCodegenKind::Intrinsic { arity, .. } => CallableAbi::pure(*arity),
            ResolvedCodegenKind::BeamFunction { abi, .. }
            | ResolvedCodegenKind::ExternalFunction { abi, .. } => {
                let fallback =
                    fallback_ty.map(|ty| CallableAbi::from_type(ty, &mut canonicalize_effects));
                let occurrence_evidence = fallback.and_then(|abi| abi.evidence);
                // The occurrence type carries call-site specialization, while
                // the exported ABI defines the callee's positional prefix.
                // Specialize declaration slots in place; effects absorbed by
                // an open row remain in the forwarded tail.
                let mut instantiated = abi.clone();
                if let (Some(declared), Some(occurrence)) =
                    (abi.evidence.as_ref(), occurrence_evidence.as_ref())
                {
                    instantiated.evidence = Some(declared.specialize_declared_slots(occurrence));
                }
                instantiated
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        CallableAbi, EvidenceAbi, EvidenceInstallKind, EvidenceReframeKind, EvidenceReframePlan,
        EvidenceSelector, EvidenceSlotResolution,
    };

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
    fn open_declaration_specialization_keeps_row_effects_out_of_static_prefix() {
        let declared = EvidenceAbi::new(["OpenAdapter.A", "OpenAdapter.B"], true);
        let occurrence = EvidenceAbi::new(["Main.Z", "OpenAdapter.A", "OpenAdapter.B"], true);
        assert_eq!(
            declared.specialize_declared_slots(&occurrence),
            EvidenceAbi::new(["OpenAdapter.A", "OpenAdapter.B"], true)
        );
    }

    #[test]
    fn reframe_plan_reuses_identical_abi() {
        let abi = EvidenceAbi::new(["Main.Fail<Std.Int.Int>"], true);
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
    fn reframe_plan_relabels_a_unique_generic_family_slot() {
        let source = EvidenceAbi::new(["Main.Rollback<$1>"], true);
        let target = EvidenceAbi::new(["Main.Rollback<Std.String.String>"], true);
        assert_eq!(
            EvidenceReframePlan::between(&source, &target).kind,
            EvidenceReframeKind::ReframeOpen {
                source_static_count: 1,
                forward_static_positions: vec![],
                selectors: vec![EvidenceSelector::Relabel {
                    position: 1,
                    target: "Main.Rollback<Std.String.String>".into(),
                }],
            }
        );
    }

    #[test]
    fn reframe_plan_uses_dynamic_tag_for_missing_or_ambiguous_static_family() {
        let missing = EvidenceAbi::new(["Main.Repo"], true);
        let concrete_sibling = EvidenceAbi::new(["Main.Fail<Std.String.String>"], true);
        let ambiguous = EvidenceAbi::new(
            ["Main.Fail<Std.Int.Int>", "Main.Fail<Std.String.String>"],
            true,
        );
        let target = EvidenceAbi::new(["Main.Fail<Std.Bool.Bool>"], true);
        for source in [&missing, &concrete_sibling, &ambiguous] {
            assert_eq!(
                EvidenceReframePlan::between(source, &target).kind,
                EvidenceReframeKind::ReframeOpen {
                    source_static_count: source.static_slots().len(),
                    forward_static_positions: vec![],
                    selectors: vec![EvidenceSelector::DynamicTag(
                        "Main.Fail<Std.Bool.Bool>".into()
                    )],
                }
            );
        }
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
    fn reframe_plan_searches_open_tail_before_relabeling_a_placeholder() {
        let source = EvidenceAbi::new(["Main.Fail"], true);
        let target = EvidenceAbi::closed(["Main.Fail<Std.Int.Int>"]);
        assert_eq!(
            EvidenceReframePlan::between(&source, &target).kind,
            EvidenceReframeKind::SelectClosed {
                selectors: vec![EvidenceSelector::DynamicTag(
                    "Main.Fail<Std.Int.Int>".into()
                )]
            }
        );
    }

    #[test]
    fn installation_plan_couples_runtime_strategy_and_target_abi() {
        let open = EvidenceAbi::new(["Main.Fail"], true);
        let open_plan = open.plan_install("Main.Fail<Std.String.String>");
        assert_eq!(
            open_plan.kind,
            EvidenceInstallKind::StaticPrefix {
                source_static_count: 1
            }
        );
        assert_eq!(
            open_plan.target,
            EvidenceAbi::new(["Main.Fail<Std.String.String>"], true)
        );

        let closed = EvidenceAbi::closed(["Main.Repo"]);
        let closed_plan = closed.plan_install("Main.Fail<Std.String.String>");
        assert_eq!(closed_plan.kind, EvidenceInstallKind::Canonical);
        assert_eq!(
            closed_plan.target,
            EvidenceAbi::closed(["Main.Fail<Std.String.String>", "Main.Repo"])
        );
    }

    #[test]
    fn slot_resolution_does_not_steal_a_concrete_sibling() {
        let abi = EvidenceAbi::new(["Main.Fail<Std.String.String>"], true);
        assert_eq!(
            abi.resolve_slot("Main.Fail<Std.String.String>"),
            EvidenceSlotResolution::Static(1)
        );
        assert_eq!(
            abi.resolve_slot("Main.Fail<Std.Int.Int>"),
            EvidenceSlotResolution::DynamicTag
        );

        let generic = EvidenceAbi::new(["Main.Fail<$1>"], true);
        assert_eq!(
            generic.resolve_slot("Main.Fail<Std.Int.Int>"),
            EvidenceSlotResolution::Static(1)
        );
    }

    #[test]
    fn lambda_boundary_keeps_unused_expected_slots() {
        let expected = EvidenceAbi {
            static_effects: vec![
                "Main.Repo".into(),
                "Main.Rollback<Std.String.String>".into(),
            ],
            is_open_row: true,
        };
        let inferred = EvidenceAbi {
            static_effects: vec!["Main.Rollback<Std.String.String>".into()],
            is_open_row: false,
        };

        assert_eq!(
            EvidenceAbi::for_lambda_boundary(&expected, &inferred),
            expected
        );
    }

    #[test]
    fn lambda_boundary_keeps_distinct_concrete_family_slots() {
        let expected = EvidenceAbi {
            static_effects: vec!["Main.Fail<Std.Int.Int>".into()],
            is_open_row: true,
        };
        let inferred = EvidenceAbi {
            static_effects: vec!["Main.Fail<Std.String.String>".into()],
            is_open_row: false,
        };

        assert_eq!(
            EvidenceAbi::for_lambda_boundary(&expected, &inferred).static_effects,
            vec!["Main.Fail<Std.Int.Int>", "Main.Fail<Std.String.String>"]
        );
    }

    #[test]
    fn lambda_boundary_collapses_generic_and_concrete_family_slot() {
        let expected = EvidenceAbi {
            static_effects: vec!["Main.Rollback<$1>".into()],
            is_open_row: false,
        };
        let inferred = EvidenceAbi {
            static_effects: vec!["Main.Rollback<Std.String.String>".into()],
            is_open_row: false,
        };

        assert_eq!(
            EvidenceAbi::for_lambda_boundary(&expected, &inferred).static_effects,
            vec!["Main.Rollback<Std.String.String>"]
        );
    }
}
