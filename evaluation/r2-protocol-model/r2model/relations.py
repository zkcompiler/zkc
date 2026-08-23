"""Replay-qualified, Core-derived relation witnesses for FRI-Grind-1.

This module makes no whole-domain, FRI, or security claim. A public relation
judgment accepts only :class:`QualifiedExecution` values, replays them through
``execution.requalify``, and regenerates every schema and validation policy
from the admitted protocol subjects. A caller therefore cannot make a
comparison pass by shortening a trace schema and its map together.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
import re
from typing import Any, Mapping

from .execution import (
    QualifiedExecution,
    StrategyReceipt,
    TraceEvent,
    TraceKind,
    requalify,
)
from .frigrind import (
    ActionKind,
    Actor,
    CoreAction,
    FrozenFixture,
    Interpretation,
    Provenance,
    ScenarioVariant,
    TerminalKind,
    ValueSort,
    admit_scenario,
    fresh_fri_scenario,
    load_fixture,
)
from .terms import CheckResult, OutcomeClass, semantic_id


_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
_ANCHOR = re.compile(r"sha256:[0-9a-f]{64}\Z")
_REPO_ROOT = Path(__file__).resolve().parents[3]


class SubjectOrganization(str, Enum):
    SHARED_GRINDING_CORE = "SharedGrindingCore"
    MAPPED_DISTINCT_CORES = "MappedDistinctCores"
    HYBRID_FACTORIZATION = "HybridFactorization"


class DispositionKind(str, Enum):
    PRESERVED = "Preserved"
    SOURCE_ONLY = "SourceOnly"
    TARGET_ONLY = "TargetOnly"


class MapLaw(str, Enum):
    TYPED_VALUE_IDENTITY = "TypedValueIdentity"
    NO_COUNTERPART = "NoCounterpart"


class ObservationPolicy(str, Enum):
    EXACT_TYPED_EVENT = "ExactTypedEvent"


class OriginPolicy(str, Enum):
    INTERPRETATION_AND_SOURCE_SENSITIVE = "InterpretationAndSourceSensitive"


class TerminalPolicy(str, Enum):
    EXACT_SOURCE_RESIDUAL = "ExactSourceResidual"


class StrategyPolicy(str, Enum):
    EXACT_RECEIPT_CONTRACT = "ExactReceiptContract"


class AnchorCapability(str, Enum):
    REFERENCE_VALUE = "ReferenceValue"
    SEMANTIC_SOURCE_BYTES = "SemanticSourceBytes"


@dataclass(frozen=True)
class ActionDescriptor:
    """An indexed, complete projection of one Core action."""

    index: int
    occurrence: str
    label: str
    kind: ActionKind
    actor: Actor
    value_sort: ValueSort
    cardinality: int | None
    count: int
    namespace: str | None
    coin_source: str | None
    visibility: str | None
    required_influences: tuple[str, ...]
    predicate: str | None
    failure_effect: str | None
    route_formula: str | None
    residual: str | None

    @classmethod
    def from_core(cls, index: int, action: CoreAction) -> "ActionDescriptor":
        return cls(
            index=index,
            occurrence=action.occurrence,
            label=action.label,
            kind=action.kind,
            actor=action.actor,
            value_sort=action.value_sort,
            cardinality=action.cardinality,
            count=action.count,
            namespace=action.namespace,
            coin_source=action.coin_source.value if action.coin_source else None,
            visibility=action.visibility.value if action.visibility else None,
            required_influences=action.required_influences,
            predicate=action.predicate.value if action.predicate else None,
            failure_effect=action.failure_effect.value if action.failure_effect else None,
            route_formula=action.route_formula.value if action.route_formula else None,
            residual=action.residual.value if action.residual else None,
        )

    @property
    def value_signature(self) -> tuple[Any, ...]:
        return (
            self.occurrence,
            self.kind,
            self.actor,
            self.value_sort,
            self.cardinality,
            self.count,
        )

    def term(self) -> dict[str, Any]:
        return {
            "index": self.index,
            "occurrence": self.occurrence,
            "label": self.label,
            "kind": self.kind.value,
            "actor": self.actor.value,
            "sort": self.value_sort.value,
            "cardinality": self.cardinality,
            "count": self.count,
            "namespace": self.namespace,
            "coin_source": self.coin_source,
            "visibility": self.visibility,
            "required_influences": list(self.required_influences),
            "predicate": self.predicate,
            "failure_effect": self.failure_effect,
            "route_formula": self.route_formula,
            "residual": self.residual,
        }


@dataclass(frozen=True)
class TypedDisposition:
    source_index: int | None
    target_index: int | None
    source_occurrence: str | None
    target_occurrence: str | None
    kind: DispositionKind
    law: MapLaw

    def term(self) -> dict[str, Any]:
        return {
            "source_index": self.source_index,
            "target_index": self.target_index,
            "source": self.source_occurrence,
            "target": self.target_occurrence,
            "kind": self.kind.value,
            "law": self.law.value,
        }


@dataclass(frozen=True)
class RelationShape:
    organization: SubjectOrganization
    fresh_core_id: str
    fs_core_id: str
    fresh_actions: tuple[ActionDescriptor, ...]
    fs_actions: tuple[ActionDescriptor, ...]
    dispositions: tuple[TypedDisposition, ...]

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.relation-shape.v3",
            {
                "organization": self.organization.value,
                "fresh_core": self.fresh_core_id,
                "fs_core": self.fs_core_id,
                "fresh_actions": [item.term() for item in self.fresh_actions],
                "fs_actions": [item.term() for item in self.fs_actions],
                "dispositions": [item.term() for item in self.dispositions],
            },
        )

    def summary(self) -> dict[str, Any]:
        return {
            "shape_id": self.identity,
            "organization": self.organization.value,
            "fresh_core_id": self.fresh_core_id,
            "fs_core_id": self.fs_core_id,
            "fresh_action_count": len(self.fresh_actions),
            "fs_action_count": len(self.fs_actions),
        }


@dataclass(frozen=True)
class ValidationProfile:
    relation_shape_id: str
    fresh_evaluator_basis_id: str
    fs_evaluator_basis_id: str
    fresh_core_derivation: str
    fs_core_derivation: str
    fresh_construction_id: str
    fs_construction_id: str
    fresh_qualification_law: str
    fs_qualification_law: str
    observation_policy: ObservationPolicy
    origin_policy: OriginPolicy
    terminal_policy: TerminalPolicy
    strategy_policy: StrategyPolicy

    def term(self) -> dict[str, Any]:
        return {
            "shape": self.relation_shape_id,
            "fresh_evaluator_basis": self.fresh_evaluator_basis_id,
            "fs_evaluator_basis": self.fs_evaluator_basis_id,
            "fresh_core_derivation": self.fresh_core_derivation,
            "fs_core_derivation": self.fs_core_derivation,
            "fresh_construction": self.fresh_construction_id,
            "fs_construction": self.fs_construction_id,
            "fresh_qualification_law": self.fresh_qualification_law,
            "fs_qualification_law": self.fs_qualification_law,
            "observation_policy": self.observation_policy.value,
            "origin_policy": self.origin_policy.value,
            "terminal_policy": self.terminal_policy.value,
            "strategy_policy": self.strategy_policy.value,
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.relation-validation-profile.v3", self.term())


@dataclass(frozen=True)
class ComparedRunEvidence:
    """Exact replay evidence before Fresh/FS roles or relation policy are trusted."""

    left_qualification_id: str
    right_qualification_id: str
    left_request_id: str
    right_request_id: str
    left_record_id: str
    right_record_id: str
    left_coin_tape_id: str | None
    right_coin_tape_id: str | None
    left_dependency_qualification_ids: tuple[str, ...]
    right_dependency_qualification_ids: tuple[str, ...]

    def term(self) -> dict[str, Any]:
        return {
            "left_qualification_id": self.left_qualification_id,
            "right_qualification_id": self.right_qualification_id,
            "left_request_id": self.left_request_id,
            "right_request_id": self.right_request_id,
            "left_record_id": self.left_record_id,
            "right_record_id": self.right_record_id,
            "left_coin_tape_id": self.left_coin_tape_id,
            "right_coin_tape_id": self.right_coin_tape_id,
            "left_dependency_qualification_ids": list(
                self.left_dependency_qualification_ids
            ),
            "right_dependency_qualification_ids": list(
                self.right_dependency_qualification_ids
            ),
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.compared-run-evidence.v3", self.term())


@dataclass(frozen=True)
class RelationRunEvidence:
    relation_shape_id: str
    validation_profile_id: str
    fresh_qualification_id: str
    fs_qualification_id: str
    fresh_request_id: str
    fs_request_id: str
    fresh_record_id: str
    fs_record_id: str
    fresh_coin_tape_id: str
    fresh_dependency_qualification_ids: tuple[str, ...]
    fs_dependency_qualification_ids: tuple[str, ...]

    def term(self) -> dict[str, Any]:
        return {
            "relation_shape_id": self.relation_shape_id,
            "validation_profile_id": self.validation_profile_id,
            "fresh_qualification_id": self.fresh_qualification_id,
            "fs_qualification_id": self.fs_qualification_id,
            "fresh_request_id": self.fresh_request_id,
            "fs_request_id": self.fs_request_id,
            "fresh_record_id": self.fresh_record_id,
            "fs_record_id": self.fs_record_id,
            "fresh_coin_tape_id": self.fresh_coin_tape_id,
            "fresh_dependency_qualification_ids": list(
                self.fresh_dependency_qualification_ids
            ),
            "fs_dependency_qualification_ids": list(
                self.fs_dependency_qualification_ids
            ),
        }

    @property
    def identity(self) -> str:
        return semantic_id("r2.relation-run-evidence.v3", self.term())


@dataclass(frozen=True)
class HybridFactorization:
    relation_shape_id: str
    validation_profile_id: str
    common_occurrences: tuple[str, ...]
    fresh_local_occurrences: tuple[str, ...]
    fs_local_occurrences: tuple[str, ...]
    fresh_qualification_id: str
    fs_qualification_id: str
    projected_trace_id: str

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.hybrid-factorization.v3",
            {
                "organization": SubjectOrganization.HYBRID_FACTORIZATION.value,
                "shape": self.relation_shape_id,
                "validation_profile": self.validation_profile_id,
                "common_occurrences": list(self.common_occurrences),
                "fresh_local_occurrences": list(self.fresh_local_occurrences),
                "fs_local_occurrences": list(self.fs_local_occurrences),
                "fresh_qualification": self.fresh_qualification_id,
                "fs_qualification": self.fs_qualification_id,
                "projected_trace": self.projected_trace_id,
            },
        )


@dataclass(frozen=True)
class RelationPublicValue:
    relation_subject_id: str
    occurrence: str
    value_sort: ValueSort
    cardinality: int
    value: int
    source_evidence_id: str

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.relation-public-value.v3",
            {
                "relation_subject": self.relation_subject_id,
                "occurrence": self.occurrence,
                "sort": self.value_sort.value,
                "cardinality": self.cardinality,
                "value": self.value,
                "source_evidence": self.source_evidence_id,
            },
        )


@dataclass(frozen=True)
class ProtocolStatementOccurrence:
    qualification_id: str
    core_id: str
    request_id: str
    occurrence: str
    value_sort: ValueSort
    cardinality: int
    value: int
    trace_event_id: str

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.protocol-statement-occurrence.v3",
            {
                "qualification": self.qualification_id,
                "core": self.core_id,
                "request": self.request_id,
                "occurrence": self.occurrence,
                "sort": self.value_sort.value,
                "cardinality": self.cardinality,
                "value": self.value,
                "trace_event": self.trace_event_id,
            },
        )


@dataclass(frozen=True)
class PointwiseBridge:
    relation_value: RelationPublicValue
    protocol_statement: ProtocolStatementOccurrence
    law: str = "TypedValueEquality"

    @property
    def identity(self) -> str:
        return semantic_id(
            "r2.pointwise-statement-bridge.v3",
            {
                "relation_operand": self.relation_value.identity,
                "protocol_operand": self.protocol_statement.identity,
                "law": self.law,
            },
        )


@dataclass(frozen=True)
class AnchorReadRequest:
    label: str
    capability: AnchorCapability


def _result(
    outcome: OutcomeClass,
    boundary: str,
    code: str,
    detail: str,
    *,
    subject: str = "",
    **evidence: Any,
) -> CheckResult:
    return CheckResult(outcome, boundary, code, detail, subject, evidence)


def _with_evidence(result: CheckResult, evidence: Mapping[str, Any]) -> CheckResult:
    """Preserve a judgment while adding authoritative replay evidence."""

    return CheckResult(
        result.outcome,
        result.boundary,
        result.code,
        result.detail,
        result.subject,
        {**dict(result.evidence), **dict(evidence)},
    )


def _bounded_text(value: Any, limit: int) -> bool:
    if not isinstance(value, str) or not value:
        return False
    try:
        return len(value.encode("utf-8")) <= limit
    except UnicodeEncodeError:
        return False


def _safe_identity(value: Any) -> str:
    try:
        identity = value.identity
    except (AttributeError, TypeError, ValueError, RecursionError):
        return ""
    return identity if isinstance(identity, str) and _CONTENT_ID.fullmatch(identity) else ""


def _descriptors(scenario: ScenarioVariant) -> tuple[ActionDescriptor, ...]:
    return tuple(
        ActionDescriptor.from_core(index, action)
        for index, action in enumerate(scenario.core.actions)
    )


def _shape_vocabulary_failure(shape: RelationShape) -> CheckResult | None:
    if (
        not isinstance(shape.organization, SubjectOrganization)
        or not isinstance(shape.fresh_core_id, str)
        or _CONTENT_ID.fullmatch(shape.fresh_core_id) is None
        or not isinstance(shape.fs_core_id, str)
        or _CONTENT_ID.fullmatch(shape.fs_core_id) is None
        or not isinstance(shape.fresh_actions, tuple)
        or not isinstance(shape.fs_actions, tuple)
        or not isinstance(shape.dispositions, tuple)
        or len(shape.fresh_actions) > 64
        or len(shape.fs_actions) > 64
        or len(shape.dispositions) > 128
        or any(not isinstance(item, ActionDescriptor) for item in shape.fresh_actions)
        or any(not isinstance(item, ActionDescriptor) for item in shape.fs_actions)
        or any(not isinstance(item, TypedDisposition) for item in shape.dispositions)
    ):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:shape:vocabulary",
            "R2-SHAPE-010",
            "relation shape vocabulary or aggregate bound is malformed",
            subject=_safe_identity(shape),
        )
    return None


def _profile_vocabulary_failure(profile: ValidationProfile) -> CheckResult | None:
    ids = (
        profile.relation_shape_id,
        profile.fresh_evaluator_basis_id,
        profile.fs_evaluator_basis_id,
        profile.fresh_construction_id,
        profile.fs_construction_id,
    )
    texts = (
        profile.fresh_core_derivation,
        profile.fs_core_derivation,
        profile.fresh_qualification_law,
        profile.fs_qualification_law,
    )
    if (
        any(not isinstance(value, str) or _CONTENT_ID.fullmatch(value) is None for value in ids)
        or any(not _bounded_text(value, 256) for value in texts)
        or not isinstance(profile.observation_policy, ObservationPolicy)
        or not isinstance(profile.origin_policy, OriginPolicy)
        or not isinstance(profile.terminal_policy, TerminalPolicy)
        or not isinstance(profile.strategy_policy, StrategyPolicy)
    ):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:validation:profile-vocabulary",
            "R2-PROFILE-004",
            "validation profile vocabulary is malformed",
            subject=_safe_identity(profile),
        )
    return None


def _scenario_pair_failure(
    fresh: ScenarioVariant,
    fs: ScenarioVariant,
) -> CheckResult | None:
    if not isinstance(fresh, ScenarioVariant) or not isinstance(fs, ScenarioVariant):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:shape",
            "R2-SHAPE-001",
            "relation subjects have the wrong type",
        )
    fresh_admission = admit_scenario(fresh)
    fs_admission = admit_scenario(fs)
    if fresh_admission.outcome is not OutcomeClass.AFFIRMATIVE:
        return _result(
            (
                OutcomeClass.MALFORMED
                if fresh_admission.outcome is OutcomeClass.MALFORMED
                else OutcomeClass.MISSING_DEPENDENCY
            ),
            "relations:shape:fresh",
            "R2-SHAPE-002",
            f"Fresh subject is not admitted: {fresh_admission.code}",
            subject=_safe_identity(fresh),
        )
    if fs_admission.outcome is not OutcomeClass.AFFIRMATIVE:
        return _result(
            (
                OutcomeClass.MALFORMED
                if fs_admission.outcome is OutcomeClass.MALFORMED
                else OutcomeClass.MISSING_DEPENDENCY
            ),
            "relations:shape:fs",
            "R2-SHAPE-003",
            f"FS subject is not admitted: {fs_admission.code}",
            subject=_safe_identity(fs),
        )
    if fresh.interpretation is not Interpretation.FRESH or fs.interpretation is not Interpretation.FS:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:shape",
            "R2-SHAPE-004",
            "relation sides are not ordered Fresh then Fiat--Shamir",
        )
    return None


def derive_relation_shape(
    fresh: ScenarioVariant,
    fs: ScenarioVariant,
    organization: SubjectOrganization | None = None,
) -> RelationShape | CheckResult:
    """Derive the only admissible action schemas and map from two Cores."""

    failure = _scenario_pair_failure(fresh, fs)
    if failure is not None:
        return failure
    assert isinstance(fresh, ScenarioVariant) and isinstance(fs, ScenarioVariant)

    if organization is None:
        organization = (
            SubjectOrganization.SHARED_GRINDING_CORE
            if fresh.core.identity == fs.core.identity
            else SubjectOrganization.MAPPED_DISTINCT_CORES
        )
    if not isinstance(organization, SubjectOrganization) or organization is SubjectOrganization.HYBRID_FACTORIZATION:
        return _result(
            OutcomeClass.MALFORMED,
            "relations:shape",
            "R2-SHAPE-005",
            "direct relation organization is malformed",
        )
    if organization is SubjectOrganization.SHARED_GRINDING_CORE:
        if fresh.core.identity != fs.core.identity or not fresh.core.includes_grinding:
            return _result(
                OutcomeClass.MISMATCH,
                "relations:shape:shared",
                "R2-SHAPE-006",
                "shared organization requires the same grinding Core",
            )
    else:
        expected_fresh = fresh_fri_scenario(fs.core)
        if fresh.core.identity != expected_fresh.core.identity:
            return _result(
                OutcomeClass.MISMATCH,
                "relations:shape:distinct",
                "R2-SHAPE-007",
                "distinct organization is not the no-grind Fresh projection of the FS Core",
            )

    source = _descriptors(fresh)
    target = _descriptors(fs)
    source_by_name = {item.occurrence: item for item in source}
    target_by_name = {item.occurrence: item for item in target}
    common_source_order = tuple(
        item.occurrence for item in source if item.occurrence in target_by_name
    )
    common_target_order = tuple(
        item.occurrence for item in target if item.occurrence in source_by_name
    )
    if common_source_order != common_target_order:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:shape:order",
            "R2-SHAPE-008",
            "common Core occurrences have different order",
        )
    for occurrence in common_source_order:
        if source_by_name[occurrence].value_signature != target_by_name[occurrence].value_signature:
            return _result(
                OutcomeClass.MISMATCH,
                "relations:shape:type",
                "R2-SHAPE-009",
                f"mapped occurrence has a different value type: {occurrence}",
            )

    dispositions: list[TypedDisposition] = []
    for target_item in target:
        source_item = source_by_name.get(target_item.occurrence)
        if source_item is None:
            dispositions.append(
                TypedDisposition(
                    None,
                    target_item.index,
                    None,
                    target_item.occurrence,
                    DispositionKind.TARGET_ONLY,
                    MapLaw.NO_COUNTERPART,
                )
            )
        else:
            dispositions.append(
                TypedDisposition(
                    source_item.index,
                    target_item.index,
                    source_item.occurrence,
                    target_item.occurrence,
                    DispositionKind.PRESERVED,
                    MapLaw.TYPED_VALUE_IDENTITY,
                )
            )
    for source_item in source:
        if source_item.occurrence not in target_by_name:
            dispositions.append(
                TypedDisposition(
                    source_item.index,
                    None,
                    source_item.occurrence,
                    None,
                    DispositionKind.SOURCE_ONLY,
                    MapLaw.NO_COUNTERPART,
                )
            )

    return RelationShape(
        organization,
        fresh.core.identity,
        fs.core.identity,
        source,
        target,
        tuple(dispositions),
    )


def _replayed(value: QualifiedExecution, side: str) -> QualifiedExecution | CheckResult:
    checked = requalify(value)
    if isinstance(checked, CheckResult):
        return _result(
            checked.outcome,
            f"relations:qualification:{side}",
            "R2-RELQUAL-001",
            f"{side} execution did not requalify: {checked.code}",
            subject=_safe_identity(value),
            underlying_code=checked.code,
        )
    return checked


def _profile_unchecked(
    shape: RelationShape,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> ValidationProfile:
    return ValidationProfile(
        shape.identity,
        fresh.evaluator_basis.identity,
        fs.evaluator_basis.identity,
        fresh.request.core_derivation.value,
        fs.request.core_derivation.value,
        fresh.request.scenario.construction.identity,
        fs.request.scenario.construction.identity,
        fresh.evaluator_basis.qualification_law,
        fs.evaluator_basis.qualification_law,
        ObservationPolicy.EXACT_TYPED_EVENT,
        OriginPolicy.INTERPRETATION_AND_SOURCE_SENSITIVE,
        TerminalPolicy.EXACT_SOURCE_RESIDUAL,
        StrategyPolicy.EXACT_RECEIPT_CONTRACT,
    )


def _application_point_failure(
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult | None:
    if (
        fresh.request.inputs != fs.request.inputs
        or fresh.request.application_context != fs.request.application_context
        or fresh.request.source_fixture_id != fs.request.source_fixture_id
        or fresh.request.source_package_id != fs.request.source_package_id
    ):
        return _result(
            OutcomeClass.MISMATCH,
            "relations:validation:request-point",
            "R2-VALID-005",
            "Fresh and FS qualifications do not bind the same application point",
        )
    return None


def derive_validation_profile(
    shape: RelationShape,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> ValidationProfile | CheckResult:
    """Derive reusable validation policy and evaluator-basis bindings."""

    if not isinstance(shape, RelationShape):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:validation-profile",
            "R2-PROFILE-001",
            "relation shape has the wrong type",
        )
    shape_failure = _shape_vocabulary_failure(shape)
    if shape_failure is not None:
        return shape_failure
    left = _replayed(fresh, "fresh")
    if isinstance(left, CheckResult):
        return left
    right = _replayed(fs, "fs")
    if isinstance(right, CheckResult):
        return right
    compared_evidence = _compared_run_evidence(left, right)
    expected_shape = derive_relation_shape(
        left.request.scenario,
        right.request.scenario,
    )
    if isinstance(expected_shape, CheckResult):
        return _with_evidence(expected_shape, compared_evidence)
    expected_profile = _profile_unchecked(expected_shape, left, right)
    run_evidence = _run_evidence(expected_shape, expected_profile, left, right)
    if shape != expected_shape or shape.identity != expected_shape.identity:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:validation-profile",
            "R2-PROFILE-002",
            "relation shape differs from exact Core derivation",
            subject=_safe_identity(shape),
            supplied_shape_id=_safe_identity(shape),
            **run_evidence,
        )
    point_failure = _application_point_failure(left, right)
    if point_failure is not None:
        return _with_evidence(point_failure, run_evidence)
    if (
        left.record.disposition is not TerminalKind.SOURCE_RESIDUAL
        or right.record.disposition is not TerminalKind.SOURCE_RESIDUAL
    ):
        return _result(
            OutcomeClass.MISMATCH,
            "relations:validation-profile:terminal",
            "R2-PROFILE-003",
            "the R2 relation profile requires exact source-residual executions",
            subject=expected_shape.identity,
            **run_evidence,
        )
    return expected_profile


def _validated_pair(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> tuple[QualifiedExecution, QualifiedExecution] | CheckResult:
    if not isinstance(shape, RelationShape) or not isinstance(profile, ValidationProfile):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:validation",
            "R2-VALID-001",
            "relation shape or validation profile has the wrong type",
        )
    shape_failure = _shape_vocabulary_failure(shape)
    if shape_failure is not None:
        return shape_failure
    profile_failure = _profile_vocabulary_failure(profile)
    if profile_failure is not None:
        return profile_failure
    left = _replayed(fresh, "fresh")
    if isinstance(left, CheckResult):
        return left
    right = _replayed(fs, "fs")
    if isinstance(right, CheckResult):
        return right
    compared_evidence = _compared_run_evidence(left, right)
    expected_shape = derive_relation_shape(
        left.request.scenario,
        right.request.scenario,
    )
    if isinstance(expected_shape, CheckResult):
        return _with_evidence(expected_shape, compared_evidence)
    expected_profile = _profile_unchecked(expected_shape, left, right)
    run_evidence = _run_evidence(expected_shape, expected_profile, left, right)
    if shape != expected_shape or shape.identity != expected_shape.identity:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:validation:shape",
            "R2-VALID-002",
            "shape, schemas, order, or disposition map differs from Core authority",
            subject=_safe_identity(shape),
            supplied_shape_id=_safe_identity(shape),
            **run_evidence,
        )
    if profile != expected_profile or profile.identity != expected_profile.identity:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:validation:profile",
            "R2-VALID-004",
            "validation policy, qualification law, or evaluator-basis binding differs",
            subject=_safe_identity(profile),
            supplied_profile_id=_safe_identity(profile),
            **run_evidence,
        )
    point_failure = _application_point_failure(left, right)
    if point_failure is not None:
        return _with_evidence(point_failure, run_evidence)
    if (
        left.record.disposition is not TerminalKind.SOURCE_RESIDUAL
        or right.record.disposition is not TerminalKind.SOURCE_RESIDUAL
    ):
        return _result(
            OutcomeClass.MISMATCH,
            "relations:validation:terminal",
            "R2-VALID-003",
            "comparison is outside the exact source-residual profile",
            subject=shape.identity,
            **run_evidence,
        )
    return left, right


def check_typed_disposition_map(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult:
    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:typed-disposition-map",
        "R2-MAP-000",
        "Core-derived schemas and the exhaustive typed disposition map are exact",
        subject=shape.identity,
        shape_id=shape.identity,
        **_run_evidence(shape, profile, left, right),
    )


def _events(qualified: QualifiedExecution) -> dict[str, TraceEvent]:
    return {event.occurrence: event for event in qualified.record.events}


def _compared_run_evidence_object(
    left: QualifiedExecution,
    right: QualifiedExecution,
) -> ComparedRunEvidence:
    left_tape = left.request.coin_tape
    right_tape = right.request.coin_tape
    return ComparedRunEvidence(
        left.identity,
        right.identity,
        left.request.identity,
        right.request.identity,
        left.record.identity,
        right.record.identity,
        left_tape.identity if left_tape is not None else None,
        right_tape.identity if right_tape is not None else None,
        tuple(dependency.identity for dependency in left.dependencies),
        tuple(dependency.identity for dependency in right.dependencies),
    )


def _compared_run_evidence(
    left: QualifiedExecution,
    right: QualifiedExecution,
) -> dict[str, Any]:
    evidence = _compared_run_evidence_object(left, right)
    return {
        "compared_run_evidence_id": evidence.identity,
        **evidence.term(),
    }


def _run_evidence_object(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> RelationRunEvidence:
    tape = fresh.request.coin_tape
    assert tape is not None
    return RelationRunEvidence(
        shape.identity,
        profile.identity,
        fresh.identity,
        fs.identity,
        fresh.request.identity,
        fs.request.identity,
        fresh.record.identity,
        fs.record.identity,
        tape.identity,
        tuple(
            dependency.identity for dependency in fresh.dependencies
        ),
        tuple(
            dependency.identity for dependency in fs.dependencies
        ),
    )


def _run_evidence(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> dict[str, Any]:
    evidence = _run_evidence_object(shape, profile, fresh, fs)
    return {
        "run_evidence_id": evidence.identity,
        **evidence.term(),
    }


def derive_relation_run_evidence(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> RelationRunEvidence | CheckResult:
    """Requalify a pair and expose its immutable judgment-evidence preimage."""

    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    return _run_evidence_object(shape, profile, left, right)


def _mapped(shape: RelationShape) -> tuple[TypedDisposition, ...]:
    return tuple(
        disposition
        for disposition in shape.dispositions
        if disposition.kind is DispositionKind.PRESERVED
    )


def _event_value(value: Any) -> Any:
    return value.value if isinstance(value, Enum) else value


def _observation(event: TraceEvent) -> tuple[Any, ...]:
    return (
        event.occurrence,
        event.kind.value,
        event.actor.value,
        _event_value(event.value),
    )


def compare_mapped_values(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult:
    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    left_events, right_events = _events(left), _events(right)
    for disposition in _mapped(shape):
        assert disposition.source_occurrence is not None
        assert disposition.target_occurrence is not None
        source = left_events[disposition.source_occurrence]
        target = right_events[disposition.target_occurrence]
        if _event_value(source.value) != _event_value(target.value):
            return _result(
                OutcomeClass.MISMATCH,
                "relations:mapped-value",
                "R2-VALUE-001",
                f"mapped values differ at {source.occurrence}",
                subject=shape.identity,
                **_run_evidence(shape, profile, left, right),
            )
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:mapped-value",
        "R2-VALUE-000",
        "all mapped typed values commute",
        subject=shape.identity,
        shape_id=shape.identity,
        **_run_evidence(shape, profile, left, right),
    )


def compare_full_observations(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult:
    """Compare every mapped observable field except origin, checked separately."""

    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    left_events, right_events = _events(left), _events(right)
    for disposition in _mapped(shape):
        assert disposition.source_occurrence is not None
        assert disposition.target_occurrence is not None
        if (
            _observation(left_events[disposition.source_occurrence])
            != _observation(right_events[disposition.target_occurrence])
        ):
            return _result(
                OutcomeClass.MISMATCH,
                "relations:full-observation",
                "R2-OBS-001",
                f"mapped observation differs at {disposition.source_occurrence}",
                subject=shape.identity,
                **_run_evidence(shape, profile, left, right),
            )
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:full-observation",
        "R2-OBS-000",
        "all mapped typed observations commute; origin is evaluated separately",
        subject=shape.identity,
        shape_id=shape.identity,
        **_run_evidence(shape, profile, left, right),
    )


def compare_origins(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult:
    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    left_events, right_events = _events(left), _events(right)
    replaced: list[str] = []
    for disposition in _mapped(shape):
        assert disposition.source_occurrence is not None
        assert disposition.target_occurrence is not None
        source = left_events[disposition.source_occurrence]
        target = right_events[disposition.target_occurrence]
        if source.kind is TraceKind.CHALLENGE:
            if (
                source.origin is not Provenance.PUBLIC_COIN_TAPE
                or target.origin is not Provenance.TRANSCRIPT_CONSTRUCTION
            ):
                return _result(
                    OutcomeClass.MISMATCH,
                    "relations:origin",
                    "R2-ORIGIN-001",
                    f"challenge origin relation differs at {source.occurrence}",
                    subject=shape.identity,
                    **_run_evidence(shape, profile, left, right),
                )
            replaced.append(source.occurrence)
        elif source.origin is not target.origin:
            return _result(
                OutcomeClass.MISMATCH,
                "relations:origin",
                "R2-ORIGIN-002",
                f"non-challenge origin differs at {source.occurrence}",
                subject=shape.identity,
                **_run_evidence(shape, profile, left, right),
            )
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:origin",
        "R2-ORIGIN-000",
        "origins obey the interpretation-sensitive map",
        subject=shape.identity,
        shape_id=shape.identity,
        replaced_challenge_origins=replaced,
        **_run_evidence(shape, profile, left, right),
    )


def _receipts(qualified: QualifiedExecution) -> dict[str, StrategyReceipt]:
    return {receipt.output_occurrence: receipt for receipt in qualified.record.receipts}


def _receipt_contract(receipt: StrategyReceipt) -> tuple[Any, ...]:
    return (
        receipt.strategy_kind,
        receipt.visible_reads,
        receipt.previews,
    )


def compare_strategies(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult:
    """Classify exact strategy-contract equality, including one-sided messages."""

    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    left_receipts, right_receipts = _receipts(left), _receipts(right)
    differences: list[str] = []
    names = tuple(dict.fromkeys((*left_receipts, *right_receipts)))
    for occurrence in names:
        source = left_receipts.get(occurrence)
        target = right_receipts.get(occurrence)
        if source is None or target is None or _receipt_contract(source) != _receipt_contract(target):
            differences.append(occurrence)
    if differences:
        return _result(
            OutcomeClass.SEMANTIC_NEGATIVE,
            "relations:strategy",
            "R2-STRATEGY-001",
            "Fresh and FS prover strategy contracts are not identified",
            subject=shape.identity,
            differing_occurrences=differences,
            **_run_evidence(shape, profile, left, right),
        )
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:strategy",
        "R2-STRATEGY-000",
        "all prover strategy contracts are identical",
        subject=shape.identity,
        shape_id=shape.identity,
        **_run_evidence(shape, profile, left, right),
    )


def _projected_trace_id(
    qualified: QualifiedExecution,
    occurrences: tuple[str, ...],
) -> str:
    events = _events(qualified)
    return semantic_id(
        "r2.projected-common-trace.v3",
        [_observation(events[occurrence]) for occurrence in occurrences],
    )


def derive_hybrid_factorization(
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> HybridFactorization | CheckResult:
    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    run_evidence = _run_evidence(shape, profile, left, right)
    if shape.organization is not SubjectOrganization.MAPPED_DISTINCT_CORES:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:hybrid",
            "R2-HYBRID-001",
            "hybrid factorization requires the distinct no-grind Fresh organization",
            subject=shape.identity,
            **run_evidence,
        )
    if (
        tuple(dependency.identity for dependency in left.dependencies)
        != (right.identity,)
    ):
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "relations:hybrid:qualification-link",
            "R2-HYBRID-006",
            "hybrid factorization requires Fresh coins derived from the compared FS qualification",
            subject=shape.identity,
            expected_fs_qualification_id=right.identity,
            **run_evidence,
        )
    left_names = tuple(item.occurrence for item in shape.fresh_actions)
    right_names = tuple(item.occurrence for item in shape.fs_actions)
    right_set = set(right_names)
    left_set = set(left_names)
    common = tuple(name for name in left_names if name in right_set)
    common_from_right = tuple(name for name in right_names if name in left_set)
    fresh_local = tuple(name for name in left_names if name not in right_set)
    fs_local = tuple(name for name in right_names if name not in left_set)
    if common != common_from_right:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:hybrid:order",
            "R2-HYBRID-002",
            "common occurrence order differs",
            subject=shape.identity,
            **run_evidence,
        )
    if set(common).union(fresh_local) != left_set or set(common).union(fs_local) != right_set:
        return _result(
            OutcomeClass.CHECKER_FAILURE,
            "relations:hybrid:partition",
            "R2-HYBRID-999",
            "Core-derived hybrid partition is not exhaustive",
            subject=shape.identity,
            **run_evidence,
        )
    left_trace = _projected_trace_id(left, common)
    right_trace = _projected_trace_id(right, common)
    if left_trace != right_trace:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:hybrid:trace",
            "R2-HYBRID-003",
            "projected common traces differ",
            subject=shape.identity,
            fresh_projected_trace_id=left_trace,
            fs_projected_trace_id=right_trace,
            **run_evidence,
        )
    return HybridFactorization(
        shape.identity,
        profile.identity,
        common,
        fresh_local,
        fs_local,
        left.identity,
        right.identity,
        left_trace,
    )


def check_hybrid_factorization(
    factorization: HybridFactorization,
    shape: RelationShape,
    profile: ValidationProfile,
    fresh: QualifiedExecution,
    fs: QualifiedExecution,
) -> CheckResult:
    checked = _validated_pair(shape, profile, fresh, fs)
    if isinstance(checked, CheckResult):
        return checked
    left, right = checked
    run_evidence = _run_evidence(shape, profile, left, right)
    if not isinstance(factorization, HybridFactorization):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:hybrid",
            "R2-HYBRID-004",
            "hybrid factorization has the wrong type",
            subject=shape.identity,
            **run_evidence,
        )
    if (
        any(
            not isinstance(value, str) or _CONTENT_ID.fullmatch(value) is None
            for value in (
                factorization.relation_shape_id,
                factorization.validation_profile_id,
                factorization.fresh_qualification_id,
                factorization.fs_qualification_id,
                factorization.projected_trace_id,
            )
        )
        or any(
            not isinstance(values, tuple)
            or len(values) > 64
            or any(not _bounded_text(value, 256) for value in values)
            for values in (
                factorization.common_occurrences,
                factorization.fresh_local_occurrences,
                factorization.fs_local_occurrences,
            )
        )
    ):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:hybrid",
            "R2-HYBRID-007",
            "hybrid factorization vocabulary is malformed",
            subject=_safe_identity(factorization),
            **run_evidence,
        )
    expected = derive_hybrid_factorization(shape, profile, fresh, fs)
    if isinstance(expected, CheckResult):
        return expected
    if factorization != expected or factorization.identity != expected.identity:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:hybrid",
            "R2-HYBRID-005",
            "hybrid factorization differs from the complete Core-derived partition",
            subject=_safe_identity(factorization),
            **run_evidence,
        )
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:hybrid",
        "R2-HYBRID-000",
        "Core-derived hybrid factorization and common projected trace are exact",
        subject=factorization.identity,
        factorization_id=factorization.identity,
        projected_trace_id=factorization.projected_trace_id,
        **run_evidence,
    )


def protocol_statement_occurrence(
    qualified: QualifiedExecution,
) -> ProtocolStatementOccurrence | CheckResult:
    checked = _replayed(qualified, "statement")
    if isinstance(checked, CheckResult):
        return checked
    action = checked.request.scenario.core.action("statement:f_root")
    matches = tuple(
        event
        for event in checked.record.events
        if event.occurrence == action.occurrence
    )
    if len(matches) != 1:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "relations:statement-bridge",
            "R2-BRIDGE-002",
            "qualified execution has no unique Statement occurrence",
            subject=checked.identity,
        )
    event = matches[0]
    assert action.cardinality is not None
    return ProtocolStatementOccurrence(
        checked.identity,
        checked.request.scenario.core.identity,
        checked.request.identity,
        action.occurrence,
        action.value_sort,
        action.cardinality,
        int(event.value),
        semantic_id("r2.trace-event.v3", event.term()),
    )


def _relation_operand_failure(value: RelationPublicValue) -> CheckResult | None:
    if not isinstance(value, RelationPublicValue):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:statement-bridge:relation-operand",
            "R2-BRIDGE-003",
            "relation public value has the wrong type",
        )
    if (
        not isinstance(value.relation_subject_id, str)
        or _CONTENT_ID.fullmatch(value.relation_subject_id) is None
        or not isinstance(value.source_evidence_id, str)
        or _CONTENT_ID.fullmatch(value.source_evidence_id) is None
        or not _bounded_text(value.occurrence, 256)
        or not isinstance(value.value_sort, ValueSort)
        or isinstance(value.cardinality, bool)
        or not isinstance(value.cardinality, int)
        or value.cardinality <= 0
        or isinstance(value.value, bool)
        or not isinstance(value.value, int)
        or value.value < 0
        or value.value >= value.cardinality
    ):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:statement-bridge:relation-operand",
            "R2-BRIDGE-004",
            "relation public value is not a closed typed operand",
            subject=_safe_identity(value),
        )
    return None


def derive_pointwise_bridge(
    relation_value: RelationPublicValue | None,
    qualified: QualifiedExecution,
) -> PointwiseBridge | CheckResult:
    """Build a pointwise bridge only when both separately identified operands exist."""

    protocol_value = protocol_statement_occurrence(qualified)
    if isinstance(protocol_value, CheckResult):
        return protocol_value
    if relation_value is None:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "relations:statement-bridge:relation-operand",
            "R2-BRIDGE-001",
            "fixture provides no relation-side public value operand",
            subject=protocol_value.qualification_id,
            protocol_statement_id=protocol_value.identity,
            missing_operand="RelationPublicValue",
        )
    failure = _relation_operand_failure(relation_value)
    if failure is not None:
        return failure
    if (
        relation_value.value_sort is not protocol_value.value_sort
        or relation_value.cardinality != protocol_value.cardinality
    ):
        return _result(
            OutcomeClass.MISMATCH,
            "relations:statement-bridge:type",
            "R2-BRIDGE-005",
            "relation and protocol operands have different value types",
            subject=protocol_value.qualification_id,
            relation_operand_id=relation_value.identity,
            protocol_operand_id=protocol_value.identity,
        )
    if relation_value.value != protocol_value.value:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:statement-bridge:value",
            "R2-BRIDGE-006",
            "relation and protocol public values differ at this point",
            subject=protocol_value.qualification_id,
            relation_operand_id=relation_value.identity,
            protocol_operand_id=protocol_value.identity,
        )
    return _result(
        OutcomeClass.MISSING_DEPENDENCY,
        "relations:statement-bridge:relation-qualification",
        "R2-BRIDGE-009",
        "matching syntax and value do not supply relation-side qualification authority",
        subject=protocol_value.qualification_id,
        relation_operand_id=relation_value.identity,
        protocol_operand_id=protocol_value.identity,
        missing_dependency="QualifiedRelationPublicValue",
        missing_occurrence_map="AdmittedRelationToProtocolOccurrenceMap",
    )


def check_pointwise_bridge(
    bridge: PointwiseBridge,
    qualified: QualifiedExecution,
) -> CheckResult:
    checked = _replayed(qualified, "statement")
    if isinstance(checked, CheckResult):
        return checked
    if not isinstance(bridge, PointwiseBridge):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:statement-bridge",
            "R2-BRIDGE-007",
            "pointwise bridge has the wrong type",
        )
    if (
        not isinstance(bridge.relation_value, RelationPublicValue)
        or not isinstance(
            bridge.protocol_statement,
            ProtocolStatementOccurrence,
        )
        or not isinstance(bridge.law, str)
    ):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:statement-bridge",
            "R2-BRIDGE-011",
            "pointwise bridge vocabulary is malformed",
            subject=checked.identity,
        )
    protocol_value = protocol_statement_occurrence(checked)
    if isinstance(protocol_value, CheckResult):
        return protocol_value
    if bridge.law != "TypedValueEquality":
        return _result(
            OutcomeClass.MALFORMED,
            "relations:statement-bridge",
            "R2-BRIDGE-010",
            "pointwise bridge law is outside the closed vocabulary",
            subject=checked.identity,
        )
    if bridge.protocol_statement != protocol_value:
        return _result(
            OutcomeClass.MISMATCH,
            "relations:statement-bridge",
            "R2-BRIDGE-008",
            "pointwise bridge protocol operand differs from exact requalification",
            subject=checked.identity,
        )
    failure = _relation_operand_failure(bridge.relation_value)
    if failure is not None:
        return failure
    return _result(
        OutcomeClass.MISSING_DEPENDENCY,
        "relations:statement-bridge:relation-qualification",
        "R2-BRIDGE-009",
        "pointwise bridge cannot be admitted without relation-side qualification authority",
        subject=checked.identity,
        bridge_id=bridge.identity,
        relation_operand_id=bridge.relation_value.identity,
        protocol_operand_id=bridge.protocol_statement.identity,
        missing_dependency="QualifiedRelationPublicValue",
        missing_occurrence_map="AdmittedRelationToProtocolOccurrenceMap",
    )


def statement_correspondence(
    qualified: QualifiedExecution,
    relation_value: RelationPublicValue | None = None,
) -> CheckResult:
    """Canonical bridge judgment; the current fixture takes MissingDependency."""

    bridge = derive_pointwise_bridge(relation_value, qualified)
    if isinstance(bridge, CheckResult):
        return bridge
    return check_pointwise_bridge(bridge, qualified)


def _digest(value: Any) -> bytes | CheckResult:
    if not isinstance(value, str) or _ANCHOR.fullmatch(value) is None:
        return _result(
            OutcomeClass.MALFORMED,
            "relations:anchor-syntax",
            "R2-AUTH-003",
            "anchor is not strict lowercase sha256 syntax",
        )
    return bytes.fromhex(value[7:])


def _requalify_fixture(
    fixture: FrozenFixture,
    boundary: str,
) -> FrozenFixture | CheckResult:
    if (
        not isinstance(fixture, FrozenFixture)
        or not isinstance(fixture.relative_path, str)
        or not isinstance(fixture.sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", fixture.sha256) is None
        or not isinstance(fixture.payload_term, tuple)
        or isinstance(fixture.relation_projection_occurrences, bool)
        or not isinstance(fixture.relation_projection_occurrences, int)
    ):
        return _result(
            OutcomeClass.MALFORMED,
            boundary,
            "R2-FIXTURE-001",
            "fixture qualification input is malformed",
        )
    try:
        base = load_fixture(_REPO_ROOT)
        companion = load_fixture(_REPO_ROOT, companion=True)
    except (OSError, TypeError, ValueError) as error:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            boundary,
            "R2-FIXTURE-002",
            f"pinned fixture sources cannot be reconstructed: {error}",
        )
    expected_by_binding = {
        (base.relative_path, base.sha256): base,
        (companion.relative_path, companion.sha256): companion,
    }
    expected = expected_by_binding.get((fixture.relative_path, fixture.sha256))
    if expected is None:
        return _result(
            OutcomeClass.MISMATCH,
            boundary,
            "R2-FIXTURE-003",
            "fixture path and content binding is not registered",
            subject=f"sha256:{fixture.sha256}",
        )
    if (
        type(fixture.partitions) is not type(expected.partitions)
        or fixture.payload_term != expected.payload_term
        or fixture.partitions != expected.partitions
        or fixture.relation_projection_occurrences
        != expected.relation_projection_occurrences
        or fixture != expected
    ):
        return _result(
            OutcomeClass.MISMATCH,
            boundary,
            "R2-FIXTURE-004",
            "fixture semantic payload differs from exact source reconstruction",
            subject=f"sha256:{fixture.sha256}",
        )
    return expected


def check_anchor_authority(
    fixture: FrozenFixture,
    request: AnchorReadRequest,
) -> CheckResult:
    if (
        not isinstance(fixture, FrozenFixture)
        or not isinstance(request, AnchorReadRequest)
        or not _bounded_text(request.label, 128)
        or not isinstance(request.capability, AnchorCapability)
    ):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:source-authority",
            "R2-AUTH-002",
            "authority request is malformed",
        )
    qualified_fixture = _requalify_fixture(fixture, "relations:source-authority")
    if isinstance(qualified_fixture, CheckResult):
        return qualified_fixture
    fixture = qualified_fixture
    anchors = fixture.payload.get("anchors")
    if not isinstance(anchors, Mapping) or request.label not in anchors:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "relations:source-authority",
            "R2-AUTH-004",
            "requested anchor reference is absent",
        )
    digest = _digest(anchors[request.label])
    if isinstance(digest, CheckResult):
        return digest
    if request.capability is AnchorCapability.SEMANTIC_SOURCE_BYTES:
        return _result(
            OutcomeClass.REFUSED,
            "relations:source-authority",
            "R2-AUTH-001",
            "fixture authority exposes a reference value, not referenced source bytes",
            subject=f"sha256:{fixture.sha256}",
            label=request.label,
        )
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:source-authority",
        "R2-AUTH-000",
        "declared reference value is readable",
        subject=f"sha256:{fixture.sha256}",
        fixture_id=f"sha256:{fixture.sha256}",
        label=request.label,
        anchor=anchors[request.label],
    )


def project_sha256_216(anchor: Any) -> tuple[int, ...] | CheckResult:
    """Project a 256-bit reference into eight 27-bit limbs (216 bits total)."""

    digest = _digest(anchor)
    if isinstance(digest, CheckResult):
        return digest
    mask = (1 << 27) - 1
    limbs = tuple(
        int.from_bytes(digest[offset : offset + 4], "big") & mask
        for offset in range(0, 32, 4)
    )
    assert len(limbs) == 8 and all(0 <= limb < 1 << 27 for limb in limbs)
    return limbs


def classify_projection(fixture: FrozenFixture) -> CheckResult:
    if not isinstance(fixture, FrozenFixture):
        return _result(
            OutcomeClass.MALFORMED,
            "relations:relation-anchor-projection",
            "R2-PROJ-005",
            "fixture has the wrong type",
        )
    qualified_fixture = _requalify_fixture(
        fixture,
        "relations:relation-anchor-projection",
    )
    if isinstance(qualified_fixture, CheckResult):
        return qualified_fixture
    fixture = qualified_fixture
    count = fixture.relation_projection_occurrences
    if isinstance(count, bool) or not isinstance(count, int) or count < 0:
        return _result(
            OutcomeClass.MALFORMED,
            "relations:relation-anchor-projection",
            "R2-PROJ-006",
            "projection occurrence count is malformed",
        )
    if count == 0:
        return _result(
            OutcomeClass.NOT_EXERCISED,
            "relations:relation-anchor-projection",
            "R2-PROJ-000",
            "base fixture has no projection occurrence",
            subject=f"sha256:{fixture.sha256}",
        )
    if count != 1:
        return _result(
            OutcomeClass.UNSUPPORTED,
            "relations:relation-anchor-projection",
            "R2-PROJ-003",
            "fixture is outside the one-occurrence companion profile",
            subject=f"sha256:{fixture.sha256}",
        )
    anchors = fixture.payload.get("anchors")
    if not isinstance(anchors, Mapping) or "contract" not in anchors:
        return _result(
            OutcomeClass.MISSING_DEPENDENCY,
            "relations:relation-anchor-projection",
            "R2-PROJ-007",
            "companion projection has no contract anchor reference",
            subject=f"sha256:{fixture.sha256}",
        )
    projected = project_sha256_216(anchors["contract"])
    if isinstance(projected, CheckResult):
        return projected
    return _result(
        OutcomeClass.AFFIRMATIVE,
        "relations:relation-anchor-projection",
        "R2-PROJ-002",
        "one exact eight-by-27-bit companion projection is present",
        subject=f"sha256:{fixture.sha256}",
        fixture_id=f"sha256:{fixture.sha256}",
        anchor=anchors["contract"],
        projected_limbs=list(projected),
        input_bits=256,
        output_bits=216,
        truncated_bits=40,
    )


def projection_loss_applicability(fixture: FrozenFixture) -> CheckResult:
    classified = classify_projection(fixture)
    if classified.outcome is OutcomeClass.NOT_EXERCISED:
        return _result(
            OutcomeClass.NOT_EXERCISED,
            "analysis:projection-loss",
            "R2-LOSS-000",
            "no projection occurrence exists",
            subject=classified.subject,
        )
    if classified.outcome is not OutcomeClass.AFFIRMATIVE:
        return classified
    return _result(
        OutcomeClass.CANNOT_ANSWER,
        "analysis:projection-loss",
        "R2-LOSS-001",
        "pricing the 40-bit projection loss requires an explicit collision assumption and bound",
        subject=classified.evidence["fixture_id"],
        input_bits=256,
        output_bits=216,
        truncated_bits=40,
        required_assumption="CollisionResistanceOfProjectedSha256",
    )
