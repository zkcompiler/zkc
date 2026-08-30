"""Bounded Relations pressure instruments for the exact classical FRI control.

The module grounds the selected public statement and initial logical oracle,
then consumes a reusable PIR-owned oracle-commitment construction view.  An
accepting finite execution leaves Reed--Solomon proximity unevaluated and can
never establish an outer computation relation.  Its raw native-trace grounding
is not a durable interface; it exposes the future need for a PIR-owned,
purpose-specific confidential Oracle view.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from .classical import (
    DEGREE_BOUNDS,
    DOMAIN_ORDERS,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_NATIVE_CORE,
    FOLD_ROUNDS,
    GOLDILOCKS_MODULUS,
    LAYER_QUERY_OCCURRENCES,
    QUERY_REPETITIONS,
    ClassicalLogicalOracle,
    ClassicalNativeTrace,
    ClassicalPublicEnvironment,
    GoldilocksElement,
    verify_native_trace,
)
from .oracle_construction import (
    OracleCommitmentCapability,
    OracleCommitmentConstructionDeclaration,
    OracleCommitmentStaticMaps,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    SemanticId,
    affirmative,
    encode_term,
    kind_mismatch,
    malformed,
    refused,
    semantic_id,
)


def _semantic_ref(value: SemanticId) -> dict[str, Any]:
    if not isinstance(value, SemanticId):
        raise malformed(
            "classical-relations:formation",
            "FRI-IOR-CLASSICAL-RELATION-001",
            "a Relations coordinate requires a SemanticId",
        )
    return value.to_term()


class DistanceMetric(str, Enum):
    RELATIVE_HAMMING = "RelativeHammingDistance"


class ProximityEvaluationStatus(str, Enum):
    NOT_EVALUATED = "NotEvaluated"


class OuterRelationPremise(str, Enum):
    ACCEPTING_EXECUTION = "AcceptingExecution"
    UNEVALUATED_PROXIMITY_RESIDUAL = "UnevaluatedProximityResidual"


@dataclass(frozen=True, slots=True)
class ExactReedSolomonProximityRelation:
    """One exact close/far relation schema for the selected theorem question."""

    profile_id: SemanticId
    field_size: int
    initial_domain_order: int
    degree_bound_exclusive: int
    distance_metric: DistanceMetric
    distance_threshold_numerator: int
    distance_threshold_denominator: int

    def __post_init__(self) -> None:
        if self.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity:
            raise malformed(
                "classical-relations:relation-formation",
                "FRI-IOR-CLASSICAL-RELATION-002",
                "the relation must bind the exact classical FRI profile",
            )
        if (
            self.field_size != GOLDILOCKS_MODULUS
            or self.initial_domain_order != DOMAIN_ORDERS[0]
            or self.degree_bound_exclusive != DEGREE_BOUNDS[0]
            or self.distance_metric is not DistanceMetric.RELATIVE_HAMMING
            or self.distance_threshold_numerator != 1
            or self.distance_threshold_denominator != 2
        ):
            raise malformed(
                "classical-relations:relation-formation",
                "FRI-IOR-CLASSICAL-RELATION-003",
                "the selected relation parameters are exact and closed",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "profile_id": _semantic_ref(self.profile_id),
            "code_family": "reed-solomon-evaluation-code",
            "field_size": self.field_size,
            "initial_domain_order": self.initial_domain_order,
            "degree_bound_exclusive": self.degree_bound_exclusive,
            "distance_metric": self.distance_metric.value,
            "distance_threshold": {
                "numerator": self.distance_threshold_numerator,
                "denominator": self.distance_threshold_denominator,
            },
            "positive_meaning": "oracle-is-within-threshold-of-the-code",
            "far_instance_meaning": "oracle-is-delta-far-from-the-code",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-definition",
            "fri-ior.classical-relations.rs-proximity.v1",
            self.to_term(),
        )


EXACT_RS_PROXIMITY_RELATION = ExactReedSolomonProximityRelation(
    EXACT_CLASSICAL_FRI_PROFILE.identity,
    GOLDILOCKS_MODULUS,
    DOMAIN_ORDERS[0],
    DEGREE_BOUNDS[0],
    DistanceMetric.RELATIVE_HAMMING,
    1,
    2,
)


@dataclass(frozen=True, slots=True)
class ClassicalRelationStatementOccurrence:
    """The Statement coordinate projected from one native public environment."""

    public_environment: ClassicalPublicEnvironment

    def __post_init__(self) -> None:
        if type(self.public_environment) is not ClassicalPublicEnvironment:
            raise malformed(
                "classical-relations:statement-formation",
                "FRI-IOR-CLASSICAL-RELATION-004",
                "the Statement occurrence must be projected from a formed public environment",
            )
        if self.public_environment.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity:
            raise malformed(
                "classical-relations:statement-formation",
                "FRI-IOR-CLASSICAL-RELATION-005",
                "the Statement must bind the exact classical profile",
            )
        encode_term(self.to_term())

    @property
    def profile_id(self) -> SemanticId:
        return self.public_environment.profile_id

    @property
    def public_environment_id(self) -> SemanticId:
        return self.public_environment.identity

    @property
    def statement_coordinate_id(self) -> SemanticId:
        return self.public_environment.statement_coordinate_id

    @property
    def canonical_statement(self) -> bytes:
        return self.public_environment.statement

    def to_term(self) -> dict[str, Any]:
        return {
            "profile_id": _semantic_ref(self.profile_id),
            "public_environment_id": _semantic_ref(self.public_environment_id),
            "statement_coordinate_id": _semantic_ref(
                self.statement_coordinate_id
            ),
            "visibility": "PublicInstance",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-statement-occurrence",
            "fri-ior.classical-relations.statement.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ExactRsProximityRelationInstance:
    relation_id: SemanticId
    statement_id: SemanticId
    public_environment_id: SemanticId
    statement_coordinate_id: SemanticId
    initial_oracle_material_id: SemanticId

    def __post_init__(self) -> None:
        if self.relation_id != EXACT_RS_PROXIMITY_RELATION.identity:
            raise malformed(
                "classical-relations:instance-formation",
                "FRI-IOR-CLASSICAL-RELATION-006",
                "the instance requires the exact RS proximity definition",
            )
        for value in (
            self.statement_id,
            self.public_environment_id,
            self.statement_coordinate_id,
            self.initial_oracle_material_id,
        ):
            _semantic_ref(value)
        if (
            self.public_environment_id.subject_kind
            != "classical-fri-public-environment"
            or self.statement_coordinate_id.subject_kind
            != "classical-fri-public-environment-coordinate"
        ):
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "classical-relations:instance-formation",
                "FRI-IOR-CLASSICAL-RELATION-028",
                "the instance requires exact public-environment Statement coordinates",
            )
        if self.initial_oracle_material_id.subject_kind != "classical-fri-logical-oracle":
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "classical-relations:instance-formation",
                "FRI-IOR-CLASSICAL-RELATION-007",
                "the instance requires an initial logical-oracle identity",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "relation_id": _semantic_ref(self.relation_id),
            "statement_id": _semantic_ref(self.statement_id),
            "public_environment_id": _semantic_ref(self.public_environment_id),
            "statement_coordinate_id": _semantic_ref(
                self.statement_coordinate_id
            ),
            "initial_oracle_material_id": _semantic_ref(
                self.initial_oracle_material_id
            ),
            "satisfaction_status": ProximityEvaluationStatus.NOT_EVALUATED.value,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-instance",
            "fri-ior.classical-relations.rs-instance.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ClassicalProtocolRelationBinding:
    relation_instance_id: SemanticId
    statement_occurrence_id: SemanticId
    public_environment_id: SemanticId
    statement_coordinate_id: SemanticId
    native_core_id: SemanticId
    initial_oracle_occurrence_id: SemanticId

    def __post_init__(self) -> None:
        for value in (
            self.relation_instance_id,
            self.statement_occurrence_id,
            self.public_environment_id,
            self.statement_coordinate_id,
            self.native_core_id,
            self.initial_oracle_occurrence_id,
        ):
            _semantic_ref(value)
        if self.native_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity:
            raise malformed(
                "classical-relations:binding-formation",
                "FRI-IOR-CLASSICAL-RELATION-008",
                "the relation binding requires the exact native Core",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "relation_instance_id": _semantic_ref(self.relation_instance_id),
            "statement_occurrence_id": _semantic_ref(self.statement_occurrence_id),
            "public_environment_id": _semantic_ref(self.public_environment_id),
            "statement_coordinate_id": _semantic_ref(
                self.statement_coordinate_id
            ),
            "native_core_id": _semantic_ref(self.native_core_id),
            "initial_oracle_occurrence_id": _semantic_ref(
                self.initial_oracle_occurrence_id
            ),
            "oracle_role": "OracleStatement:G0",
            "statement_role": "PublicEnvironment:Statement",
            "value_relation": "SameExactValue",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-protocol-binding",
            "fri-ior.classical-relations.protocol-binding.v1",
            self.to_term(),
        )


def form_exact_rs_relation_instance_and_binding(
    statement: object,
    initial_oracle: object,
) -> tuple[ExactRsProximityRelationInstance, ClassicalProtocolRelationBinding]:
    if type(statement) is not ClassicalRelationStatementOccurrence:
        raise malformed(
            "classical-relations:instance-binding-formation",
            "FRI-IOR-CLASSICAL-RELATION-009",
            "instance formation requires a classical Statement occurrence",
        )
    if (
        type(initial_oracle) is not ClassicalLogicalOracle
        or initial_oracle.layer != 0
        or initial_oracle.origin != "InitialOracle"
    ):
        raise malformed(
            "classical-relations:instance-binding-formation",
            "FRI-IOR-CLASSICAL-RELATION-010",
            "instance formation requires the exact initial logical oracle",
        )
    instance = ExactRsProximityRelationInstance(
        EXACT_RS_PROXIMITY_RELATION.identity,
        statement.identity,
        statement.public_environment_id,
        statement.statement_coordinate_id,
        initial_oracle.identity,
    )
    binding = ClassicalProtocolRelationBinding(
        instance.identity,
        statement.identity,
        statement.public_environment_id,
        statement.statement_coordinate_id,
        EXACT_CLASSICAL_NATIVE_CORE.identity,
        initial_oracle.identity,
    )
    return instance, binding


_INITIAL_GROUNDING_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedInitialOracleGrounding:
    instance_id: SemanticId
    binding_id: SemanticId
    native_trace_id: SemanticId
    public_environment_id: SemanticId
    statement_coordinate_id: SemanticId
    initial_oracle_material_id: SemanticId

    def __init__(
        self,
        instance_id: SemanticId,
        binding_id: SemanticId,
        native_trace_id: SemanticId,
        public_environment_id: SemanticId,
        statement_coordinate_id: SemanticId,
        initial_oracle_material_id: SemanticId,
        *,
        _token: object,
    ) -> None:
        if _token is not _INITIAL_GROUNDING_TOKEN:
            raise malformed(
                "classical-relations:initial-grounding-formation",
                "FRI-IOR-CLASSICAL-RELATION-011",
                "an initial-oracle grounding is checker-issued",
            )
        object.__setattr__(self, "instance_id", instance_id)
        object.__setattr__(self, "binding_id", binding_id)
        object.__setattr__(self, "native_trace_id", native_trace_id)
        object.__setattr__(self, "public_environment_id", public_environment_id)
        object.__setattr__(self, "statement_coordinate_id", statement_coordinate_id)
        object.__setattr__(
            self,
            "initial_oracle_material_id",
            initial_oracle_material_id,
        )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "instance_id": _semantic_ref(self.instance_id),
            "binding_id": _semantic_ref(self.binding_id),
            "native_trace_id": _semantic_ref(self.native_trace_id),
            "public_environment_id": _semantic_ref(self.public_environment_id),
            "statement_coordinate_id": _semantic_ref(
                self.statement_coordinate_id
            ),
            "initial_oracle_material_id": _semantic_ref(
                self.initial_oracle_material_id
            ),
            "grounding_law": (
                "same-exact-native-public-environment-statement-and-"
                "initial-logical-oracle-material"
            ),
            "evaluation_surface": "RawNativeTraceInitialOracle",
            "durable_required_view": (
                "PirOwnedPurposeSpecificConfidentialOracleView"
            ),
            "durable_promotion_ready": False,
            "establishes_proximity": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-initial-oracle-grounding",
            "fri-ior.classical-relations.initial-oracle-grounding.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class InitialOracleGroundingAdmission:
    result: CheckResult
    checked: CheckedInitialOracleGrounding | None


def check_initial_oracle_grounding(
    instance: object,
    binding: object,
    trace: object,
) -> InitialOracleGroundingAdmission:
    boundary = "classical-relations:initial-oracle-grounding"
    if (
        type(instance) is not ExactRsProximityRelationInstance
        or type(binding) is not ClassicalProtocolRelationBinding
        or type(trace) is not ClassicalNativeTrace
    ):
        return InitialOracleGroundingAdmission(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-012",
                "grounding requires exact instance, binding, and trace carriers",
            ),
            None,
        )
    initial_oracle = trace.oracles[0]
    expected_statement = ClassicalRelationStatementOccurrence(
        trace.public_environment
    )
    if (
        binding.relation_instance_id != instance.identity
        or binding.statement_occurrence_id != instance.statement_id
        or instance.statement_id != expected_statement.identity
        or binding.public_environment_id != trace.public_environment.identity
        or instance.public_environment_id != trace.public_environment.identity
        or binding.statement_coordinate_id
        != trace.public_environment.statement_coordinate_id
        or instance.statement_coordinate_id
        != trace.public_environment.statement_coordinate_id
        or binding.native_core_id != trace.native_core_id
        or binding.initial_oracle_occurrence_id != initial_oracle.identity
        or instance.initial_oracle_material_id != initial_oracle.identity
    ):
        return InitialOracleGroundingAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-013",
                "the relation instance, binding, and trace name different public-environment or initial-oracle coordinates",
            ),
            None,
        )
    checked = CheckedInitialOracleGrounding(
        instance.identity,
        binding.identity,
        trace.identity,
        trace.public_environment.identity,
        trace.public_environment.statement_coordinate_id,
        initial_oracle.identity,
        _token=_INITIAL_GROUNDING_TOKEN,
    )
    return InitialOracleGroundingAdmission(
        affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-RELATION-100",
            "the relation OracleStatement is grounded to exact native G0 material",
            subject=checked.identity,
            public_environment_id=trace.public_environment.identity,
            statement_coordinate_id=(
                trace.public_environment.statement_coordinate_id
            ),
            evaluation_surface="RawNativeTraceInitialOracle",
            durable_required_view=(
                "PirOwnedPurposeSpecificConfidentialOracleView"
            ),
            durable_promotion_ready=False,
            establishes_proximity=False,
        ),
        checked,
    )


@dataclass(frozen=True, slots=True)
class ClassicalConstructionRelationView:
    construction_id: SemanticId
    source_core_id: SemanticId
    target_core_id: SemanticId
    public_environment_map_id: SemanticId
    publication_map_id: SemanticId
    fresh_coin_map_id: SemanticId
    query_draw_map_id: SemanticId
    answer_opening_map_id: SemanticId
    scalar_terminal_map_id: SemanticId
    check_map_id: SemanticId
    outcome_map_id: SemanticId
    public_environment_coordinates: int
    root_publications: int
    query_draws: int
    logical_query_occurrences: int

    def __post_init__(self) -> None:
        for value in (
            self.construction_id,
            self.source_core_id,
            self.target_core_id,
            self.public_environment_map_id,
            self.publication_map_id,
            self.fresh_coin_map_id,
            self.query_draw_map_id,
            self.answer_opening_map_id,
            self.scalar_terminal_map_id,
            self.check_map_id,
            self.outcome_map_id,
        ):
            _semantic_ref(value)
        if (
            self.source_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity
            or self.target_core_id != EXACT_CLASSICAL_COMMITTED_CORE.identity
            or self.public_environment_coordinates != 2
            or self.root_publications != FOLD_ROUNDS
            or self.query_draws != QUERY_REPETITIONS
            or self.logical_query_occurrences != LAYER_QUERY_OCCURRENCES
        ):
            raise malformed(
                "classical-relations:construction-view-formation",
                "FRI-IOR-CLASSICAL-RELATION-014",
                "the construction view must expose three roots and twelve occurrences",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "construction_id": _semantic_ref(self.construction_id),
            "source_core_id": _semantic_ref(self.source_core_id),
            "target_core_id": _semantic_ref(self.target_core_id),
            "public_environment_map_id": _semantic_ref(
                self.public_environment_map_id
            ),
            "publication_map_id": _semantic_ref(self.publication_map_id),
            "fresh_coin_map_id": _semantic_ref(self.fresh_coin_map_id),
            "query_draw_map_id": _semantic_ref(self.query_draw_map_id),
            "answer_opening_map_id": _semantic_ref(self.answer_opening_map_id),
            "scalar_terminal_map_id": _semantic_ref(self.scalar_terminal_map_id),
            "check_map_id": _semantic_ref(self.check_map_id),
            "outcome_map_id": _semantic_ref(self.outcome_map_id),
            "public_environment_coordinates": self.public_environment_coordinates,
            "root_publications": self.root_publications,
            "query_draws": self.query_draws,
            "logical_query_occurrences": self.logical_query_occurrences,
            "physical-opening-deduplication": "preserves-logical-multiplicity",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-construction-view",
            "fri-ior.classical-relations.construction-view.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ConstructionRelationViewAdmission:
    result: CheckResult
    view: ClassicalConstructionRelationView | None


def _map_identity(label: str, value: Any) -> SemanticId:
    return semantic_id(
        "oracle-construction-map",
        f"fri-ior.classical-relations.{label}.v1",
        value.to_term()
        if hasattr(value, "to_term")
        else [item.to_term() for item in value],
    )


def check_construction_relation_view(
    capability: object,
) -> ConstructionRelationViewAdmission:
    """Read one admitted stable subject through its live capability.

    A run receipt, inert construction ID, or caller-authored declaration is
    rejected at this boundary.  The returned view contains no process-local
    authority or result reference.
    """

    boundary = "classical-relations:construction-view"
    if type(capability) is not OracleCommitmentCapability:
        return ConstructionRelationViewAdmission(
            kind_mismatch(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-022",
                "the construction slot requires a live oracle-construction capability",
            ),
            None,
        )
    subject = capability.construction_subject
    checked = capability.checked_construction
    maps = checked.maps
    if (
        type(subject) is not OracleCommitmentConstructionDeclaration
        or type(maps) is not OracleCommitmentStaticMaps
        or capability.construction_id != subject.identity
        or checked.construction_id != subject.identity
        or checked.construction_subject is not subject
        or checked.source_profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity
        or checked.source_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity
        or checked.target_core_id != EXACT_CLASSICAL_COMMITTED_CORE.identity
        or checked.maps != subject.maps
    ):
        return ConstructionRelationViewAdmission(
            kind_mismatch(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-023",
                "the live capability does not expose the exact admitted subject and maps",
            ),
            None,
        )
    if (
        len(maps.public_environment_map) != 2
        or tuple(item.semantic_purpose for item in maps.public_environment_map)
        != ("Statement", "ApplicationContext")
        or len(maps.publication_map) != FOLD_ROUNDS
        or len(maps.fresh_coin_map) != FOLD_ROUNDS
        or len(maps.query_draw_map) != QUERY_REPETITIONS
        or len(maps.answer_opening_map) != LAYER_QUERY_OCCURRENCES
        or tuple(item.occurrence_ordinal for item in maps.answer_opening_map)
        != tuple(range(LAYER_QUERY_OCCURRENCES))
        or tuple(
            (item.draw_ordinal, item.layer) for item in maps.answer_opening_map
        )
        != tuple(
            (draw, layer)
            for draw in range(QUERY_REPETITIONS)
            for layer in range(FOLD_ROUNDS)
        )
        or maps.scalar_terminal_map.value_type != "GoldilocksElement"
    ):
        return ConstructionRelationViewAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-024",
                "the construction does not expose the exact total three-root/twelve-occurrence maps",
            ),
            None,
        )
    view = ClassicalConstructionRelationView(
        subject.identity,
        subject.source_core_id,
        subject.target_core_id,
        _map_identity("public-environment-map", maps.public_environment_map),
        _map_identity("publication-map", maps.publication_map),
        _map_identity("fresh-coin-map", maps.fresh_coin_map),
        _map_identity("query-draw-map", maps.query_draw_map),
        _map_identity("answer-opening-map", maps.answer_opening_map),
        _map_identity("scalar-terminal-map", maps.scalar_terminal_map),
        _map_identity("check-map", maps.check_map),
        _map_identity("outcome-map", maps.outcome_map),
        len(maps.public_environment_map),
        len(maps.publication_map),
        len(maps.query_draw_map),
        len(maps.answer_opening_map),
    )
    return ConstructionRelationViewAdmission(
        affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-RELATION-101",
            "the stable construction exposes exact Relations map coordinates",
            subject=view.identity,
            construction_id=subject.identity,
            public_environment_coordinates=len(maps.public_environment_map),
            root_publications=FOLD_ROUNDS,
            query_draws=QUERY_REPETITIONS,
            logical_query_occurrences=LAYER_QUERY_OCCURRENCES,
            establishes_binding=False,
            establishes_proximity=False,
        ),
        view,
    )


@dataclass(frozen=True, slots=True)
class ClassicalTerminalResidual:
    relation_instance_id: SemanticId
    binding_id: SemanticId
    native_trace_id: SemanticId
    construction_view_id: SemanticId
    terminal_scalar: GoldilocksElement
    execution_terminal: str
    proximity_status: ProximityEvaluationStatus = field(
        default=ProximityEvaluationStatus.NOT_EVALUATED,
        init=False,
    )

    def __post_init__(self) -> None:
        for value in (
            self.relation_instance_id,
            self.binding_id,
            self.native_trace_id,
            self.construction_view_id,
        ):
            _semantic_ref(value)
        if not isinstance(self.terminal_scalar, GoldilocksElement):
            raise malformed(
                "classical-relations:residual-formation",
                "FRI-IOR-CLASSICAL-RELATION-015",
                "the exact residual requires one scalar terminal",
            )
        if self.execution_terminal != "Accept":
            raise malformed(
                "classical-relations:residual-formation",
                "FRI-IOR-CLASSICAL-RELATION-016",
                "this residual is formed only after protocol acceptance",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "relation_instance_id": _semantic_ref(self.relation_instance_id),
            "binding_id": _semantic_ref(self.binding_id),
            "native_trace_id": _semantic_ref(self.native_trace_id),
            "construction_view_id": _semantic_ref(self.construction_view_id),
            "terminal_scalar": self.terminal_scalar.to_term(),
            "execution_terminal": self.execution_terminal,
            "proximity_status": self.proximity_status.value,
            "establishes_proximity": False,
            "establishes_outer_computation_relation": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-proximity-residual",
            "fri-ior.classical-relations.scalar-terminal-residual.v1",
            self.to_term(),
        )


_RELATION_GROUNDING_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedClassicalRelationGrounding:
    instance_id: SemanticId
    binding_id: SemanticId
    initial_grounding_id: SemanticId
    construction_view_id: SemanticId
    terminal_residual: ClassicalTerminalResidual

    def __init__(
        self,
        instance_id: SemanticId,
        binding_id: SemanticId,
        initial_grounding_id: SemanticId,
        construction_view_id: SemanticId,
        terminal_residual: ClassicalTerminalResidual,
        *,
        _token: object,
    ) -> None:
        if _token is not _RELATION_GROUNDING_TOKEN:
            raise malformed(
                "classical-relations:grounding-formation",
                "FRI-IOR-CLASSICAL-RELATION-025",
                "a complete relation grounding is checker-issued",
            )
        object.__setattr__(self, "instance_id", instance_id)
        object.__setattr__(self, "binding_id", binding_id)
        object.__setattr__(self, "initial_grounding_id", initial_grounding_id)
        object.__setattr__(self, "construction_view_id", construction_view_id)
        object.__setattr__(self, "terminal_residual", terminal_residual)
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "instance_id": _semantic_ref(self.instance_id),
            "binding_id": _semantic_ref(self.binding_id),
            "initial_grounding_id": _semantic_ref(self.initial_grounding_id),
            "construction_view_id": _semantic_ref(self.construction_view_id),
            "terminal_residual": self.terminal_residual.to_term(),
            "scope": "one-accepted-native-execution-plus-stable-construction-view",
            "nonclaims": [
                "reed-solomon-proximity",
                "outer-computation-relation",
                "commitment-binding-hiding-or-extraction",
                "theorem-truth-applicability-or-security",
            ],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-relations-grounding",
            "fri-ior.classical-relations.grounding.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ClassicalRelationGroundingAdmission:
    result: CheckResult
    checked: CheckedClassicalRelationGrounding | None


def check_classical_relation_grounding(
    instance: object,
    binding: object,
    trace: object,
    initial_grounding: object,
    construction_capability: object,
) -> ClassicalRelationGroundingAdmission:
    boundary = "classical-relations:grounding"
    if (
        type(instance) is not ExactRsProximityRelationInstance
        or type(binding) is not ClassicalProtocolRelationBinding
        or type(trace) is not ClassicalNativeTrace
        or type(initial_grounding) is not CheckedInitialOracleGrounding
    ):
        return ClassicalRelationGroundingAdmission(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-026",
                "complete grounding requires exact relation and native-run carriers",
            ),
            None,
        )
    if (
        initial_grounding.instance_id != instance.identity
        or initial_grounding.binding_id != binding.identity
        or initial_grounding.native_trace_id != trace.identity
    ):
        return ClassicalRelationGroundingAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-027",
                "the supplied initial grounding belongs to different coordinates",
            ),
            None,
        )
    view_admission = check_construction_relation_view(construction_capability)
    if view_admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
        return ClassicalRelationGroundingAdmission(view_admission.result, None)
    if view_admission.view is None:
        raise RuntimeError("affirmative construction view omitted its subject")
    native_acceptance = verify_native_trace(trace)
    if native_acceptance.outcome is not OutcomeClass.AFFIRMATIVE:
        return ClassicalRelationGroundingAdmission(native_acceptance, None)
    residual = ClassicalTerminalResidual(
        instance.identity,
        binding.identity,
        trace.identity,
        view_admission.view.identity,
        trace.terminal_scalar,
        "Accept",
    )
    checked = CheckedClassicalRelationGrounding(
        instance.identity,
        binding.identity,
        initial_grounding.identity,
        view_admission.view.identity,
        residual,
        _token=_RELATION_GROUNDING_TOKEN,
    )
    return ClassicalRelationGroundingAdmission(
        affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-RELATION-102",
            "the accepted native execution is grounded to the exact relation and stable construction view",
            subject=checked.identity,
            protocol_terminal="Accept",
            proximity_status=ProximityEvaluationStatus.NOT_EVALUATED.value,
            establishes_proximity=False,
            establishes_outer_computation_relation=False,
        ),
        checked,
    )


@dataclass(frozen=True, slots=True)
class OuterRelationInferenceRequest:
    residual: ClassicalTerminalResidual
    outer_relation_id: SemanticId
    premise: OuterRelationPremise

    def __post_init__(self) -> None:
        if type(self.residual) is not ClassicalTerminalResidual:
            raise malformed(
                "classical-relations:outer-inference-formation",
                "FRI-IOR-CLASSICAL-RELATION-017",
                "outer inference requires the exact residual carrier",
            )
        _semantic_ref(self.outer_relation_id)
        if not isinstance(self.premise, OuterRelationPremise):
            raise malformed(
                "classical-relations:outer-inference-formation",
                "FRI-IOR-CLASSICAL-RELATION-018",
                "outer inference requires a typed premise",
            )


def infer_outer_computation_relation(candidate: object) -> CheckResult:
    boundary = "classical-relations:outer-computation-inference"
    if type(candidate) is not OuterRelationInferenceRequest:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-CLASSICAL-RELATION-019",
            "outer inference requires a formed request",
        )
    if candidate.outer_relation_id.subject_kind != "outer-computation-relation":
        return kind_mismatch(
            boundary,
            "FRI-IOR-CLASSICAL-RELATION-020",
            "the request names a wrong-kind outer relation",
        )
    return refused(
        boundary,
        "FRI-IOR-CLASSICAL-RELATION-021",
        "FRI acceptance and an unevaluated proximity residual do not establish an outer computation relation",
    )


__all__ = [
    "CheckedClassicalRelationGrounding",
    "CheckedInitialOracleGrounding",
    "ClassicalConstructionRelationView",
    "ClassicalProtocolRelationBinding",
    "ClassicalRelationGroundingAdmission",
    "ClassicalRelationStatementOccurrence",
    "ClassicalTerminalResidual",
    "ConstructionRelationViewAdmission",
    "DistanceMetric",
    "EXACT_RS_PROXIMITY_RELATION",
    "ExactReedSolomonProximityRelation",
    "ExactRsProximityRelationInstance",
    "InitialOracleGroundingAdmission",
    "OuterRelationInferenceRequest",
    "OuterRelationPremise",
    "ProximityEvaluationStatus",
    "check_classical_relation_grounding",
    "check_construction_relation_view",
    "check_initial_oracle_grounding",
    "form_exact_rs_relation_instance_and_binding",
    "infer_outer_computation_relation",
]
