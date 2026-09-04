"""Bounded Relations pressure instruments for the exact classical FRI control.

The module grounds the selected public statement and initial logical oracle,
then consumes a reusable PIR-owned oracle-commitment construction view.  The
initial material comparison requires independent live Relations assignment
authority and a purpose-bound PIR confidential view issued only from causal
generation.  An accepting finite execution leaves Reed--Solomon proximity
unevaluated and can never establish an outer computation relation.  Neither a
raw trace nor a portable material-derived identity is an authority surface.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping

from .classical import (
    DEGREE_BOUNDS,
    DOMAIN_ORDERS,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID,
    EXACT_CLASSICAL_NATIVE_CORE,
    EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID,
    EXACT_NATIVE_TERMINAL_COORDINATE_ID,
    FOLD_ROUNDS,
    GOLDILOCKS_MODULUS,
    LAYER_QUERY_OCCURRENCES,
    PUBLIC_ENVIRONMENT_SCHEMA,
    QUERY_REPETITIONS,
    ClassicalPublicEnvironment,
    GoldilocksElement,
)
from .confidential_oracle import (
    CausalNativeRunFact,
    CausalNativeExecutionAuthority,
    ConfidentialInitialOracleDisclosurePolicy,
    ConfidentialInitialOracleViewCapability,
    EXACT_INITIAL_ORACLE_COORDINATE_ID,
    InitialOracleSupplyRef,
    NativeInvocationRef,
    _has_live_causal_execution_authority,
    _read_causal_execution_binding,
    _read_confidential_initial_oracle_view,
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


class OracleMaterialAgreementOutcome(str, Enum):
    """Semantic result of the confidential whole-carrier operation."""

    AFFIRMATIVE = "Affirmative"
    NEGATIVE = "Negative"
    CANNOT_ANSWER = "CannotAnswer"
    KIND_MISMATCH = "KindMismatch"
    MALFORMED = "Malformed"
    REFUSED = "Refused"


@dataclass(frozen=True, slots=True)
class OracleMaterialAgreementResult:
    """Local qualified result; it never transports either compared carrier."""

    outcome: OracleMaterialAgreementOutcome
    boundary: str
    code: str
    detail: str
    subject: SemanticId | None = None
    evidence: Mapping[str, Any] = field(default_factory=dict)

    def to_term(self) -> dict[str, Any]:
        return {
            "outcome": self.outcome.value,
            "boundary": self.boundary,
            "code": self.code,
            "detail": self.detail,
            "subject": None if self.subject is None else self.subject.to_term(),
            "evidence": {
                key: value.to_term() if isinstance(value, SemanticId) else value
                for key, value in self.evidence.items()
            },
        }


class _OwnerLocalResult:
    __slots__ = ()

    def __copy__(self) -> None:
        raise TypeError("owner-local Relations authority cannot be copied")

    def __deepcopy__(self, memo: object) -> None:
        raise TypeError("owner-local Relations authority cannot be copied")

    def __reduce__(self) -> None:
        raise TypeError("owner-local Relations authority cannot be serialized")

    def __reduce_ex__(self, protocol: int) -> None:
        raise TypeError("owner-local Relations authority cannot be serialized")

    def __getstate__(self) -> None:
        raise TypeError("owner-local Relations authority has no portable state")


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


EXACT_RS_PROXIMITY_INTERFACE_ID = semantic_id(
    "relations-interface",
    "fri-ior.classical-relations.rs-interface.v1",
    {
        "relation_id": EXACT_RS_PROXIMITY_RELATION.identity.to_term(),
        "public_values": [
            {
                "ref": "statement",
                "value_type": "CanonicalTermBytes",
            }
        ],
        "oracle_material": [
            {
                "ref": "initial-oracle",
                "value_type": "GoldilocksElement[64]",
            }
        ],
        "phase_values": [],
    },
)

EXACT_RELATION_STATEMENT_ROLE_ID = semantic_id(
    "relations-public-role",
    "fri-ior.classical-relations.statement-role.v1",
    {
        "interface_id": EXACT_RS_PROXIMITY_INTERFACE_ID.to_term(),
        "ref": "statement",
        "value_type": "CanonicalTermBytes",
    },
)

EXACT_RELATION_INITIAL_ORACLE_ROLE_ID = semantic_id(
    "relations-oracle-role",
    "fri-ior.classical-relations.initial-oracle-role.v1",
    {
        "interface_id": EXACT_RS_PROXIMITY_INTERFACE_ID.to_term(),
        "ref": "initial-oracle",
        "value_type": "GoldilocksElement[64]",
    },
)

EXACT_NATIVE_STATEMENT_TARGET_ID = semantic_id(
    "classical-fri-protocol-statement-target",
    "fri-ior.classical-relations.protocol-statement-target.v1",
    {
        "protocol_id": EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID.to_term(),
        "native_core_id": EXACT_CLASSICAL_NATIVE_CORE.identity.to_term(),
        "public_environment_schema": PUBLIC_ENVIRONMENT_SCHEMA,
        "coordinate_ordinal": 0,
        "name": "statement",
        "semantic_purpose": "Statement",
        "visibility": "Public",
        "value_type": "CanonicalTermBytes",
    },
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
    interface_id: SemanticId
    public_statement: bytes

    def __post_init__(self) -> None:
        if self.interface_id != EXACT_RS_PROXIMITY_INTERFACE_ID:
            raise malformed(
                "classical-relations:instance-formation",
                "FRI-IOR-CLASSICAL-RELATION-006",
                "the instance requires the exact RS proximity Interface",
            )
        if (
            type(self.public_statement) is not bytes
            or not self.public_statement
            or len(self.public_statement) > 1 << 14
        ):
            raise malformed(
                "classical-relations:instance-formation",
                "FRI-IOR-CLASSICAL-RELATION-028",
                "the public Statement must be non-empty bounded canonical bytes",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "interface_id": _semantic_ref(self.interface_id),
            "public_values": {
                "statement": self.public_statement.hex(),
            },
            "oracle_public_bindings": {},
            "phase_values": {},
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-instance",
            "fri-ior.classical-relations.rs-instance.v2",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ClassicalProtocolRelationBinding:
    relation_interface_id: SemanticId
    relation_statement_role_id: SemanticId
    protocol_statement_target_id: SemanticId
    relation_initial_oracle_role_id: SemanticId
    protocol_id: SemanticId
    native_core_id: SemanticId
    initial_oracle_coordinate_id: SemanticId
    initial_oracle_fixation_coordinate_id: SemanticId

    def __post_init__(self) -> None:
        for value in (
            self.relation_interface_id,
            self.relation_statement_role_id,
            self.protocol_statement_target_id,
            self.relation_initial_oracle_role_id,
            self.protocol_id,
            self.native_core_id,
            self.initial_oracle_coordinate_id,
            self.initial_oracle_fixation_coordinate_id,
        ):
            _semantic_ref(value)
        if (
            self.relation_interface_id != EXACT_RS_PROXIMITY_INTERFACE_ID
            or self.relation_statement_role_id
            != EXACT_RELATION_STATEMENT_ROLE_ID
            or self.protocol_statement_target_id
            != EXACT_NATIVE_STATEMENT_TARGET_ID
            or self.relation_initial_oracle_role_id
            != EXACT_RELATION_INITIAL_ORACLE_ROLE_ID
        ):
            raise malformed(
                "classical-relations:binding-formation",
                "FRI-IOR-CLASSICAL-RELATION-007",
                "the relation binding requires the exact static Interface roles and Statement target",
            )
        if (
            self.protocol_id != EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID
            or self.native_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity
        ):
            raise malformed(
                "classical-relations:binding-formation",
                "FRI-IOR-CLASSICAL-RELATION-008",
                "the relation binding requires the exact native Fresh Protocol and Core",
            )
        if self.initial_oracle_coordinate_id != EXACT_INITIAL_ORACLE_COORDINATE_ID:
            raise malformed(
                "classical-relations:binding-formation",
                "FRI-IOR-CLASSICAL-RELATION-030",
                "the relation binding requires the static G0 Oracle coordinate",
            )
        if (
            self.initial_oracle_fixation_coordinate_id
            != EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID
        ):
            raise malformed(
                "classical-relations:binding-formation",
                "FRI-IOR-CLASSICAL-RELATION-040",
                "the relation binding requires the static G0 fixation coordinate",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "relation_interface_id": _semantic_ref(self.relation_interface_id),
            "relation_statement_role_id": _semantic_ref(
                self.relation_statement_role_id
            ),
            "protocol_statement_target_id": _semantic_ref(
                self.protocol_statement_target_id
            ),
            "relation_initial_oracle_role_id": _semantic_ref(
                self.relation_initial_oracle_role_id
            ),
            "protocol_id": _semantic_ref(self.protocol_id),
            "native_core_id": _semantic_ref(self.native_core_id),
            "initial_oracle_coordinate_id": _semantic_ref(
                self.initial_oracle_coordinate_id
            ),
            "initial_oracle_fixation_coordinate_id": _semantic_ref(
                self.initial_oracle_fixation_coordinate_id
            ),
            "oracle_target": "LogicalOracleTarget:G0",
            "value_relation": "SameExactValue",
            "instance_specific": False,
            "run_specific": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-protocol-binding",
            "fri-ior.classical-relations.protocol-binding.v2",
            self.to_term(),
        )


def form_exact_rs_relation_instance_and_binding(
    statement: object,
) -> tuple[ExactRsProximityRelationInstance, ClassicalProtocolRelationBinding]:
    if type(statement) is not ClassicalRelationStatementOccurrence:
        raise malformed(
            "classical-relations:instance-binding-formation",
            "FRI-IOR-CLASSICAL-RELATION-009",
            "instance formation requires a classical Statement occurrence",
        )
    instance = ExactRsProximityRelationInstance(
        EXACT_RS_PROXIMITY_INTERFACE_ID,
        statement.canonical_statement,
    )
    binding = ClassicalProtocolRelationBinding(
        EXACT_RS_PROXIMITY_INTERFACE_ID,
        EXACT_RELATION_STATEMENT_ROLE_ID,
        EXACT_NATIVE_STATEMENT_TARGET_ID,
        EXACT_RELATION_INITIAL_ORACLE_ROLE_ID,
        EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID,
        EXACT_CLASSICAL_NATIVE_CORE.identity,
        EXACT_INITIAL_ORACLE_COORDINATE_ID,
        EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID,
    )
    return instance, binding


def oracle_material_question_id(
    instance: ExactRsProximityRelationInstance,
    binding: ClassicalProtocolRelationBinding,
    statement: ClassicalRelationStatementOccurrence,
) -> SemanticId:
    """Return the public, occurrence-specific material-question coordinate."""

    if (
        type(instance) is not ExactRsProximityRelationInstance
        or type(binding) is not ClassicalProtocolRelationBinding
        or type(statement) is not ClassicalRelationStatementOccurrence
        or binding.relation_interface_id != instance.interface_id
        or instance.public_statement != statement.canonical_statement
    ):
        raise malformed(
            "classical-relations:oracle-material-question-formation",
            "FRI-IOR-CLASSICAL-RELATION-010",
            "the Oracle-material question requires one exact instance, static binding, and matching Statement occurrence",
        )
    return semantic_id(
        "relations-oracle-material-question",
        "fri-ior.classical-relations.oracle-material-question.v2",
        {
            "instance_id": instance.identity.to_term(),
            "binding_id": binding.identity.to_term(),
            "statement_occurrence_id": statement.identity.to_term(),
            "public_environment_id": statement.public_environment_id.to_term(),
            "statement_coordinate_id": statement.statement_coordinate_id.to_term(),
            "protocol_id": binding.protocol_id.to_term(),
            "oracle_coordinate_id": (
                binding.initial_oracle_coordinate_id.to_term()
            ),
            "fixation_coordinate_id": (
                binding.initial_oracle_fixation_coordinate_id.to_term()
            ),
            "comparison_scope": "WholeCarrier",
        },
    )


def form_exact_initial_oracle_disclosure_policy(
    instance: ExactRsProximityRelationInstance,
    binding: ClassicalProtocolRelationBinding,
    statement: ClassicalRelationStatementOccurrence,
) -> ConfidentialInitialOracleDisclosurePolicy:
    question_id = oracle_material_question_id(instance, binding, statement)
    consumer_id = semantic_id(
        "relations-confidential-view-consumer",
        "fri-ior.classical-relations.confidential-view-consumer.v1",
        {"question_id": question_id.to_term()},
    )
    purpose_id = semantic_id(
        "relations-confidential-view-purpose",
        "fri-ior.classical-relations.confidential-view-purpose.v1",
        {"question_id": question_id.to_term()},
    )
    return ConfidentialInitialOracleDisclosurePolicy(
        protocol_id=binding.protocol_id,
        native_core_id=binding.native_core_id,
        oracle_coordinate_id=binding.initial_oracle_coordinate_id,
        fixation_coordinate_id=(
            binding.initial_oracle_fixation_coordinate_id
        ),
        downstream_consumer_id=consumer_id,
        purpose_id=purpose_id,
    )


_RELATION_SECRET_TOKEN = object()
_RELATION_SECRET_CAPABILITY_TOKEN = object()


class RelationInitialOracleSecretAssignment(_OwnerLocalResult):
    """Independent Relations-side material bound to one causal occurrence."""

    __slots__ = (
        "_authority",
        "_instance_id",
        "_binding_id",
        "_statement_occurrence_id",
        "_statement_coordinate_id",
        "_consumer_id",
        "_purpose_id",
        "_protocol_id",
        "_native_core_id",
        "_public_environment_id",
        "_oracle_coordinate_id",
        "_fixation_coordinate_id",
        "_invocation_ref",
        "_supply_ref",
        "_values",
    )

    def __init__(
        self,
        instance: ExactRsProximityRelationInstance,
        binding: ClassicalProtocolRelationBinding,
        statement: ClassicalRelationStatementOccurrence,
        execution_authority: CausalNativeExecutionAuthority,
        values: tuple[GoldilocksElement, ...],
        *,
        _token: object,
    ) -> None:
        if _token is not _RELATION_SECRET_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "classical-relations:secret-assignment-formation",
                "FRI-IOR-CLASSICAL-RELATION-031",
                "a relation secret assignment requires the owner issuance path",
            )
        (
            protocol_id,
            native_core_id,
            public_environment_id,
            oracle_coordinate_id,
            fixation_coordinate_id,
            invocation_ref,
            supply_ref,
        ) = _read_causal_execution_binding(execution_authority)
        if (
            binding.relation_interface_id != instance.interface_id
            or instance.public_statement != statement.canonical_statement
            or statement.public_environment_id != public_environment_id
            or binding.protocol_id != protocol_id
            or binding.native_core_id != native_core_id
            or binding.initial_oracle_coordinate_id != oracle_coordinate_id
            or binding.initial_oracle_fixation_coordinate_id
            != fixation_coordinate_id
        ):
            raise ModelFailure(
                OutcomeClass.REFUSED,
                "classical-relations:secret-assignment-formation",
                "FRI-IOR-CLASSICAL-RELATION-032",
                "the assignment coordinates differ from the causal invocation",
            )
        if (
            type(values) is not tuple
            or len(values) != DOMAIN_ORDERS[0]
            or any(not isinstance(value, GoldilocksElement) for value in values)
        ):
            raise malformed(
                "classical-relations:secret-assignment-formation",
                "FRI-IOR-CLASSICAL-RELATION-033",
                "the relation assignment must contain the exact whole G0 carrier",
            )
        self._authority = _RELATION_SECRET_TOKEN
        self._instance_id = instance.identity
        self._binding_id = binding.identity
        self._statement_occurrence_id = statement.identity
        self._statement_coordinate_id = statement.statement_coordinate_id
        policy = form_exact_initial_oracle_disclosure_policy(
            instance,
            binding,
            statement,
        )
        self._consumer_id = policy.downstream_consumer_id
        self._purpose_id = policy.purpose_id
        self._protocol_id = protocol_id
        self._native_core_id = native_core_id
        self._public_environment_id = public_environment_id
        self._oracle_coordinate_id = oracle_coordinate_id
        self._fixation_coordinate_id = fixation_coordinate_id
        self._invocation_ref = invocation_ref
        self._supply_ref = supply_ref
        self._values = values

    def __repr__(self) -> str:
        return "RelationInitialOracleSecretAssignment(owner_local=True)"


class RelationInitialOracleSecretAssignmentCapability(_OwnerLocalResult):
    __slots__ = ("_authority", "_assignment")

    def __init__(
        self,
        assignment: RelationInitialOracleSecretAssignment,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _RELATION_SECRET_CAPABILITY_TOKEN
            or type(assignment) is not RelationInitialOracleSecretAssignment
            or assignment._authority is not _RELATION_SECRET_TOKEN
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "classical-relations:secret-capability-formation",
                "FRI-IOR-CLASSICAL-RELATION-034",
                "a secret capability requires the exact live assignment",
            )
        self._authority = _RELATION_SECRET_CAPABILITY_TOKEN
        self._assignment = assignment

    def __repr__(self) -> str:
        return "RelationInitialOracleSecretAssignmentCapability(owner_local=True)"


def issue_relation_initial_oracle_secret_assignment(
    instance: object,
    binding: object,
    statement: object,
    execution_authority: object,
    values: object,
) -> RelationInitialOracleSecretAssignmentCapability:
    if (
        type(instance) is not ExactRsProximityRelationInstance
        or type(binding) is not ClassicalProtocolRelationBinding
        or type(statement) is not ClassicalRelationStatementOccurrence
        or not _has_live_causal_execution_authority(execution_authority)
        or type(values) is not tuple
    ):
        raise ModelFailure(
            OutcomeClass.MISSING_DEPENDENCY,
            "classical-relations:secret-assignment-issuance",
            "FRI-IOR-CLASSICAL-RELATION-035",
            "secret issuance requires exact live instance, binding, Statement occurrence, and causal authority",
        )
    assignment = RelationInitialOracleSecretAssignment(
        instance,
        binding,
        statement,
        execution_authority,
        values,
        _token=_RELATION_SECRET_TOKEN,
    )
    return RelationInitialOracleSecretAssignmentCapability(
        assignment,
        _token=_RELATION_SECRET_CAPABILITY_TOKEN,
    )


_INITIAL_GROUNDING_TOKEN = object()
_INITIAL_GROUNDING_RESULT_REF_TOKEN = object()


class InitialOracleGroundingResultRef(_OwnerLocalResult):
    __slots__ = ("_authority",)

    def __init__(self, *, _token: object) -> None:
        if _token is not _INITIAL_GROUNDING_RESULT_REF_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "classical-relations:initial-grounding-ref-formation",
                "FRI-IOR-CLASSICAL-RELATION-036",
                "a grounding result reference is checker-issued",
            )
        self._authority = _INITIAL_GROUNDING_RESULT_REF_TOKEN

    def __repr__(self) -> str:
        return "InitialOracleGroundingResultRef(process_local=True)"


class CheckedInitialOracleGrounding(_OwnerLocalResult):
    """Completed whole-carrier comparison plus hidden live operation state."""

    __slots__ = (
        "instance_id",
        "binding_id",
        "statement_occurrence_id",
        "public_environment_id",
        "statement_coordinate_id",
        "protocol_id",
        "native_core_id",
        "initial_oracle_coordinate_id",
        "initial_oracle_fixation_coordinate_id",
        "policy_id",
        "outcome",
        "result_ref",
        "_authority",
        "_run_fact",
        "_invocation_ref",
        "_supply_ref",
    )

    def __init__(
        self,
        instance: ExactRsProximityRelationInstance,
        binding: ClassicalProtocolRelationBinding,
        statement: ClassicalRelationStatementOccurrence,
        policy_id: SemanticId,
        outcome: OracleMaterialAgreementOutcome,
        run_fact: CausalNativeRunFact,
        invocation_ref: NativeInvocationRef,
        supply_ref: InitialOracleSupplyRef,
        *,
        _token: object,
    ) -> None:
        if _token is not _INITIAL_GROUNDING_TOKEN:
            raise malformed(
                "classical-relations:initial-grounding-formation",
                "FRI-IOR-CLASSICAL-RELATION-011",
                "an initial-oracle grounding is checker-issued",
            )
        self.instance_id = instance.identity
        self.binding_id = binding.identity
        self.statement_occurrence_id = statement.identity
        self.public_environment_id = statement.public_environment_id
        self.statement_coordinate_id = statement.statement_coordinate_id
        self.protocol_id = binding.protocol_id
        self.native_core_id = binding.native_core_id
        self.initial_oracle_coordinate_id = binding.initial_oracle_coordinate_id
        self.initial_oracle_fixation_coordinate_id = (
            binding.initial_oracle_fixation_coordinate_id
        )
        self.policy_id = policy_id
        self.outcome = outcome
        self.result_ref = InitialOracleGroundingResultRef(
            _token=_INITIAL_GROUNDING_RESULT_REF_TOKEN
        )
        self._authority = _INITIAL_GROUNDING_TOKEN
        self._run_fact = run_fact
        self._invocation_ref = invocation_ref
        self._supply_ref = supply_ref
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "instance_id": _semantic_ref(self.instance_id),
            "binding_id": _semantic_ref(self.binding_id),
            "statement_occurrence_id": _semantic_ref(
                self.statement_occurrence_id
            ),
            "public_environment_id": _semantic_ref(self.public_environment_id),
            "statement_coordinate_id": _semantic_ref(
                self.statement_coordinate_id
            ),
            "protocol_id": _semantic_ref(self.protocol_id),
            "native_core_id": _semantic_ref(self.native_core_id),
            "initial_oracle_coordinate_id": _semantic_ref(
                self.initial_oracle_coordinate_id
            ),
            "initial_oracle_fixation_coordinate_id": _semantic_ref(
                self.initial_oracle_fixation_coordinate_id
            ),
            "policy_id": _semantic_ref(self.policy_id),
            "native_run_fact_id": _semantic_ref(self._run_fact.identity),
            "outcome": self.outcome.value,
            "grounding_law": "same-type-whole-carrier-equality",
            "evaluation_surface": "PurposeBoundCausalConfidentialOracleView",
            "material_serialized": False,
            "material_digest_serialized": False,
            "local_occurrence_serialized": False,
            "establishes_proximity": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "checked-initial-oracle-grounding",
            "fri-ior.classical-relations.initial-oracle-grounding.v3",
            self.to_term(),
        )

    def __repr__(self) -> str:
        return (
            "CheckedInitialOracleGrounding("
            f"outcome={self.outcome.value}, owner_local=True)"
        )


@dataclass(frozen=True, slots=True)
class InitialOracleGroundingAdmission:
    result: OracleMaterialAgreementResult
    checked: CheckedInitialOracleGrounding | None


def _material_result(
    outcome: OracleMaterialAgreementOutcome,
    code: str,
    detail: str,
    *,
    subject: SemanticId | None = None,
    **evidence: Any,
) -> OracleMaterialAgreementResult:
    return OracleMaterialAgreementResult(
        outcome,
        "classical-relations:initial-oracle-grounding",
        code,
        detail,
        subject,
        evidence,
    )


def check_initial_oracle_grounding(
    instance: object,
    binding: object,
    statement: object,
    relation_secret_capability: object,
    pir_view_capability: object,
) -> InitialOracleGroundingAdmission:
    if (
        type(instance) is not ExactRsProximityRelationInstance
        or type(binding) is not ClassicalProtocolRelationBinding
        or type(statement) is not ClassicalRelationStatementOccurrence
    ):
        return InitialOracleGroundingAdmission(
            _material_result(
                OracleMaterialAgreementOutcome.MALFORMED,
                "FRI-IOR-CLASSICAL-RELATION-012",
                "grounding requires exact instance, binding, and Statement carriers",
            ),
            None,
        )
    if relation_secret_capability is None or pir_view_capability is None:
        return InitialOracleGroundingAdmission(
            _material_result(
                OracleMaterialAgreementOutcome.CANNOT_ANSWER,
                "FRI-IOR-CLASSICAL-RELATION-037",
                "a required live whole-carrier authority is unavailable",
            ),
            None,
        )
    if (
        type(relation_secret_capability)
        is not RelationInitialOracleSecretAssignmentCapability
        or relation_secret_capability._authority
        is not _RELATION_SECRET_CAPABILITY_TOKEN
        or relation_secret_capability._assignment._authority
        is not _RELATION_SECRET_TOKEN
        or type(pir_view_capability)
        is not ConfidentialInitialOracleViewCapability
    ):
        return InitialOracleGroundingAdmission(
            _material_result(
                OracleMaterialAgreementOutcome.REFUSED,
                "FRI-IOR-CLASSICAL-RELATION-038",
                "caller-authored or wrong-kind values are not live comparison authority",
            ),
            None,
        )
    try:
        view = _read_confidential_initial_oracle_view(pir_view_capability)
    except ModelFailure:
        return InitialOracleGroundingAdmission(
            _material_result(
                OracleMaterialAgreementOutcome.REFUSED,
                "FRI-IOR-CLASSICAL-RELATION-038",
                "caller-authored or wrong-kind values are not live comparison authority",
            ),
            None,
        )
    assignment = relation_secret_capability._assignment
    if (
        binding.relation_interface_id != instance.interface_id
        or instance.public_statement != statement.canonical_statement
    ):
        return InitialOracleGroundingAdmission(
            _material_result(
                OracleMaterialAgreementOutcome.REFUSED,
                "FRI-IOR-CLASSICAL-RELATION-013",
                "the instance public values do not match the selected Statement occurrence",
            ),
            None,
        )
    expected_policy = form_exact_initial_oracle_disclosure_policy(
        instance,
        binding,
        statement,
    )
    if (
        binding.relation_interface_id != instance.interface_id
        or instance.public_statement != statement.canonical_statement
        or assignment._instance_id != instance.identity
        or assignment._binding_id != binding.identity
        or assignment._statement_occurrence_id != statement.identity
        or assignment._statement_coordinate_id
        != statement.statement_coordinate_id
        or assignment._consumer_id != expected_policy.downstream_consumer_id
        or assignment._purpose_id != expected_policy.purpose_id
        or assignment._protocol_id != binding.protocol_id
        or assignment._native_core_id != binding.native_core_id
        or assignment._public_environment_id != statement.public_environment_id
        or assignment._oracle_coordinate_id
        != binding.initial_oracle_coordinate_id
        or assignment._fixation_coordinate_id
        != binding.initial_oracle_fixation_coordinate_id
        or view._protocol_id != binding.protocol_id
        or view._native_core_id != binding.native_core_id
        or view._public_environment_id != statement.public_environment_id
        or view._oracle_coordinate_id != binding.initial_oracle_coordinate_id
        or view._fixation_coordinate_id
        != binding.initial_oracle_fixation_coordinate_id
        or view._policy.identity != expected_policy.identity
        or view._policy.downstream_consumer_id
        != expected_policy.downstream_consumer_id
        or view._policy.purpose_id != expected_policy.purpose_id
        or assignment._invocation_ref is not view._invocation_ref
        or assignment._supply_ref is not view._supply_ref
        or view._run_fact.protocol_id != binding.protocol_id
        or view._run_fact.native_core_id != binding.native_core_id
        or view._run_fact.public_environment_id != statement.public_environment_id
        or view._run_fact.initial_oracle_coordinate_id
        != binding.initial_oracle_coordinate_id
        or view._run_fact.initial_oracle_fixation_coordinate_id
        != binding.initial_oracle_fixation_coordinate_id
    ):
        return InitialOracleGroundingAdmission(
            _material_result(
                OracleMaterialAgreementOutcome.REFUSED,
                "FRI-IOR-CLASSICAL-RELATION-013",
                "the authorities belong to different coordinates, policy, invocation, or supply",
            ),
            None,
        )
    outcome = (
        OracleMaterialAgreementOutcome.AFFIRMATIVE
        if assignment._values == view._values
        else OracleMaterialAgreementOutcome.NEGATIVE
    )
    checked = CheckedInitialOracleGrounding(
        instance,
        binding,
        statement,
        expected_policy.identity,
        outcome,
        view._run_fact,
        view._invocation_ref,
        view._supply_ref,
        _token=_INITIAL_GROUNDING_TOKEN,
    )
    if outcome is OracleMaterialAgreementOutcome.AFFIRMATIVE:
        result = _material_result(
            OracleMaterialAgreementOutcome.AFFIRMATIVE,
            "FRI-IOR-CLASSICAL-RELATION-100",
            "the two authorized whole G0 carriers agree",
            subject=checked.identity,
            policy_id=expected_policy.identity,
            initial_oracle_coordinate_id=binding.initial_oracle_coordinate_id,
            material_serialized=False,
            material_digest_serialized=False,
            establishes_proximity=False,
        )
    else:
        result = _material_result(
            OracleMaterialAgreementOutcome.NEGATIVE,
            "FRI-IOR-CLASSICAL-RELATION-103",
            "the two authorized whole G0 carriers disagree",
            subject=checked.identity,
            policy_id=expected_policy.identity,
            initial_oracle_coordinate_id=binding.initial_oracle_coordinate_id,
            material_serialized=False,
            material_digest_serialized=False,
            establishes_proximity=False,
        )
    return InitialOracleGroundingAdmission(result, checked)


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
    initial_grounding_id: SemanticId
    protocol_id: SemanticId
    native_core_id: SemanticId
    public_environment_id: SemanticId
    initial_oracle_coordinate_id: SemanticId
    initial_oracle_fixation_coordinate_id: SemanticId
    terminal_occurrence_coordinate_id: SemanticId
    construction_view_id: SemanticId
    execution_terminal: str
    proximity_status: ProximityEvaluationStatus = field(
        default=ProximityEvaluationStatus.NOT_EVALUATED,
        init=False,
    )

    def __post_init__(self) -> None:
        for value in (
            self.relation_instance_id,
            self.binding_id,
            self.initial_grounding_id,
            self.protocol_id,
            self.native_core_id,
            self.public_environment_id,
            self.initial_oracle_coordinate_id,
            self.initial_oracle_fixation_coordinate_id,
            self.terminal_occurrence_coordinate_id,
            self.construction_view_id,
        ):
            _semantic_ref(value)
        if (
            self.protocol_id != EXACT_CLASSICAL_NATIVE_FRESH_PROTOCOL_ID
            or self.native_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity
            or self.initial_oracle_coordinate_id
            != EXACT_INITIAL_ORACLE_COORDINATE_ID
            or self.initial_oracle_fixation_coordinate_id
            != EXACT_INITIAL_ORACLE_FIXATION_COORDINATE_ID
            or self.terminal_occurrence_coordinate_id
            != EXACT_NATIVE_TERMINAL_COORDINATE_ID
        ):
            raise malformed(
                "classical-relations:residual-formation",
                "FRI-IOR-CLASSICAL-RELATION-015",
                "the residual requires exact value-free Protocol occurrence coordinates",
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
            "initial_grounding_id": _semantic_ref(self.initial_grounding_id),
            "protocol_id": _semantic_ref(self.protocol_id),
            "native_core_id": _semantic_ref(self.native_core_id),
            "public_environment_id": _semantic_ref(self.public_environment_id),
            "initial_oracle_coordinate_id": _semantic_ref(
                self.initial_oracle_coordinate_id
            ),
            "initial_oracle_fixation_coordinate_id": _semantic_ref(
                self.initial_oracle_fixation_coordinate_id
            ),
            "terminal_occurrence_coordinate_id": _semantic_ref(
                self.terminal_occurrence_coordinate_id
            ),
            "construction_view_id": _semantic_ref(self.construction_view_id),
            "execution_terminal": self.execution_terminal,
            "proximity_status": self.proximity_status.value,
            "terminal_value_serialized": False,
            "trace_identity_serialized": False,
            "establishes_proximity": False,
            "establishes_outer_computation_relation": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "relations-proximity-residual",
            "fri-ior.classical-relations.scalar-terminal-residual.v2",
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
    initial_grounding: object,
    construction_capability: object,
) -> ClassicalRelationGroundingAdmission:
    boundary = "classical-relations:grounding"
    if (
        type(instance) is not ExactRsProximityRelationInstance
        or type(binding) is not ClassicalProtocolRelationBinding
        or type(initial_grounding) is not CheckedInitialOracleGrounding
    ):
        return ClassicalRelationGroundingAdmission(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-026",
                "complete grounding requires exact relation and checked-result carriers",
            ),
            None,
        )
    if (
        initial_grounding.instance_id != instance.identity
        or initial_grounding.binding_id != binding.identity
        or initial_grounding._authority is not _INITIAL_GROUNDING_TOKEN
        or initial_grounding.result_ref._authority
        is not _INITIAL_GROUNDING_RESULT_REF_TOKEN
        or initial_grounding.outcome
        is not OracleMaterialAgreementOutcome.AFFIRMATIVE
    ):
        return ClassicalRelationGroundingAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-027",
                "the supplied initial grounding is not the matching live Affirmative result",
            ),
            None,
        )
    view_admission = check_construction_relation_view(construction_capability)
    if view_admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
        return ClassicalRelationGroundingAdmission(view_admission.result, None)
    if view_admission.view is None:
        raise RuntimeError("affirmative construction view omitted its subject")
    run_fact = initial_grounding._run_fact
    if (
        type(run_fact) is not CausalNativeRunFact
        or binding.relation_interface_id != instance.interface_id
        or run_fact.protocol_id != binding.protocol_id
        or run_fact.native_core_id != binding.native_core_id
        or run_fact.public_environment_id
        != initial_grounding.public_environment_id
        or run_fact.initial_oracle_coordinate_id
        != binding.initial_oracle_coordinate_id
        or run_fact.initial_oracle_fixation_coordinate_id
        != binding.initial_oracle_fixation_coordinate_id
        or run_fact.terminal_occurrence_coordinate_id
        != EXACT_NATIVE_TERMINAL_COORDINATE_ID
        or run_fact.execution_terminal != "Accept"
    ):
        return ClassicalRelationGroundingAdmission(
            refused(
                boundary,
                "FRI-IOR-CLASSICAL-RELATION-041",
                "the live checked result lacks the matching public Accept run fact",
            ),
            None,
        )
    residual = ClassicalTerminalResidual(
        instance.identity,
        binding.identity,
        initial_grounding.identity,
        binding.protocol_id,
        binding.native_core_id,
        initial_grounding.public_environment_id,
        binding.initial_oracle_coordinate_id,
        binding.initial_oracle_fixation_coordinate_id,
        EXACT_NATIVE_TERMINAL_COORDINATE_ID,
        view_admission.view.identity,
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
    "EXACT_NATIVE_STATEMENT_TARGET_ID",
    "EXACT_RELATION_INITIAL_ORACLE_ROLE_ID",
    "EXACT_RELATION_STATEMENT_ROLE_ID",
    "EXACT_RS_PROXIMITY_INTERFACE_ID",
    "EXACT_RS_PROXIMITY_RELATION",
    "ExactReedSolomonProximityRelation",
    "ExactRsProximityRelationInstance",
    "InitialOracleGroundingAdmission",
    "InitialOracleGroundingResultRef",
    "OracleMaterialAgreementOutcome",
    "OracleMaterialAgreementResult",
    "OuterRelationInferenceRequest",
    "OuterRelationPremise",
    "ProximityEvaluationStatus",
    "RelationInitialOracleSecretAssignment",
    "RelationInitialOracleSecretAssignmentCapability",
    "check_classical_relation_grounding",
    "check_construction_relation_view",
    "check_initial_oracle_grounding",
    "form_exact_initial_oracle_disclosure_policy",
    "form_exact_rs_relation_instance_and_binding",
    "infer_outer_computation_relation",
    "issue_relation_initial_oracle_secret_assignment",
    "oracle_material_question_id",
]
