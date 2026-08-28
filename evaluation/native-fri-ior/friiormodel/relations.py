"""Exact Relations grounding for the finite native FRI/IOR case.

This module checks one deliberately narrow correspondence seam.  It binds an
exact public statement and one initial logical-oracle material occurrence to
the native execution, names the two source construction inputs
and two target cap publications, and compares every selected native query
answer occurrence with the authenticated public opening used by the committed
verifier.

The result is not a commitment compiler, a commitment-binding judgment, or a
FRI theorem.  In particular, sampled execution acceptance leaves the
Reed--Solomon proximity proposition ``NotEvaluated`` and cannot establish an
outer computation relation.  Complete logical-oracle carriers are used only at
the live grounding boundary; portable terms contain typed semantic identities,
never oracle entries, source coefficients, unopened salts, or generation data.
The deterministic material identities are validation-only names: they leak
equality and permit offline confirmation of guessable material, so they are
not confidentiality devices.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from types import MappingProxyType
from typing import Any, ClassVar

from .committed import verify_committed_fri
from .native import (
    INITIAL_ORACLE_NAME,
    PROVER_ORACLE_NAME,
    LayerQueryAnswerOccurrence,
    LogicalOracle,
    NativeFriTrace,
    NativeOracleLayer,
    OracleOrigin,
    OraclePublicationMode,
    resolve_layer_query_answers,
    verify_native_trace,
)
from .profile import D0, EXACT_PROFILE, admit_exact_profile
from .proof import CommittedFriPublicInputs, PublicFriProof
from .subjects import COMMITMENT_COMPILATION_DECLARATION
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    SemanticId,
    affirmative,
    checker_failure,
    encode_term,
    kind_mismatch,
    malformed,
    refused,
    semantic_id,
    unsupported,
)
from .transcript import FiatShamirTranscript, derive_fiat_shamir_transcript


RELATION_STATEMENT_SCHEMA = "zkc.fri-ior.relation-statement-occurrence.v1"
INITIAL_ORACLE_BINDING_SCHEMA = "zkc.fri-ior.initial-oracle-material-binding.v1"
GROUNDING_REQUEST_SCHEMA = "zkc.fri-ior.relation-grounding-request.v1"
GROUNDING_RESULT_SCHEMA = "zkc.fri-ior.checked-relation-grounding.v1"


class FriOracleLayer(str, Enum):
    """The two source/target construction layers in canonical order."""

    INITIAL = "initial"
    FIRST_FOLD = "first-fold"


class RepresentationBoundary(str, Enum):
    """Exact boundaries whose representation relation is fixed here."""

    LOGICAL_ORACLE_PUBLICATION = "logical-oracle-to-publication-observation"
    LOGICAL_ORACLE_COMMITMENT_CAP = "logical-oracle-to-commitment-cap"


class RepresentationClass(str, Enum):
    """Classification names are not mutually coercible proof capabilities."""

    TOTAL_EQUIVALENCE = "TotalEquivalence"
    INJECTIVE_EMBEDDING = "InjectiveEmbedding"
    DIRECTIONAL_LOSSY_PROJECTION = "DirectionalLossyProjection"
    NON_ISOMORPHIC_CONSTRUCTION_RELATION = "NonIsomorphicConstructionRelation"
    SAME_EXACT_VALUE = "SameExactValue"


class ResidualStatus(str, Enum):
    """The only scientific-residual status produced by this package."""

    NOT_EVALUATED = "NotEvaluated"


class OuterInferencePremise(str, Enum):
    """Insufficient premises that a caller may try to overinterpret."""

    ACCEPTING_EXECUTION = "AcceptingExecution"
    FRI_PROXIMITY_RESIDUAL = "FriProximityResidual"


def _freeze_closed_term(value: Any) -> Any:
    """Copy one bounded closed term without accepting ambient containers."""

    if value is None or type(value) in (bool, int, str, bytes):
        frozen = value
    elif type(value) in (tuple, list):
        frozen = tuple(_freeze_closed_term(item) for item in value)
    elif type(value) in (dict, MappingProxyType):
        if not all(type(key) is str for key in value):
            raise malformed(
                "relations:statement-formation",
                "FRI-IOR-RELATION-001",
                "a relation statement map requires exact text keys",
            )
        frozen = MappingProxyType(
            {
                key: _freeze_closed_term(value[key])
                for key in sorted(value, key=lambda item: item.encode("utf-8"))
            }
        )
    else:
        raise malformed(
            "relations:statement-formation",
            "FRI-IOR-RELATION-002",
            "a relation statement must use the closed finite term carrier",
        )
    encode_term(frozen)
    return frozen


def _term_copy(value: Any) -> Any:
    if type(value) in (dict, MappingProxyType):
        return {key: _term_copy(item) for key, item in value.items()}
    if type(value) is tuple:
        return [_term_copy(item) for item in value]
    return value


def _semantic_ref(identity: SemanticId) -> dict[str, Any]:
    return identity.to_term()


def _require_semantic_id(
    value: object,
    *,
    boundary: str,
    code: str,
    label: str,
) -> None:
    if not isinstance(value, SemanticId):
        raise malformed(boundary, code, f"{label} requires a typed SemanticId")


def _oracle_material_preimage(oracle: LogicalOracle) -> dict[str, Any]:
    dependency = oracle.declared_strategy_dependency
    return {
        "kind": "LogicalOracleMaterial",
        "version": 1,
        "name": oracle.name,
        "domain": oracle.domain.to_term(),
        "origin": oracle.origin.value,
        "publication_mode": oracle.publication_mode.value,
        "entries": [
            {
                "point": entry.point.value,
                "answer": entry.value.to_term(),
            }
            for entry in oracle.entries
        ],
        "declared_strategy_dependency": (
            None
            if dependency is None
            else {
                "subject": dependency.subject,
                "authored_at": dependency.authored_at,
                "declared_read_set": list(dependency.declared_read_set),
                "authority": "caller-declared-replay-metadata-only",
                "establishes_strategy_nonanticipation": False,
            }
        ),
    }


def logical_oracle_material_id(candidate: object) -> SemanticId:
    """Identify exact logical-oracle material without returning its carrier."""

    if type(candidate) is not LogicalOracle:
        raise malformed(
            "relations:oracle-material-identity",
            "FRI-IOR-RELATION-003",
            "logical-oracle material identity requires a LogicalOracle",
        )
    return semantic_id(
        "logical-oracle-material",
        "fri-ior.relations.logical-oracle-material.v1",
        _oracle_material_preimage(candidate),
    )


def _layer_number(layer: FriOracleLayer) -> int:
    return 0 if layer is FriOracleLayer.INITIAL else 1


def _expected_native_layer(layer: FriOracleLayer) -> NativeOracleLayer:
    return (
        NativeOracleLayer.INITIAL
        if layer is FriOracleLayer.INITIAL
        else NativeOracleLayer.FIRST_FOLD
    )


def _expected_oracle_name(layer: FriOracleLayer) -> str:
    return (
        INITIAL_ORACLE_NAME if layer is FriOracleLayer.INITIAL else PROVER_ORACLE_NAME
    )


def _construction_input_occurrence_id(
    trace: NativeFriTrace,
    layer: FriOracleLayer,
    oracle: LogicalOracle,
) -> SemanticId:
    return semantic_id(
        "commitment-construction-input-occurrence",
        "fri-ior.relations.commitment-input-occurrence.v1",
        {
            "native_trace_id": _semantic_ref(trace.identity),
            "layer": layer.value,
            "oracle_name": oracle.name,
            "oracle_material_id": _semantic_ref(logical_oracle_material_id(oracle)),
        },
    )


def _cap_publication_occurrence_id(
    proof: PublicFriProof,
    layer: FriOracleLayer,
) -> SemanticId:
    cap = proof.cap0 if layer is FriOracleLayer.INITIAL else proof.cap1
    return semantic_id(
        "committed-cap-publication-occurrence",
        "fri-ior.relations.cap-publication-occurrence.v1",
        {
            "proof_id": _semantic_ref(proof.identity),
            "layer": layer.value,
            "occurrence": f"cap[{_layer_number(layer)}]",
            "cap_id": _semantic_ref(cap.identity),
        },
    )


@dataclass(frozen=True, slots=True)
class RelationStatementOccurrence:
    """One exact relation-side public Statement occurrence."""

    profile_id: SemanticId
    ordinal: int
    value: Any

    SUBJECT_KIND: ClassVar[str] = "relation-statement-occurrence"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.relations.statement.v1"

    def __post_init__(self) -> None:
        _require_semantic_id(
            self.profile_id,
            boundary="relations:statement-formation",
            code="FRI-IOR-RELATION-004",
            label="profile_id",
        )
        if type(self.ordinal) is not int or self.ordinal != 0:
            raise malformed(
                "relations:statement-formation",
                "FRI-IOR-RELATION-005",
                "the finite relation has exactly statement occurrence zero",
            )
        object.__setattr__(self, "value", _freeze_closed_term(self.value))
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": RELATION_STATEMENT_SCHEMA,
            "profile_id": _semantic_ref(self.profile_id),
            "role": "PublicInstance",
            "occurrence_ordinal": self.ordinal,
            "value": _term_copy(self.value),
            "initial_oracle_role": "OracleStatement",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(self.SUBJECT_KIND, self.IDENTITY_DOMAIN, self.to_term())


@dataclass(frozen=True, slots=True)
class InitialOracleMaterialBinding:
    """Portable coordinates associating one initial material occurrence.

    Only the material identity is portable.  The live ``LogicalOracle`` and
    its entries are supplied separately to the grounding operation.  This
    record associates exact occurrences; it does not establish a predicate
    that derives or semantically relates the Oracle material to the Statement.
    Its deterministic material identity is linkable and not confidential.
    """

    relation_statement_id: SemanticId
    material_occurrence_ordinal: int
    oracle_name: str
    domain_name: str
    oracle_material_id: SemanticId

    SUBJECT_KIND: ClassVar[str] = "initial-oracle-material-binding"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.relations.initial-oracle-binding.v1"

    def __post_init__(self) -> None:
        for value, label, code in (
            (self.relation_statement_id, "relation_statement_id", "006"),
            (self.oracle_material_id, "oracle_material_id", "007"),
        ):
            _require_semantic_id(
                value,
                boundary="relations:oracle-binding-formation",
                code=f"FRI-IOR-RELATION-{code}",
                label=label,
            )
        if type(self.material_occurrence_ordinal) is not int or (
            self.material_occurrence_ordinal != 0
        ):
            raise malformed(
                "relations:oracle-binding-formation",
                "FRI-IOR-RELATION-008",
                "the initial OracleStatement has exactly material occurrence zero",
            )
        if self.oracle_name != INITIAL_ORACLE_NAME or self.domain_name != D0.name:
            raise malformed(
                "relations:oracle-binding-formation",
                "FRI-IOR-RELATION-009",
                "the selected initial material binding must name O0 over D0",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": INITIAL_ORACLE_BINDING_SCHEMA,
            "relation_statement_id": _semantic_ref(self.relation_statement_id),
            "material_occurrence_ordinal": self.material_occurrence_ordinal,
            "oracle_name": self.oracle_name,
            "domain_name": self.domain_name,
            "oracle_origin": OracleOrigin.INITIAL_ORACLE.value,
            "publication_mode": OraclePublicationMode.LOGICAL_ACCESS.value,
            "oracle_material_id": _semantic_ref(self.oracle_material_id),
            "portable_material": "identity-only",
            "material_identity_privacy": ("deterministic-linkable-not-confidential"),
            "establishes_statement_to_oracle_predicate": False,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(self.SUBJECT_KIND, self.IDENTITY_DOMAIN, self.to_term())


@dataclass(frozen=True, slots=True)
class ConstructionInputReference:
    """Exact source occurrence named by the commitment construction seam."""

    layer: FriOracleLayer
    oracle_name: str
    source_occurrence_id: SemanticId
    oracle_material_id: SemanticId

    def __post_init__(self) -> None:
        if not isinstance(self.layer, FriOracleLayer):
            raise malformed(
                "relations:construction-reference-formation",
                "FRI-IOR-RELATION-010",
                "a construction input requires a typed FRI oracle layer",
            )
        if not isinstance(self.oracle_name, str) or not self.oracle_name:
            raise malformed(
                "relations:construction-reference-formation",
                "FRI-IOR-RELATION-011",
                "a construction input requires a non-empty oracle name",
            )
        for value, label in (
            (self.source_occurrence_id, "source_occurrence_id"),
            (self.oracle_material_id, "oracle_material_id"),
        ):
            _require_semantic_id(
                value,
                boundary="relations:construction-reference-formation",
                code="FRI-IOR-RELATION-012",
                label=label,
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer.value,
            "oracle_name": self.oracle_name,
            "source_occurrence_id": _semantic_ref(self.source_occurrence_id),
            "oracle_material_id": _semantic_ref(self.oracle_material_id),
        }


@dataclass(frozen=True, slots=True)
class CapOccurrenceReference:
    """Exact target cap publication consumed by the committed verifier."""

    layer: FriOracleLayer
    occurrence_name: str
    cap_occurrence_id: SemanticId
    cap_value_id: SemanticId

    def __post_init__(self) -> None:
        if not isinstance(self.layer, FriOracleLayer):
            raise malformed(
                "relations:cap-reference-formation",
                "FRI-IOR-RELATION-013",
                "a cap reference requires a typed FRI oracle layer",
            )
        if not isinstance(self.occurrence_name, str) or not self.occurrence_name:
            raise malformed(
                "relations:cap-reference-formation",
                "FRI-IOR-RELATION-014",
                "a cap reference requires a non-empty occurrence name",
            )
        for value, label in (
            (self.cap_occurrence_id, "cap_occurrence_id"),
            (self.cap_value_id, "cap_value_id"),
        ):
            _require_semantic_id(
                value,
                boundary="relations:cap-reference-formation",
                code="FRI-IOR-RELATION-015",
                label=label,
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer.value,
            "occurrence_name": self.occurrence_name,
            "cap_occurrence_id": _semantic_ref(self.cap_occurrence_id),
            "cap_value_id": _semantic_ref(self.cap_value_id),
        }


@dataclass(frozen=True, slots=True)
class FriRelationGroundingRequest:
    """Inert exact coordinates to be checked against separately supplied runs."""

    statement: RelationStatementOccurrence
    initial_oracle_binding: InitialOracleMaterialBinding
    commitment_compilation_id: SemanticId
    construction_inputs: tuple[ConstructionInputReference, ...]
    cap_occurrences: tuple[CapOccurrenceReference, ...]

    SUBJECT_KIND: ClassVar[str] = "fri-relation-grounding-request"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.relations.grounding-request.v1"

    def __post_init__(self) -> None:
        if type(self.statement) is not RelationStatementOccurrence:
            raise malformed(
                "relations:grounding-request-formation",
                "FRI-IOR-RELATION-016",
                "a grounding request requires a RelationStatementOccurrence",
            )
        if type(self.initial_oracle_binding) is not InitialOracleMaterialBinding:
            raise malformed(
                "relations:grounding-request-formation",
                "FRI-IOR-RELATION-017",
                "a grounding request requires an InitialOracleMaterialBinding",
            )
        _require_semantic_id(
            self.commitment_compilation_id,
            boundary="relations:grounding-request-formation",
            code="FRI-IOR-RELATION-018",
            label="commitment_compilation_id",
        )
        if (
            type(self.construction_inputs) is not tuple
            or len(self.construction_inputs) != 2
            or not all(
                type(item) is ConstructionInputReference
                for item in self.construction_inputs
            )
            or type(self.cap_occurrences) is not tuple
            or len(self.cap_occurrences) != 2
            or not all(
                type(item) is CapOccurrenceReference for item in self.cap_occurrences
            )
        ):
            raise malformed(
                "relations:grounding-request-formation",
                "FRI-IOR-RELATION-019",
                "the grounding request requires two source inputs and two target caps",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": GROUNDING_REQUEST_SCHEMA,
            "statement_id": _semantic_ref(self.statement.identity),
            "initial_oracle_binding_id": _semantic_ref(
                self.initial_oracle_binding.identity
            ),
            "commitment_compilation_id": _semantic_ref(self.commitment_compilation_id),
            "construction_inputs": [
                item.to_term() for item in self.construction_inputs
            ],
            "cap_occurrences": [item.to_term() for item in self.cap_occurrences],
            "requested_correspondence": (
                "exact-selected-run-openings-not-full-compiler-commutation"
            ),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(self.SUBJECT_KIND, self.IDENTITY_DOMAIN, self.to_term())


@dataclass(frozen=True, slots=True)
class RepresentationBoundaryDeclaration:
    """A taxonomy declaration; formation grants no representation fact."""

    boundary: RepresentationBoundary
    proposed_classification: RepresentationClass

    def __post_init__(self) -> None:
        if not isinstance(self.boundary, RepresentationBoundary) or not isinstance(
            self.proposed_classification,
            RepresentationClass,
        ):
            raise malformed(
                "relations:representation-formation",
                "FRI-IOR-RELATION-040",
                "a representation declaration requires typed boundary and class values",
            )

    def to_term(self) -> dict[str, str]:
        return {
            "boundary": self.boundary.value,
            "proposed_classification": self.proposed_classification.value,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "representation-boundary-declaration",
            "fri-ior.relations.representation-boundary.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class OpeningOccurrenceGrounding:
    """Inert record of one native occurrence and one selected public opening.

    Direct construction is not a checked capability.  Checker provenance
    exists only on the enclosing affirmative relation-grounding result.
    """

    top_level_ordinal: int
    layer: FriOracleLayer
    source_query_occurrence_id: SemanticId
    target_opening_occurrence_id: SemanticId
    target_opening_id: SemanticId
    cap_occurrence_id: SemanticId
    pair_value_id: SemanticId
    opening_table_index: int
    value_relation: RepresentationClass = field(
        default=RepresentationClass.SAME_EXACT_VALUE,
        init=False,
    )
    is_checked_capability: bool = field(default=False, init=False)

    def __post_init__(self) -> None:
        if type(self.top_level_ordinal) is not int or self.top_level_ordinal < 0:
            raise malformed(
                "relations:run-grounding-formation",
                "FRI-IOR-RELATION-041",
                "a run grounding requires a non-negative top-level ordinal",
            )
        if not isinstance(self.layer, FriOracleLayer):
            raise malformed(
                "relations:run-grounding-formation",
                "FRI-IOR-RELATION-042",
                "a run grounding requires a typed FRI layer",
            )
        if type(self.opening_table_index) is not int or self.opening_table_index < 0:
            raise malformed(
                "relations:run-grounding-formation",
                "FRI-IOR-RELATION-043",
                "a run grounding requires a non-negative opening-table index",
            )
        for value in (
            self.source_query_occurrence_id,
            self.target_opening_occurrence_id,
            self.target_opening_id,
            self.cap_occurrence_id,
            self.pair_value_id,
        ):
            _require_semantic_id(
                value,
                boundary="relations:run-grounding-formation",
                code="FRI-IOR-RELATION-044",
                label="run grounding identity",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "top_level_ordinal": self.top_level_ordinal,
            "layer": self.layer.value,
            "source_query_occurrence_id": _semantic_ref(
                self.source_query_occurrence_id
            ),
            "target_opening_occurrence_id": _semantic_ref(
                self.target_opening_occurrence_id
            ),
            "target_opening_id": _semantic_ref(self.target_opening_id),
            "cap_occurrence_id": _semantic_ref(self.cap_occurrence_id),
            "pair_value_id": _semantic_ref(self.pair_value_id),
            "opening_table_index": self.opening_table_index,
            "value_relation": self.value_relation.value,
            "authority": "portable-inert-record-no-live-check-capability",
            "is_checked_capability": self.is_checked_capability,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "opening-occurrence-grounding-record",
            "fri-ior.relations.opening-occurrence-grounding.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class FriTerminalResidualBoundary:
    """Inert record separating a terminal from an unproved FRI proposition.

    The carrier cannot certify that supplied IDs came from accepted runs.
    Checker provenance exists only on the enclosing affirmative result.
    """

    relation_statement_id: SemanticId
    native_trace_id: SemanticId
    committed_verification_id: SemanticId
    terminal_material_id: SemanticId
    execution_terminal: str
    residual_status: ResidualStatus = field(
        default=ResidualStatus.NOT_EVALUATED,
        init=False,
    )
    establishes_proximity: bool = field(default=False, init=False)
    establishes_proximity_preservation: bool = field(default=False, init=False)
    implies_outer_computation_relation: bool = field(default=False, init=False)
    is_checked_capability: bool = field(default=False, init=False)

    def __post_init__(self) -> None:
        for value in (
            self.relation_statement_id,
            self.native_trace_id,
            self.committed_verification_id,
            self.terminal_material_id,
        ):
            _require_semantic_id(
                value,
                boundary="relations:residual-formation",
                code="FRI-IOR-RELATION-045",
                label="residual boundary identity",
            )
        if self.execution_terminal != "Accept":
            raise malformed(
                "relations:residual-formation",
                "FRI-IOR-RELATION-046",
                "this residual record is formed only for an Accept terminal",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "relation_statement_id": _semantic_ref(self.relation_statement_id),
            "native_trace_id": _semantic_ref(self.native_trace_id),
            "committed_verification_id": _semantic_ref(self.committed_verification_id),
            "terminal_material_id": _semantic_ref(self.terminal_material_id),
            "execution_terminal": self.execution_terminal,
            "residual_proposition": {
                "kind": "ReedSolomonProximity",
                "initial_domain": D0.name,
                "degree_bound_exclusive": (
                    EXACT_PROFILE.initial_degree_bound_exclusive
                ),
            },
            "residual_status": self.residual_status.value,
            "establishes_proximity": self.establishes_proximity,
            "establishes_proximity_preservation": (
                self.establishes_proximity_preservation
            ),
            "implies_outer_computation_relation": (
                self.implies_outer_computation_relation
            ),
            "authority": "portable-inert-record-no-live-check-capability",
            "is_checked_capability": self.is_checked_capability,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fri-terminal-residual-record",
            "fri-ior.relations.terminal-residual.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class OuterRelationInferenceRequest:
    """One deliberately insufficient attempt to infer an outer relation."""

    grounding_id: SemanticId
    outer_relation_id: SemanticId
    premise: OuterInferencePremise

    def __post_init__(self) -> None:
        _require_semantic_id(
            self.grounding_id,
            boundary="relations:outer-inference-formation",
            code="FRI-IOR-RELATION-060",
            label="grounding_id",
        )
        _require_semantic_id(
            self.outer_relation_id,
            boundary="relations:outer-inference-formation",
            code="FRI-IOR-RELATION-061",
            label="outer_relation_id",
        )
        if not isinstance(self.premise, OuterInferencePremise):
            raise malformed(
                "relations:outer-inference-formation",
                "FRI-IOR-RELATION-062",
                "an outer inference request requires a typed premise",
            )


def canonical_relation_grounding_request(
    statement: object,
    trace: object,
    public_inputs: object,
    proof: object,
) -> FriRelationGroundingRequest:
    """Form inert exact coordinates; the checker recomputes every coordinate."""

    if type(statement) is not RelationStatementOccurrence:
        raise malformed(
            "relations:grounding-request-construction",
            "FRI-IOR-RELATION-063",
            "request construction requires a RelationStatementOccurrence",
        )
    if type(trace) is not NativeFriTrace:
        raise malformed(
            "relations:grounding-request-construction",
            "FRI-IOR-RELATION-064",
            "request construction requires a NativeFriTrace",
        )
    if type(public_inputs) is not CommittedFriPublicInputs:
        raise malformed(
            "relations:grounding-request-construction",
            "FRI-IOR-RELATION-065",
            "request construction requires committed public inputs",
        )
    if type(proof) is not PublicFriProof:
        raise malformed(
            "relations:grounding-request-construction",
            "FRI-IOR-RELATION-066",
            "request construction requires a public FRI proof",
        )

    initial_material = logical_oracle_material_id(trace.initial_oracle)
    initial_binding = InitialOracleMaterialBinding(
        statement.identity,
        0,
        INITIAL_ORACLE_NAME,
        D0.name,
        initial_material,
    )
    construction_inputs = tuple(
        ConstructionInputReference(
            layer,
            oracle.name,
            _construction_input_occurrence_id(trace, layer, oracle),
            logical_oracle_material_id(oracle),
        )
        for layer, oracle in (
            (FriOracleLayer.INITIAL, trace.initial_oracle),
            (FriOracleLayer.FIRST_FOLD, trace.prover_oracle),
        )
    )
    cap_occurrences = tuple(
        CapOccurrenceReference(
            layer,
            f"cap[{_layer_number(layer)}]",
            _cap_publication_occurrence_id(proof, layer),
            (proof.cap0 if layer is FriOracleLayer.INITIAL else proof.cap1).identity,
        )
        for layer in (FriOracleLayer.INITIAL, FriOracleLayer.FIRST_FOLD)
    )
    return FriRelationGroundingRequest(
        statement,
        initial_binding,
        COMMITMENT_COMPILATION_DECLARATION.identity,
        construction_inputs,
        cap_occurrences,
    )


def check_representation_boundary(candidate: object) -> CheckResult:
    """Form the selected taxonomy declaration without checking its truth.

    The publication-loss checker below can provide evidence for one concrete
    lossy projection.  This operation only rejects taxonomy labels that would
    overstate either selected boundary; it does not prove the remaining label.
    """

    boundary = "relations:representation-declaration"
    if type(candidate) is not RepresentationBoundaryDeclaration:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-047",
            "representation declaration requires its exact formed carrier",
        )
    expected = {
        RepresentationBoundary.LOGICAL_ORACLE_PUBLICATION: (
            RepresentationClass.DIRECTIONAL_LOSSY_PROJECTION
        ),
        RepresentationBoundary.LOGICAL_ORACLE_COMMITMENT_CAP: (
            RepresentationClass.NON_ISOMORPHIC_CONSTRUCTION_RELATION
        ),
    }[candidate.boundary]
    if candidate.proposed_classification is not expected:
        return refused(
            boundary,
            "FRI-IOR-RELATION-048",
            (
                "the proposed representation class erases loss or mistakes a "
                "commitment construction for an isomorphism"
            ),
        )
    return affirmative(
        boundary,
        "FRI-IOR-RELATION-100",
        "the selected representation taxonomy declaration is well formed",
        subject=candidate.identity,
        classification=expected.value,
        classification_status="DeclaredNotChecked",
        establishes_classification_truth=False,
        establishes_bridge_law=False,
        establishes_commitment_security=False,
    )


def check_logical_publication_loss(first: object, second: object) -> CheckResult:
    """Check one concrete collision of the logical-publication projection."""

    boundary = "relations:logical-publication-loss"
    if type(first) is not LogicalOracle or type(second) is not LogicalOracle:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-049",
            "a projection collision requires two LogicalOracle values",
        )
    try:
        first_id = logical_oracle_material_id(first)
        second_id = logical_oracle_material_id(second)
        if first_id == second_id:
            return refused(
                boundary,
                "FRI-IOR-RELATION-050",
                "identical oracle material does not witness information loss",
            )
        first_observation = first.publication_observation()
        second_observation = second.publication_observation()
        if encode_term(first_observation) != encode_term(second_observation):
            return refused(
                boundary,
                "FRI-IOR-RELATION-051",
                "the two materials do not collide under publication observation",
            )
        observation_id = semantic_id(
            "logical-oracle-publication-observation",
            "fri-ior.relations.logical-publication-observation.v1",
            first_observation,
        )
        subject = semantic_id(
            "logical-publication-loss-witness",
            "fri-ior.relations.logical-publication-loss.v1",
            {
                "first_material_id": _semantic_ref(first_id),
                "second_material_id": _semantic_ref(second_id),
                "common_observation_id": _semantic_ref(observation_id),
            },
        )
        return affirmative(
            boundary,
            "FRI-IOR-RELATION-101",
            "two distinct logical-oracle materials have one public observation",
            subject=subject,
            classification=RepresentationClass.DIRECTIONAL_LOSSY_PROJECTION.value,
            first_material_id=first_id,
            second_material_id=second_id,
            common_observation_id=observation_id,
            establishes_commitment_security=False,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected projection-loss checker failure: {type(error).__name__}",
        )


def _expected_construction_inputs(
    trace: NativeFriTrace,
) -> tuple[ConstructionInputReference, ...]:
    return tuple(
        ConstructionInputReference(
            layer,
            oracle.name,
            _construction_input_occurrence_id(trace, layer, oracle),
            logical_oracle_material_id(oracle),
        )
        for layer, oracle in (
            (FriOracleLayer.INITIAL, trace.initial_oracle),
            (FriOracleLayer.FIRST_FOLD, trace.prover_oracle),
        )
    )


def _expected_cap_occurrences(
    proof: PublicFriProof,
) -> tuple[CapOccurrenceReference, ...]:
    return tuple(
        CapOccurrenceReference(
            layer,
            f"cap[{_layer_number(layer)}]",
            _cap_publication_occurrence_id(proof, layer),
            (proof.cap0 if layer is FriOracleLayer.INITIAL else proof.cap1).identity,
        )
        for layer in (FriOracleLayer.INITIAL, FriOracleLayer.FIRST_FOLD)
    )


def _source_query_occurrence_id(
    trace: NativeFriTrace,
    occurrence: LayerQueryAnswerOccurrence,
) -> SemanticId:
    return semantic_id(
        "native-logical-query-answer-occurrence",
        "fri-ior.relations.native-query-answer.v1",
        {
            "native_trace_id": _semantic_ref(trace.identity),
            "top_level_ordinal": occurrence.top_level_ordinal,
            "layer": occurrence.layer.value,
            "oracle_name": occurrence.oracle_name,
            "pair_index": occurrence.pair_index,
            "positive_answer_index": occurrence.positive_answer_index,
            "negative_answer_index": occurrence.negative_answer_index,
        },
    )


def _pair_value_id(positive: Any, negative: Any) -> SemanticId:
    return semantic_id(
        "ordered-antipodal-answer-pair",
        "fri-ior.relations.answer-pair.v1",
        {
            "positive": positive.to_term(),
            "negative": negative.to_term(),
        },
    )


def _ground_opening_occurrences(
    trace: NativeFriTrace,
    proof: PublicFriProof,
    transcript: FiatShamirTranscript,
    resources: ResourceCounter,
) -> tuple[OpeningOccurrenceGrounding, ...] | CheckResult:
    resolution = resolve_layer_query_answers(trace, resources)
    if isinstance(resolution, CheckResult):
        return resolution
    source_by_coordinate = {
        (item.top_level_ordinal, item.layer): item for item in resolution
    }
    records: list[OpeningOccurrenceGrounding] = []
    for query, selector in zip(
        transcript.query_occurrences,
        proof.occurrence_selectors,
        strict=True,
    ):
        for layer, table_index in (
            (FriOracleLayer.INITIAL, selector.layer0_opening_index),
            (FriOracleLayer.FIRST_FOLD, selector.layer1_opening_index),
        ):
            source = source_by_coordinate.get(
                (query.ordinal, _expected_native_layer(layer))
            )
            if source is None or table_index >= len(proof.opening_table):
                raise RuntimeError(
                    "admitted native and committed runs lack a selected pair"
                )
            entry = proof.opening_table[table_index]
            expected_key = (_layer_number(layer), source.pair_index)
            if entry.key != expected_key:
                raise RuntimeError(
                    "admitted committed run has a wrong selector coordinate"
                )
            opening = entry.opening
            if (
                source.positive_value != opening.positive
                or source.negative_value != opening.negative
            ):
                return refused(
                    "relations:run-occurrence-grounding",
                    "FRI-IOR-RELATION-054",
                    "authenticated target values disagree with the native answers",
                )
            target_occurrence_id = semantic_id(
                "committed-opening-selection-occurrence",
                "fri-ior.relations.opening-selection.v1",
                {
                    "proof_id": _semantic_ref(proof.identity),
                    "top_level_ordinal": query.ordinal,
                    "layer": layer.value,
                    "opening_table_index": table_index,
                    "opening_id": _semantic_ref(opening.identity),
                },
            )
            records.append(
                OpeningOccurrenceGrounding(
                    query.ordinal,
                    layer,
                    _source_query_occurrence_id(trace, source),
                    target_occurrence_id,
                    opening.identity,
                    _cap_publication_occurrence_id(proof, layer),
                    _pair_value_id(opening.positive, opening.negative),
                    table_index,
                )
            )
    return tuple(records)


def check_fri_relation_grounding(
    request: object,
    trace: object,
    public_inputs: object,
    proof: object,
) -> CheckResult:
    """Check the exact finite Statement/Oracle/cap/run grounding seam."""

    boundary = "relations:fri-grounding"
    if type(request) is not FriRelationGroundingRequest:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-055",
            "FRI grounding requires a FriRelationGroundingRequest",
        )
    if type(trace) is not NativeFriTrace:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-056",
            "FRI grounding requires a NativeFriTrace",
        )
    if type(public_inputs) is not CommittedFriPublicInputs:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-057",
            "FRI grounding requires committed public inputs",
        )
    if type(proof) is not PublicFriProof:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-058",
            "FRI grounding requires a public FRI proof",
        )

    try:
        resources = ResourceCounter()
        profile_admission = admit_exact_profile(public_inputs.profile)
        if profile_admission.outcome is not OutcomeClass.AFFIRMATIVE:
            return profile_admission
        if request.statement.profile_id != EXACT_PROFILE.identity:
            return unsupported(
                "relations:statement-grounding",
                "FRI-IOR-RELATION-020",
                "the relation statement names a profile outside this finite case",
            )
        if encode_term(request.statement.value) != encode_term(public_inputs.statement):
            return refused(
                "relations:statement-grounding",
                "FRI-IOR-RELATION-021",
                "the relation Statement occurrence and transcript Statement differ",
            )

        expected_initial_material = logical_oracle_material_id(trace.initial_oracle)
        binding = request.initial_oracle_binding
        if binding.relation_statement_id != request.statement.identity:
            return refused(
                "relations:initial-oracle-grounding",
                "FRI-IOR-RELATION-022",
                "the material binding names a different relation Statement occurrence",
            )
        if (
            trace.initial_oracle.name != INITIAL_ORACLE_NAME
            or trace.initial_oracle.domain != D0
            or trace.initial_oracle.origin is not OracleOrigin.INITIAL_ORACLE
            or trace.initial_oracle.publication_mode
            is not OraclePublicationMode.LOGICAL_ACCESS
            or binding.oracle_material_id != expected_initial_material
        ):
            return refused(
                "relations:initial-oracle-grounding",
                "FRI-IOR-RELATION-023",
                "the live initial logical-oracle material does not match its binding",
            )

        if request.commitment_compilation_id != (
            COMMITMENT_COMPILATION_DECLARATION.identity
        ):
            return kind_mismatch(
                "relations:construction-grounding",
                "FRI-IOR-RELATION-024",
                "the request names a different commitment-construction declaration",
            )
        if request.construction_inputs != _expected_construction_inputs(trace):
            return refused(
                "relations:construction-grounding",
                "FRI-IOR-RELATION-025",
                "the source construction-input occurrence set is not exact",
            )
        if request.cap_occurrences != _expected_cap_occurrences(proof):
            return refused(
                "relations:cap-grounding",
                "FRI-IOR-RELATION-026",
                "the target cap-publication occurrence set is not exact",
            )

        native_result = verify_native_trace(trace, resources)
        if native_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return native_result
        committed_result = verify_committed_fri(
            public_inputs,
            proof,
            resources,
        )
        if committed_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return committed_result

        transcript = derive_fiat_shamir_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            proof.cap0,
            proof.cap1,
            proof.terminal_coefficients,
            proof.grinding_nonce,
            resources,
        )
        if isinstance(transcript, CheckResult):
            return transcript
        if type(transcript) is not FiatShamirTranscript:
            raise RuntimeError("the transcript operation returned a wrong-kind value")

        if trace.beta0 != transcript.beta0 or trace.beta1 != transcript.beta1:
            return refused(
                "relations:run-occurrence-grounding",
                "FRI-IOR-RELATION-027",
                "native and committed runs do not share the exact fold challenges",
            )
        if trace.terminal.coefficients != transcript.terminal_coefficients:
            return refused(
                "relations:terminal-grounding",
                "FRI-IOR-RELATION-028",
                "native and committed runs do not share terminal material",
            )
        native_draws = tuple(
            (draw.ordinal, draw.initial_domain_index) for draw in trace.query_draws
        )
        committed_draws = tuple(
            (draw.ordinal, draw.initial_domain_index)
            for draw in transcript.query_occurrences
        )
        if native_draws != committed_draws:
            return refused(
                "relations:run-occurrence-grounding",
                "FRI-IOR-RELATION-029",
                "native and committed runs do not share ordered query occurrences",
            )

        opening_groundings = _ground_opening_occurrences(
            trace,
            proof,
            transcript,
            resources,
        )
        if isinstance(opening_groundings, CheckResult):
            return opening_groundings

        terminal_material_id = semantic_id(
            "fri-terminal-material-occurrence",
            "fri-ior.relations.terminal-material.v1",
            {
                "coefficients": [
                    coefficient.to_term() for coefficient in trace.terminal.coefficients
                ]
            },
        )
        if committed_result.subject is None:
            raise RuntimeError("affirmative committed verification lacks a subject")
        residual = FriTerminalResidualBoundary(
            request.statement.identity,
            trace.identity,
            committed_result.subject,
            terminal_material_id,
            "Accept",
        )
        result_subject = semantic_id(
            "checked-fri-relation-grounding",
            "fri-ior.relations.checked-grounding.v1",
            {
                "schema": GROUNDING_RESULT_SCHEMA,
                "request_id": _semantic_ref(request.identity),
                "native_verification_id": _semantic_ref(trace.identity),
                "committed_verification_id": _semantic_ref(committed_result.subject),
                "opening_occurrence_groundings": [
                    grounding.to_term() for grounding in opening_groundings
                ],
                "terminal_residual_boundary": residual.to_term(),
                "construction_relation_class": (
                    RepresentationClass.NON_ISOMORPHIC_CONSTRUCTION_RELATION.value
                ),
                "establishes_full_commitment_compilation": False,
            },
        )
        return affirmative(
            boundary,
            "FRI-IOR-RELATION-102",
            (
                "the exact Statement, Oracle-material association, cap "
                "coordinates, and selected run occurrences are grounded"
            ),
            subject=result_subject,
            request_id=request.identity,
            statement_grounding_id=request.statement.identity,
            initial_oracle_binding_id=binding.identity,
            construction_input_occurrence_ids=[
                item.source_occurrence_id for item in request.construction_inputs
            ],
            cap_occurrence_ids=[
                item.cap_occurrence_id for item in request.cap_occurrences
            ],
            opening_occurrence_grounding_ids=[
                grounding.identity for grounding in opening_groundings
            ],
            opening_occurrence_grounding_count=len(opening_groundings),
            unique_physical_opening_count=len(proof.opening_table),
            ordered_grounding_coordinates=[
                (grounding.top_level_ordinal, grounding.layer.value)
                for grounding in opening_groundings
            ],
            terminal_residual_boundary_id=residual.identity,
            execution_terminal=residual.execution_terminal,
            proximity_residual_status=residual.residual_status.value,
            construction_relation_class=(
                RepresentationClass.NON_ISOMORPHIC_CONSTRUCTION_RELATION.value
            ),
            resource_snapshot=resources.snapshot(),
            resource_scope="one-private-counter-for-the-complete-operation",
            establishes_statement_to_oracle_predicate=False,
            oracle_material_identity_is_confidential=False,
            oracle_material_identity_leaks_equality=True,
            establishes_full_commitment_compilation=False,
            establishes_commitment_binding=False,
            establishes_commitment_hiding=False,
            establishes_proximity=False,
            establishes_proximity_preservation=False,
            infers_outer_computation_relation=False,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected relation-grounding failure: {type(error).__name__}",
        )


def infer_outer_computation_relation(candidate: object) -> CheckResult:
    """Refuse the invalid FRI-acceptance/proximity-to-outer-relation step."""

    boundary = "relations:outer-computation-inference"
    if type(candidate) is not OuterRelationInferenceRequest:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-RELATION-067",
            "outer-relation inference requires a formed inference request",
        )
    if (
        candidate.grounding_id.subject_kind != "checked-fri-relation-grounding"
        or candidate.grounding_id.domain != "fri-ior.relations.checked-grounding.v1"
        or candidate.outer_relation_id.subject_kind != "outer-computation-relation"
    ):
        return kind_mismatch(
            boundary,
            "FRI-IOR-RELATION-068",
            "the inference request names a wrong-kind grounding or outer relation",
        )
    return refused(
        boundary,
        "FRI-IOR-RELATION-069",
        (
            "FRI execution acceptance and its unevaluated proximity residual do "
            "not establish an outer computation relation"
        ),
    )


__all__ = [
    "CapOccurrenceReference",
    "ConstructionInputReference",
    "FriOracleLayer",
    "FriRelationGroundingRequest",
    "InitialOracleMaterialBinding",
    "OuterInferencePremise",
    "OuterRelationInferenceRequest",
    "RelationStatementOccurrence",
    "RepresentationBoundary",
    "RepresentationBoundaryDeclaration",
    "RepresentationClass",
    "ResidualStatus",
    "canonical_relation_grounding_request",
    "check_fri_relation_grounding",
    "check_logical_publication_loss",
    "check_representation_boundary",
    "infer_outer_computation_relation",
    "logical_oracle_material_id",
]
