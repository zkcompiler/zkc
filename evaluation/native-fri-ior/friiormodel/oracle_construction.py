"""Reusable authority for one exact oracle-commitment construction.

The construction in this module is general only over executions of the exact
Goldilocks, order-64, three-fold classical FRI Core pair in ``classical.py``.
It does not range over arbitrary FRI profiles, commitment schemes, domains, or
query laws.  Its semantic subject owns deterministic static source/target maps,
construction-local advice shape, public-replay closure, and intrinsic bounds.

Admission re-derives those values and both endpoint identities.  It never
accepts an authored correspondence or ``commutes`` flag.  An affirmative
admission mints a fresh process-local capability.  The capability is neither a
semantic artifact nor serializable.  A checked per-run receipt is a separate,
portable record and cannot authorize another run.

The established scope is structural and deterministic.  In particular, no
result here claims commitment binding, hiding, extractability, FRI proximity
soundness, a random-oracle theorem, or transport of any cryptographic property.
Structural admission also does not certify that every runtime pair commutes;
that conclusion is issued only after independent validation of one concrete
source/target pair under the live capability.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from math import log2
from typing import Any, ClassVar

from .classical import (
    CLASSICAL_DOMAINS,
    DEFAULT_CLASSICAL_LIMITS,
    DIGEST_BYTES,
    EXACT_CLASSICAL_COMMITMENT_PROFILE,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_NATIVE_CORE,
    FOLD_ROUNDS,
    FRESH_INTERPRETATION,
    LAYER_QUERY_OCCURRENCES,
    QUERY_REPETITIONS,
    SALT_BYTES,
    ClassicalCommittedCore,
    ClassicalCommittedCase,
    ClassicalCommittedRun,
    ClassicalNativeTrace,
    ClassicalNativeCore,
    ClassicalScheduleEvent,
    build_classical_commitment,
    derive_layer_query_occurrences,
    verify_committed_run,
    verify_native_trace,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    SemanticId,
    affirmative,
    checker_failure,
    encode_term,
    malformed,
    semantic_id,
)


CONSTRUCTION_SCHEMA = (
    "zkc.classical-fri.oracle-commitment-construction-declaration.v1"
)
RUN_RECEIPT_SCHEMA = "zkc.classical-fri.oracle-commitment-run-receipt.v1"
COMMITMENT_PROFILE_NAME = "salted-sha256-antipodal-pairs-single-root-v1"
STATIC_ELABORATION_LAW = (
    "classical-fri.exact-oracle-commitment-static-elaboration.v2"
)
INTRINSIC_BOUND_LAW = "classical-fri.exact-oracle-commitment-bounds.v1"
PHYSICAL_OPENING_BINDING_LAW = (
    "canonical-deduplication-by-layer-and-pair-index"
)
OPENING_TABLE_AUTHENTICATION_CHECK = "authenticate-canonical-opening-table"

CONSTRUCTION_NONCLAIMS = (
    "commitment-binding-hiding-or-extractability",
    "fri-proximity-soundness-or-completeness",
    "universal-fri-family-compilation",
    "fiat-shamir-security",
    "cryptographic-property-transport",
    "universal-execution-commutation-without-per-run-validation",
)


def _semantic_ref(value: SemanticId, where: str) -> dict[str, Any]:
    if not isinstance(value, SemanticId):
        raise malformed(
            "oracle-construction:formation",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-001",
            f"{where} requires a typed SemanticId",
        )
    return value.to_term()


def _require_text(value: object, where: str) -> str:
    if not isinstance(value, str) or not value or len(value) > 256:
        raise malformed(
            "oracle-construction:formation",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-027",
            f"{where} requires bounded non-empty text",
        )
    return value


def _exact_source_core_id() -> SemanticId:
    """Recompute rather than copy the source Core identity."""

    return semantic_id(
        "classical-fri-native-core",
        "classical-fri.native-core.v1",
        EXACT_CLASSICAL_NATIVE_CORE.to_term(),
    )


def _exact_target_core_id() -> SemanticId:
    """Recompute rather than copy the elaborated target Core identity."""

    return semantic_id(
        "classical-fri-committed-core",
        "classical-fri.committed-core.v1",
        EXACT_CLASSICAL_COMMITTED_CORE.to_term(),
    )


@dataclass(frozen=True, slots=True)
class OracleCommitmentProfile:
    """Exact construction-local commitment and opening semantics."""

    source_profile_id: SemanticId
    commitment_semantics_id: SemanticId
    name: str
    hash_name: str
    digest_bytes: int
    salt_bytes: int
    committed_domain_orders: tuple[int, ...]
    leaf_layout: str
    root_layout: str
    query_normalization_law: str
    opening_selection_law: str
    opening_authentication_law: str
    answer_extraction_law: str

    def __post_init__(self) -> None:
        _semantic_ref(self.source_profile_id, "source_profile_id")
        _semantic_ref(
            self.commitment_semantics_id,
            "commitment_semantics_id",
        )
        if self.commitment_semantics_id != EXACT_CLASSICAL_COMMITMENT_PROFILE.identity:
            raise malformed(
                "oracle-construction:profile-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-020",
                "the construction profile must bind the exact commitment semantics",
            )
        if self.name != COMMITMENT_PROFILE_NAME:
            raise malformed(
                "oracle-construction:profile-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-002",
                "the exact construction requires its selected commitment profile",
            )
        expected = (
            "sha256",
            DIGEST_BYTES,
            SALT_BYTES,
            tuple(domain.order for domain in CLASSICAL_DOMAINS[:FOLD_ROUNDS]),
            "ordered-antipodal-goldilocks-pair-with-owner-salt",
            "one-ordered-sha256-root-per-committed-oracle",
            "layer-index-is-draw-modulo-half-domain-order",
            "canonical-deduplication-by-layer-and-pair-index",
            "salted-leaf-and-ordered-binary-path-to-single-root",
            "authenticated-positive-then-antipodal-negative",
        )
        actual = (
            self.hash_name,
            self.digest_bytes,
            self.salt_bytes,
            self.committed_domain_orders,
            self.leaf_layout,
            self.root_layout,
            self.query_normalization_law,
            self.opening_selection_law,
            self.opening_authentication_law,
            self.answer_extraction_law,
        )
        if actual != expected:
            raise malformed(
                "oracle-construction:profile-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-003",
                (
                    "the commitment profile is not the exact classical "
                    "construction profile"
                ),
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "source_profile_id": _semantic_ref(
                self.source_profile_id, "source_profile_id"
            ),
            "commitment_semantics_id": _semantic_ref(
                self.commitment_semantics_id,
                "commitment_semantics_id",
            ),
            "name": self.name,
            "hash": self.hash_name,
            "digest_bytes": self.digest_bytes,
            "salt_bytes": self.salt_bytes,
            "committed_domain_orders": list(self.committed_domain_orders),
            "leaf_layout": self.leaf_layout,
            "root_layout": self.root_layout,
            "query_normalization_law": self.query_normalization_law,
            "opening_selection_law": self.opening_selection_law,
            "opening_authentication_law": self.opening_authentication_law,
            "answer_extraction_law": self.answer_extraction_law,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "oracle-commitment-profile",
            "classical-fri.oracle-commitment-profile.v1",
            self.to_term(),
        )


EXACT_ORACLE_COMMITMENT_PROFILE = OracleCommitmentProfile(
    source_profile_id=EXACT_CLASSICAL_FRI_PROFILE.identity,
    commitment_semantics_id=EXACT_CLASSICAL_COMMITMENT_PROFILE.identity,
    name=COMMITMENT_PROFILE_NAME,
    hash_name="sha256",
    digest_bytes=DIGEST_BYTES,
    salt_bytes=SALT_BYTES,
    committed_domain_orders=tuple(
        domain.order for domain in CLASSICAL_DOMAINS[:FOLD_ROUNDS]
    ),
    leaf_layout="ordered-antipodal-goldilocks-pair-with-owner-salt",
    root_layout="one-ordered-sha256-root-per-committed-oracle",
    query_normalization_law="layer-index-is-draw-modulo-half-domain-order",
    opening_selection_law=PHYSICAL_OPENING_BINDING_LAW,
    opening_authentication_law=(
        "salted-leaf-and-ordered-binary-path-to-single-root"
    ),
    answer_extraction_law="authenticated-positive-then-antipodal-negative",
)


@dataclass(frozen=True, slots=True)
class PublicEnvironmentMapEntry:
    coordinate_ordinal: int
    source_coordinate: str
    target_coordinate: str
    semantic_purpose: str

    def __post_init__(self) -> None:
        if type(self.coordinate_ordinal) is not int or not 0 <= self.coordinate_ordinal < 2:
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-062",
                "a public-environment coordinate ordinal must be zero or one",
            )
        for value, where in (
            (self.source_coordinate, "source_coordinate"),
            (self.target_coordinate, "target_coordinate"),
            (self.semantic_purpose, "semantic_purpose"),
        ):
            _require_text(value, where)
        expected = (
            (0, "statement", "statement", "Statement"),
            (
                1,
                "application_context",
                "application_context",
                "ApplicationContext",
            ),
        )
        if (
            self.coordinate_ordinal,
            self.source_coordinate,
            self.target_coordinate,
            self.semantic_purpose,
        ) != expected[self.coordinate_ordinal]:
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-063",
                "the exact public-environment map preserves both typed coordinates",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "coordinate_ordinal": self.coordinate_ordinal,
            "source_coordinate": self.source_coordinate,
            "target_coordinate": self.target_coordinate,
            "semantic_purpose": self.semantic_purpose,
        }


@dataclass(frozen=True, slots=True)
class PublicationMapEntry:
    layer: int
    source_oracle: str
    target_root: str
    domain_id: SemanticId

    def __post_init__(self) -> None:
        if type(self.layer) is not int or not 0 <= self.layer < FOLD_ROUNDS:
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-028",
                "a publication-map layer must be 0, 1, or 2",
            )
        _require_text(self.source_oracle, "source_oracle")
        _require_text(self.target_root, "target_root")
        _semantic_ref(self.domain_id, "domain_id")

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer,
            "source_oracle": self.source_oracle,
            "target_root": self.target_root,
            "domain_id": _semantic_ref(self.domain_id, "domain_id"),
        }


@dataclass(frozen=True, slots=True)
class FreshCoinMapEntry:
    round_ordinal: int
    source_coin: str
    target_coin: str
    protected_publication_prefix: tuple[str, ...]

    def __post_init__(self) -> None:
        if (
            type(self.round_ordinal) is not int
            or not 0 <= self.round_ordinal < FOLD_ROUNDS
        ):
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-029",
                "a Fresh-coin map round must be 0, 1, or 2",
            )
        _require_text(self.source_coin, "source_coin")
        _require_text(self.target_coin, "target_coin")
        if (
            type(self.protected_publication_prefix) is not tuple
            or not self.protected_publication_prefix
            or any(
                not isinstance(item, str) or not item
                for item in self.protected_publication_prefix
            )
        ):
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-030",
                "a Fresh coin requires a canonical non-empty protected prefix",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "round_ordinal": self.round_ordinal,
            "source_coin": self.source_coin,
            "target_coin": self.target_coin,
            "protected_publication_prefix": list(
                self.protected_publication_prefix
            ),
        }


@dataclass(frozen=True, slots=True)
class QueryDrawMapEntry:
    draw_ordinal: int
    source_draw: str
    target_draw: str

    def __post_init__(self) -> None:
        if (
            type(self.draw_ordinal) is not int
            or not 0 <= self.draw_ordinal < QUERY_REPETITIONS
        ):
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-031",
                "a query-draw map ordinal must be below four",
            )
        _require_text(self.source_draw, "source_draw")
        _require_text(self.target_draw, "target_draw")

    def to_term(self) -> dict[str, Any]:
        return {
            "draw_ordinal": self.draw_ordinal,
            "source_draw": self.source_draw,
            "target_draw": self.target_draw,
        }


@dataclass(frozen=True, slots=True)
class AnswerOpeningMapEntry:
    occurrence_ordinal: int
    draw_ordinal: int
    layer: int
    source_query_occurrence: str
    source_answer_occurrence: str
    target_selector_occurrence: str
    target_logical_opening_coordinate: str
    target_answer_coordinate: str
    target_authentication_check: str

    def __post_init__(self) -> None:
        if (
            type(self.occurrence_ordinal) is not int
            or not 0 <= self.occurrence_ordinal < LAYER_QUERY_OCCURRENCES
            or type(self.draw_ordinal) is not int
            or not 0 <= self.draw_ordinal < QUERY_REPETITIONS
            or type(self.layer) is not int
            or not 0 <= self.layer < FOLD_ROUNDS
            or self.occurrence_ordinal
            != self.draw_ordinal * FOLD_ROUNDS + self.layer
        ):
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-032",
                "an answer-opening entry requires its exact draw/layer ordinal",
            )
        for value, where in (
            (self.source_query_occurrence, "source_query_occurrence"),
            (self.source_answer_occurrence, "source_answer_occurrence"),
            (self.target_selector_occurrence, "target_selector_occurrence"),
            (
                self.target_logical_opening_coordinate,
                "target_logical_opening_coordinate",
            ),
            (self.target_answer_coordinate, "target_answer_coordinate"),
            (self.target_authentication_check, "target_authentication_check"),
        ):
            _require_text(value, where)

    def to_term(self) -> dict[str, Any]:
        return {
            "occurrence_ordinal": self.occurrence_ordinal,
            "draw_ordinal": self.draw_ordinal,
            "layer": self.layer,
            "source_query_occurrence": self.source_query_occurrence,
            "source_answer_occurrence": self.source_answer_occurrence,
            "target_selector_occurrence": self.target_selector_occurrence,
            "target_logical_opening_coordinate": (
                self.target_logical_opening_coordinate
            ),
            "target_answer_coordinate": self.target_answer_coordinate,
            "target_authentication_check": self.target_authentication_check,
        }


@dataclass(frozen=True, slots=True)
class ScalarTerminalMap:
    source_terminal: str
    target_terminal: str
    value_type: str

    def __post_init__(self) -> None:
        _require_text(self.source_terminal, "source_terminal")
        _require_text(self.target_terminal, "target_terminal")
        _require_text(self.value_type, "value_type")

    def to_term(self) -> dict[str, Any]:
        return {
            "source_terminal": self.source_terminal,
            "target_terminal": self.target_terminal,
            "value_type": self.value_type,
        }


@dataclass(frozen=True, slots=True)
class CheckMapEntry:
    ordinal: int
    source_check: str | None
    target_check: str
    disposition: str

    def __post_init__(self) -> None:
        if type(self.ordinal) is not int or self.ordinal < 0:
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-033",
                "a check-map ordinal must be non-negative",
            )
        if self.source_check is not None:
            _require_text(self.source_check, "source_check")
        _require_text(self.target_check, "target_check")
        _require_text(self.disposition, "disposition")

    def to_term(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal,
            "source_check": self.source_check,
            "target_check": self.target_check,
            "disposition": self.disposition,
        }


@dataclass(frozen=True, slots=True)
class OutcomeMapEntry:
    source_outcome: str
    target_outcome: str

    def __post_init__(self) -> None:
        if self.source_outcome not in (
            "Accept",
            "Reject",
        ) or self.target_outcome not in ("Accept", "Reject"):
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-034",
                "an outcome map uses only Accept or Reject",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "source_outcome": self.source_outcome,
            "target_outcome": self.target_outcome,
        }


@dataclass(frozen=True, slots=True)
class OracleCommitmentStaticMaps:
    """Complete static maps for the exact source/target Core pair."""

    public_environment_map: tuple[PublicEnvironmentMapEntry, ...]
    publication_map: tuple[PublicationMapEntry, ...]
    fresh_coin_map: tuple[FreshCoinMapEntry, ...]
    query_draw_map: tuple[QueryDrawMapEntry, ...]
    answer_opening_map: tuple[AnswerOpeningMapEntry, ...]
    scalar_terminal_map: ScalarTerminalMap
    check_map: tuple[CheckMapEntry, ...]
    outcome_map: tuple[OutcomeMapEntry, ...]

    def __post_init__(self) -> None:
        typed_sequences = (
            (self.public_environment_map, PublicEnvironmentMapEntry),
            (self.publication_map, PublicationMapEntry),
            (self.fresh_coin_map, FreshCoinMapEntry),
            (self.query_draw_map, QueryDrawMapEntry),
            (self.answer_opening_map, AnswerOpeningMapEntry),
            (self.check_map, CheckMapEntry),
            (self.outcome_map, OutcomeMapEntry),
        )
        if any(
            type(sequence) is not tuple
            or any(type(item) is not item_type for item in sequence)
            for sequence, item_type in typed_sequences
        ) or type(self.scalar_terminal_map) is not ScalarTerminalMap:
            raise malformed(
                "oracle-construction:map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-035",
                "static maps require exact immutable typed carriers",
            )
        ordinal_sequences = (
            tuple(item.coordinate_ordinal for item in self.public_environment_map),
            tuple(item.layer for item in self.publication_map),
            tuple(item.round_ordinal for item in self.fresh_coin_map),
            tuple(item.draw_ordinal for item in self.query_draw_map),
            tuple(item.occurrence_ordinal for item in self.answer_opening_map),
            tuple(item.ordinal for item in self.check_map),
        )
        for ordinals in ordinal_sequences:
            if len(ordinals) != len(set(ordinals)):
                raise malformed(
                    "oracle-construction:map-formation",
                    "FRI-IOR-CLASSICAL-CONSTRUCTION-036",
                    "a static map cannot duplicate its canonical ordinal",
                )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        return {
            "public_environment_map": [
                entry.to_term() for entry in self.public_environment_map
            ],
            "publication_map": [entry.to_term() for entry in self.publication_map],
            "fresh_coin_map": [entry.to_term() for entry in self.fresh_coin_map],
            "query_draw_map": [entry.to_term() for entry in self.query_draw_map],
            "answer_opening_map": [
                entry.to_term() for entry in self.answer_opening_map
            ],
            "scalar_terminal_map": self.scalar_terminal_map.to_term(),
            "check_map": [entry.to_term() for entry in self.check_map],
            "outcome_map": [entry.to_term() for entry in self.outcome_map],
        }


@dataclass(frozen=True, slots=True)
class CommitmentAdviceSchema:
    """Owner-local salt-advice shape, never a concrete advice assignment."""

    owner: str
    lifecycle: str
    binding_coordinates: tuple[str, ...]
    salts_per_layer: tuple[int, ...]
    salt_bytes: int
    public_projection: str
    portable_identity: bool

    def to_term(self) -> dict[str, Any]:
        return {
            "owner": self.owner,
            "lifecycle": self.lifecycle,
            "binding_coordinates": list(self.binding_coordinates),
            "salts_per_layer": list(self.salts_per_layer),
            "salt_bytes": self.salt_bytes,
            "public_projection": self.public_projection,
            "portable_identity": self.portable_identity,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "oracle-commitment-advice-schema",
            "classical-fri.oracle-commitment-advice-schema.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class PublicReplayClosure:
    """Exact public dependencies and forbidden private dependencies."""

    required_public_roles: tuple[str, ...]
    required_check_roles: tuple[str, ...]
    forbidden_private_roles: tuple[str, ...]

    def to_term(self) -> dict[str, Any]:
        return {
            "required_public_roles": list(self.required_public_roles),
            "required_check_roles": list(self.required_check_roles),
            "forbidden_private_roles": list(self.forbidden_private_roles),
        }


@dataclass(frozen=True, slots=True)
class IntrinsicConstructionBounds:
    """Profile semantics, not request-local checker budgets or measurements."""

    publication_roots: int
    fresh_coins: int
    query_draws: int
    logical_layer_query_occurrences: int
    max_unique_physical_openings: int
    owner_salt_leaves: int
    owner_salt_bytes: int
    commitment_leaf_hashes: int
    commitment_internal_hashes: int
    max_public_opening_leaf_hashes: int
    max_public_authentication_node_hashes: int
    max_public_authentication_sibling_digests: int
    max_public_opening_payload_bytes: int

    def to_term(self) -> dict[str, Any]:
        return {
            "publication_roots": self.publication_roots,
            "fresh_coins": self.fresh_coins,
            "query_draws": self.query_draws,
            "logical_layer_query_occurrences": (
                self.logical_layer_query_occurrences
            ),
            "max_unique_physical_openings": self.max_unique_physical_openings,
            "owner_salt_leaves": self.owner_salt_leaves,
            "owner_salt_bytes": self.owner_salt_bytes,
            "commitment_leaf_hashes": self.commitment_leaf_hashes,
            "commitment_internal_hashes": self.commitment_internal_hashes,
            "max_public_opening_leaf_hashes": (
                self.max_public_opening_leaf_hashes
            ),
            "max_public_authentication_node_hashes": (
                self.max_public_authentication_node_hashes
            ),
            "max_public_authentication_sibling_digests": (
                self.max_public_authentication_sibling_digests
            ),
            "max_public_opening_payload_bytes": (
                self.max_public_opening_payload_bytes
            ),
        }


def derive_oracle_commitment_static_maps() -> OracleCommitmentStaticMaps:
    """Deterministically elaborate all exact source/target occurrences."""

    public_environment = (
        PublicEnvironmentMapEntry(0, "statement", "statement", "Statement"),
        PublicEnvironmentMapEntry(
            1,
            "application_context",
            "application_context",
            "ApplicationContext",
        ),
    )
    publications = tuple(
        PublicationMapEntry(
            layer,
            f"G{layer}",
            f"M{layer}",
            CLASSICAL_DOMAINS[layer].identity,
        )
        for layer in range(FOLD_ROUNDS)
    )
    coins = tuple(
        FreshCoinMapEntry(
            round_ordinal,
            f"x{round_ordinal}",
            f"x{round_ordinal}",
            tuple(f"M{layer}" for layer in range(round_ordinal + 1)),
        )
        for round_ordinal in range(FOLD_ROUNDS)
    )
    draws = tuple(
        QueryDrawMapEntry(
            draw_ordinal,
            f"s0[{draw_ordinal}]",
            f"s0[{draw_ordinal}]",
        )
        for draw_ordinal in range(QUERY_REPETITIONS)
    )
    answers: list[AnswerOpeningMapEntry] = []
    for draw_ordinal in range(QUERY_REPETITIONS):
        for layer in range(FOLD_ROUNDS):
            occurrence = draw_ordinal * FOLD_ROUNDS + layer
            answers.append(
                AnswerOpeningMapEntry(
                    occurrence,
                    draw_ordinal,
                    layer,
                    f"query.{draw_ordinal}.layer.{layer}",
                    f"answer[{occurrence}]",
                    f"selector[{occurrence}]",
                    f"logical-opening[{occurrence}]",
                    "positive-then-antipodal-negative",
                    OPENING_TABLE_AUTHENTICATION_CHECK,
                )
            )
    preserved_checks = tuple(
        CheckMapEntry(
            occurrence,
            f"fold[{occurrence}]",
            f"fold[{occurrence}]",
            "preserved-fold-check",
        )
        for occurrence in range(LAYER_QUERY_OCCURRENCES)
    )
    inserted_checks = (
        CheckMapEntry(
            LAYER_QUERY_OCCURRENCES,
            None,
            OPENING_TABLE_AUTHENTICATION_CHECK,
            "inserted-bounded-physical-opening-authentication-check",
        ),
    )
    coverage_check = (
        CheckMapEntry(
            LAYER_QUERY_OCCURRENCES + 1,
            None,
            "opening-table-coverage-and-selector-check",
            "inserted-total-opening-coverage-check",
        ),
    )
    result = OracleCommitmentStaticMaps(
        public_environment,
        publications,
        coins,
        draws,
        tuple(answers),
        ScalarTerminalMap("C", "C", "GoldilocksElement"),
        preserved_checks + inserted_checks + coverage_check,
        (
            OutcomeMapEntry("Accept", "Accept"),
            OutcomeMapEntry("Reject", "Reject"),
        ),
    )
    encode_term(result.to_term())
    return result


def elaborate_committed_core(
    source_core: object,
    commitment_profile: object,
    maps: object,
) -> ClassicalCommittedCore:
    """Elaborate the exact committed target from admitted source semantics.

    The operation is deliberately bounded and non-generic.  It derives the
    target schedule from the total static maps; it does not copy the independently
    formed target singleton or accept an authored target body.
    """

    if type(source_core) is not ClassicalNativeCore:
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "oracle-construction:target-elaboration",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-021",
            "target elaboration requires the exact native Core carrier",
        )
    if type(commitment_profile) is not OracleCommitmentProfile:
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "oracle-construction:target-elaboration",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-022",
            "target elaboration requires the exact construction profile carrier",
        )
    if type(maps) is not OracleCommitmentStaticMaps:
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "oracle-construction:target-elaboration",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-023",
            "target elaboration requires the exact static-map carrier",
        )
    if source_core.identity != _exact_source_core_id():
        raise ModelFailure(
            OutcomeClass.UNSUPPORTED,
            "oracle-construction:target-elaboration",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-024",
            "the formed source Core is outside the one admitted bounded profile",
        )
    if commitment_profile != EXACT_ORACLE_COMMITMENT_PROFILE:
        raise ModelFailure(
            OutcomeClass.UNSUPPORTED,
            "oracle-construction:target-elaboration",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-025",
            "the formed commitment profile is outside the admitted construction",
        )
    expected_maps = derive_oracle_commitment_static_maps()
    if maps != expected_maps:
        raise ModelFailure(
            OutcomeClass.REFUSED,
            "oracle-construction:target-elaboration",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-026",
            "target elaboration refuses incomplete, stale, or reordered static maps",
        )

    schedule_items: list[tuple[str, str]] = []
    for publication, coin in zip(
        maps.publication_map,
        maps.fresh_coin_map,
        strict=True,
    ):
        schedule_items.append(("PublishMerkleRoot", publication.target_root))
        schedule_items.append(("PublicChallenge", coin.target_coin))
    schedule_items.extend(
        (
            ("PublishTerminalScalar", maps.scalar_terminal_map.target_terminal),
            ("PublicQueryVector", "s0[0..3]"),
            ("PublishOpeningTable", "openings"),
            ("AuthenticationAndFoldChecks", "checks"),
            ("Terminal", "AcceptOrReject"),
        )
    )
    schedule = tuple(
        ClassicalScheduleEvent(ordinal, kind, subject)
        for ordinal, (kind, subject) in enumerate(schedule_items)
    )
    return ClassicalCommittedCore(
        profile_id=commitment_profile.source_profile_id,
        source_core_id=source_core.identity,
        schedule=schedule,
        commitment_profile=commitment_profile.name,
    )


def derive_commitment_advice_schema() -> CommitmentAdviceSchema:
    schema = CommitmentAdviceSchema(
        owner="oracle-commitment-construction-prover",
        lifecycle="one-construction-invocation",
        binding_coordinates=(
            "construction-id",
            "oracle-publication-occurrence",
            "invocation-id",
        ),
        salts_per_layer=tuple(
            domain.order // 2 for domain in CLASSICAL_DOMAINS[:FOLD_ROUNDS]
        ),
        salt_bytes=SALT_BYTES,
        public_projection="only-salt-of-each-selected-physical-opening",
        portable_identity=True,
    )
    encode_term(schema.to_term())
    return schema


def derive_public_replay_closure() -> PublicReplayClosure:
    closure = PublicReplayClosure(
        required_public_roles=(
            "statement",
            "application-context",
            "M0",
            "x0",
            "M1",
            "x1",
            "M2",
            "x2",
            "C",
            "s0[0..3]",
            "canonical-deduplicated-opening-table",
            "12-total-occurrence-selectors",
        ),
        required_check_roles=(
            "opening-table-coverage",
            "opening-authentication",
            "three-layer-fold-consistency-per-draw",
            "scalar-terminal-equality",
            "accept-or-reject",
        ),
        forbidden_private_roles=(
            "complete-G0",
            "complete-G1",
            "complete-G2",
            "unopened-owner-salts",
            "owner-generation-input",
            "producer-run-receipt",
        ),
    )
    encode_term(closure.to_term())
    return closure


def derive_intrinsic_construction_bounds() -> IntrinsicConstructionBounds:
    pair_counts = tuple(
        domain.order // 2 for domain in CLASSICAL_DOMAINS[:FOLD_ROUNDS]
    )
    depths = tuple(int(log2(count)) for count in pair_counts)
    unique_per_layer = tuple(
        min(QUERY_REPETITIONS, count) for count in pair_counts
    )
    owner_leaves = sum(pair_counts)
    max_unique = sum(unique_per_layer)
    authentication_nodes = sum(
        unique * depth
        for unique, depth in zip(unique_per_layer, depths, strict=True)
    )
    # One physical opening contains two canonical u64 field elements, one
    # fixed-width salt, and its exact path of fixed-width sibling digests.
    opening_payload_bytes = sum(
        unique * (16 + SALT_BYTES + depth * DIGEST_BYTES)
        for unique, depth in zip(unique_per_layer, depths, strict=True)
    )
    result = IntrinsicConstructionBounds(
        publication_roots=FOLD_ROUNDS,
        fresh_coins=FOLD_ROUNDS,
        query_draws=QUERY_REPETITIONS,
        logical_layer_query_occurrences=LAYER_QUERY_OCCURRENCES,
        max_unique_physical_openings=max_unique,
        owner_salt_leaves=owner_leaves,
        owner_salt_bytes=owner_leaves * SALT_BYTES,
        commitment_leaf_hashes=owner_leaves,
        commitment_internal_hashes=sum(count - 1 for count in pair_counts),
        max_public_opening_leaf_hashes=max_unique,
        max_public_authentication_node_hashes=authentication_nodes,
        max_public_authentication_sibling_digests=authentication_nodes,
        max_public_opening_payload_bytes=opening_payload_bytes,
    )
    encode_term(result.to_term())
    return result


@dataclass(frozen=True, slots=True)
class OracleCommitmentConstructionDeclaration:
    source_profile_id: SemanticId
    source_core_id: SemanticId
    target_core_id: SemanticId
    commitment_profile: OracleCommitmentProfile
    maps: OracleCommitmentStaticMaps
    advice_schema: CommitmentAdviceSchema
    public_replay_closure: PublicReplayClosure
    intrinsic_bounds: IntrinsicConstructionBounds

    SUBJECT_KIND: ClassVar[str] = "oracle-commitment-construction"
    IDENTITY_DOMAIN: ClassVar[str] = (
        "classical-fri.oracle-commitment-construction.v1"
    )

    def __post_init__(self) -> None:
        _semantic_ref(self.source_profile_id, "source_profile_id")
        _semantic_ref(self.source_core_id, "source_core_id")
        _semantic_ref(self.target_core_id, "target_core_id")
        if type(self.commitment_profile) is not OracleCommitmentProfile:
            raise malformed(
                "oracle-construction:declaration-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-004",
                "the declaration requires an exact commitment-profile carrier",
            )
        if type(self.maps) is not OracleCommitmentStaticMaps:
            raise malformed(
                "oracle-construction:declaration-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-005",
                "the declaration requires exact typed static maps",
            )
        if type(self.advice_schema) is not CommitmentAdviceSchema:
            raise malformed(
                "oracle-construction:declaration-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-006",
                "the declaration requires an exact advice schema",
            )
        if type(self.public_replay_closure) is not PublicReplayClosure:
            raise malformed(
                "oracle-construction:declaration-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-007",
                "the declaration requires an exact public-replay closure",
            )
        if type(self.intrinsic_bounds) is not IntrinsicConstructionBounds:
            raise malformed(
                "oracle-construction:declaration-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-008",
                "the declaration requires exact intrinsic bounds",
            )
        encode_term(self.to_term())

    def to_term(self) -> dict[str, Any]:
        # Maps, replay closure, and concrete bounds are results of the named
        # closed laws.  They remain on the candidate carrier only so admission
        # can falsify stale witnesses; they are not authored semantic inputs.
        return {
            "schema": CONSTRUCTION_SCHEMA,
            "source_profile_id": _semantic_ref(
                self.source_profile_id, "source_profile_id"
            ),
            "source_core_id": _semantic_ref(self.source_core_id, "source_core_id"),
            "target_core_id": _semantic_ref(self.target_core_id, "target_core_id"),
            "commitment_profile_id": self.commitment_profile.identity.to_term(),
            "advice_schema_id": self.advice_schema.identity.to_term(),
            "static_elaboration_law": STATIC_ELABORATION_LAW,
            "intrinsic_bound_law": INTRINSIC_BOUND_LAW,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            self.SUBJECT_KIND,
            self.IDENTITY_DOMAIN,
            self.to_term(),
        )


EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION = (
    OracleCommitmentConstructionDeclaration(
        source_profile_id=EXACT_CLASSICAL_FRI_PROFILE.identity,
        source_core_id=_exact_source_core_id(),
        target_core_id=elaborate_committed_core(
            EXACT_CLASSICAL_NATIVE_CORE,
            EXACT_ORACLE_COMMITMENT_PROFILE,
            derive_oracle_commitment_static_maps(),
        ).identity,
        commitment_profile=EXACT_ORACLE_COMMITMENT_PROFILE,
        maps=derive_oracle_commitment_static_maps(),
        advice_schema=derive_commitment_advice_schema(),
        public_replay_closure=derive_public_replay_closure(),
        intrinsic_bounds=derive_intrinsic_construction_bounds(),
    )
)


class OracleCommitmentConstructionDefect(str, Enum):
    SOURCE_PROFILE_MISMATCH = "SourceProfileMismatch"
    SOURCE_CORE_MISMATCH = "SourceCoreMismatch"
    TARGET_CORE_MISMATCH = "TargetCoreMismatch"
    COMMITMENT_PROFILE_MISMATCH = "CommitmentProfileMismatch"
    MAP_COVERAGE_MISMATCH = "MapCoverageMismatch"
    ADVICE_OWNERSHIP_MISMATCH = "AdviceOwnershipMismatch"
    PUBLIC_REPLAY_DEPENDENCY_LEAK = "PublicReplayDependencyLeak"
    INTRINSIC_BOUND_MISMATCH = "IntrinsicBoundMismatch"


_CHECKED_CONSTRUCTION_TOKEN = object()
_RESULT_REF_TOKEN = object()


class OracleCommitmentResultRef:
    """Collision-free only by process-local object identity."""

    __slots__ = ("_authority",)

    def __init__(self, *, _token: object) -> None:
        if _token is not _RESULT_REF_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "oracle-construction:result-ref-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-037",
                "a result reference can be minted only by exact admission",
            )
        self._authority = _RESULT_REF_TOKEN

    def __repr__(self) -> str:
        return "OracleCommitmentResultRef(process_local=True)"

    def __copy__(self) -> None:
        raise TypeError("a process-local result reference cannot be copied")

    def __deepcopy__(self, memo: object) -> None:
        raise TypeError("a process-local result reference cannot be copied")

    def __reduce__(self) -> None:
        raise TypeError("a process-local result reference cannot be serialized")

    def __reduce_ex__(self, protocol: int) -> None:
        raise TypeError("a process-local result reference cannot be serialized")

    def __getstate__(self) -> None:
        raise TypeError("a process-local result reference has no portable state")


@dataclass(frozen=True, slots=True, init=False, eq=False)
class CheckedOracleCommitmentConstruction:
    """Owner-local affirmative result; neither a subject nor a receipt."""

    construction_id: SemanticId
    result_ref: OracleCommitmentResultRef
    construction_subject: OracleCommitmentConstructionDeclaration
    source_profile_id: SemanticId
    source_core_id: SemanticId
    target_core_id: SemanticId
    commitment_profile_id: SemanticId
    maps: OracleCommitmentStaticMaps
    advice_schema: CommitmentAdviceSchema
    public_replay_closure: PublicReplayClosure
    intrinsic_bounds: IntrinsicConstructionBounds
    _authority: object

    def __init__(
        self,
        declaration: OracleCommitmentConstructionDeclaration,
        *,
        _token: object,
    ) -> None:
        if _token is not _CHECKED_CONSTRUCTION_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "oracle-construction:checked-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-009",
                "a checked construction requires exact structural admission",
            )
        values = {
            "construction_id": declaration.identity,
            "result_ref": OracleCommitmentResultRef(_token=_RESULT_REF_TOKEN),
            "construction_subject": declaration,
            "source_profile_id": declaration.source_profile_id,
            "source_core_id": declaration.source_core_id,
            "target_core_id": declaration.target_core_id,
            "commitment_profile_id": declaration.commitment_profile.identity,
            "maps": declaration.maps,
            "advice_schema": declaration.advice_schema,
            "public_replay_closure": declaration.public_replay_closure,
            "intrinsic_bounds": declaration.intrinsic_bounds,
            "_authority": _CHECKED_CONSTRUCTION_TOKEN,
        }
        for name, value in values.items():
            object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return (
            "CheckedOracleCommitmentConstruction("
            f"construction_id={self.construction_id.to_text()}, process_local=True)"
        )

    def __copy__(self) -> None:
        raise TypeError("a checked process-local result cannot be copied")

    def __deepcopy__(self, memo: object) -> None:
        raise TypeError("a checked process-local result cannot be copied")

    def __reduce__(self) -> None:
        raise TypeError("a checked process-local result cannot be serialized")

    def __reduce_ex__(self, protocol: int) -> None:
        raise TypeError("a checked process-local result cannot be serialized")

    def __getstate__(self) -> None:
        raise TypeError("a checked process-local result has no portable state")


_CAPABILITY_TOKEN = object()


class OracleCommitmentCapability:
    """Fresh process-local authority for using one checked construction."""

    __slots__ = ("_authority", "_checked_construction")

    def __init__(
        self,
        checked_construction: CheckedOracleCommitmentConstruction,
        *,
        _token: object,
    ) -> None:
        if (
            _token is not _CAPABILITY_TOKEN
            or type(checked_construction) is not CheckedOracleCommitmentConstruction
            or checked_construction._authority is not _CHECKED_CONSTRUCTION_TOKEN
        ):
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "oracle-construction:capability-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-010",
                "a live capability can be minted only by exact admission",
            )
        self._authority = _CAPABILITY_TOKEN
        self._checked_construction = checked_construction

    @property
    def construction_id(self) -> SemanticId:
        return self._checked_construction.construction_id

    @property
    def checked_construction(self) -> CheckedOracleCommitmentConstruction:
        return self._checked_construction

    @property
    def construction_subject(self) -> OracleCommitmentConstructionDeclaration:
        return self._checked_construction.construction_subject

    def __repr__(self) -> str:
        return (
            "OracleCommitmentCapability("
            f"construction_id={self.construction_id.to_text()}, process_local=True)"
        )

    def __copy__(self) -> None:
        raise TypeError("an oracle-commitment capability cannot be copied")

    def __deepcopy__(self, memo: object) -> None:
        raise TypeError("an oracle-commitment capability cannot be copied")

    def __reduce__(self) -> None:
        raise TypeError("an oracle-commitment capability cannot be serialized")

    def __reduce_ex__(self, protocol: int) -> None:
        raise TypeError("an oracle-commitment capability cannot be serialized")

    def __getstate__(self) -> None:
        raise TypeError("an oracle-commitment capability has no portable state")


@dataclass(frozen=True, slots=True)
class OracleCommitmentConstructionAdmission:
    result: CheckResult
    checked_construction: CheckedOracleCommitmentConstruction | None
    capability: OracleCommitmentCapability | None

    def __post_init__(self) -> None:
        if not isinstance(self.result, CheckResult):
            raise TypeError("construction admission requires a CheckResult")
        if self.result.outcome is OutcomeClass.AFFIRMATIVE:
            if (
                type(self.checked_construction)
                is not CheckedOracleCommitmentConstruction
                or type(self.capability) is not OracleCommitmentCapability
            ):
                raise TypeError(
                    "affirmative construction admission requires checked "
                    "subject and capability"
                )
        elif self.checked_construction is not None or self.capability is not None:
            raise TypeError(
                "non-affirmative construction admission cannot carry authority"
            )


def _negative_admission(
    result: CheckResult,
) -> OracleCommitmentConstructionAdmission:
    return OracleCommitmentConstructionAdmission(result, None, None)


def _defect(
    code: str,
    detail: str,
    defect: OracleCommitmentConstructionDefect,
) -> OracleCommitmentConstructionAdmission:
    return _negative_admission(
        CheckResult(
            OutcomeClass.REFUSED,
            "oracle-construction:admission",
            code,
            detail,
            evidence={"defect": defect.value},
        )
    )


def admit_oracle_commitment_construction(
    declaration: object,
) -> OracleCommitmentConstructionAdmission:
    """Re-derive and admit exactly one reusable structural construction."""

    boundary = "oracle-construction:admission"
    if type(declaration) is not OracleCommitmentConstructionDeclaration:
        return _negative_admission(
            CheckResult(
                OutcomeClass.MALFORMED,
                boundary,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-011",
                "admission requires the exact declaration carrier",
            )
        )
    try:
        source_profile_id = EXACT_CLASSICAL_FRI_PROFILE.identity
        source_core_id = _exact_source_core_id()
        commitment_profile = EXACT_ORACLE_COMMITMENT_PROFILE
        maps = derive_oracle_commitment_static_maps()
        advice = derive_commitment_advice_schema()
        replay = derive_public_replay_closure()
        bounds = derive_intrinsic_construction_bounds()
        elaborated_target = elaborate_committed_core(
            EXACT_CLASSICAL_NATIVE_CORE,
            commitment_profile,
            maps,
        )
        target_core_id = semantic_id(
            "classical-fri-committed-core",
            "classical-fri.committed-core.v1",
            elaborated_target.to_term(),
        )

        # Re-derive the endpoint IDs directly from exact endpoint terms and
        # check their declared cross-edge before considering any candidate map.
        if EXACT_CLASSICAL_NATIVE_CORE.identity != source_core_id:
            raise RuntimeError("native Core identity implementation disagrees")
        if (
            elaborated_target.to_term()
            != EXACT_CLASSICAL_COMMITTED_CORE.to_term()
            or _exact_target_core_id() != target_core_id
            or EXACT_CLASSICAL_COMMITTED_CORE.identity != target_core_id
        ):
            raise RuntimeError("committed Core identity implementation disagrees")
        if (
            EXACT_CLASSICAL_COMMITTED_CORE.profile_id != source_profile_id
            or EXACT_CLASSICAL_COMMITTED_CORE.source_core_id != source_core_id
        ):
            raise RuntimeError("the exact target no longer elaborates the exact source")

        if declaration.source_profile_id != source_profile_id:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-012",
                "the declaration names a different classical FRI profile",
                OracleCommitmentConstructionDefect.SOURCE_PROFILE_MISMATCH,
            )
        if declaration.source_core_id != source_core_id:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-013",
                "the declaration names a different native source Core",
                OracleCommitmentConstructionDefect.SOURCE_CORE_MISMATCH,
            )
        if declaration.target_core_id != target_core_id:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-014",
                "the declaration names a different elaborated committed Core",
                OracleCommitmentConstructionDefect.TARGET_CORE_MISMATCH,
            )
        if declaration.commitment_profile != commitment_profile:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-015",
                "the declaration carries a different commitment profile",
                OracleCommitmentConstructionDefect.COMMITMENT_PROFILE_MISMATCH,
            )
        if declaration.maps != maps:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-016",
                "the declaration maps are not the re-derived exact total maps",
                OracleCommitmentConstructionDefect.MAP_COVERAGE_MISMATCH,
            )
        if declaration.advice_schema != advice:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-017",
                "the declaration changes owner-local advice shape or ownership",
                OracleCommitmentConstructionDefect.ADVICE_OWNERSHIP_MISMATCH,
            )
        if declaration.public_replay_closure != replay:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-018",
                "the declaration changes exact public replay dependencies",
                OracleCommitmentConstructionDefect.PUBLIC_REPLAY_DEPENDENCY_LEAK,
            )
        if declaration.intrinsic_bounds != bounds:
            return _defect(
                "FRI-IOR-CLASSICAL-CONSTRUCTION-019",
                "the declaration changes an intrinsic construction bound",
                OracleCommitmentConstructionDefect.INTRINSIC_BOUND_MISMATCH,
            )

        checked = CheckedOracleCommitmentConstruction(
            declaration,
            _token=_CHECKED_CONSTRUCTION_TOKEN,
        )
        capability = OracleCommitmentCapability(
            checked,
            _token=_CAPABILITY_TOKEN,
        )
        return OracleCommitmentConstructionAdmission(
            affirmative(
                boundary,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-100",
                "the exact reusable oracle-commitment construction is "
                "structurally admitted",
                subject=checked.construction_id,
                source_core_id=source_core_id,
                target_core_id=target_core_id,
                public_environment_coordinates=len(maps.public_environment_map),
                publication_roots=len(maps.publication_map),
                fresh_coins=len(maps.fresh_coin_map),
                query_draws=len(maps.query_draw_map),
                logical_opening_occurrences=len(maps.answer_opening_map),
                scope="profile-wide-structural-construction-only",
                concrete_run_validation_required=True,
            ),
            checked,
            capability,
        )
    except ModelFailure as error:
        return _negative_admission(error.to_result())
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return _negative_admission(
            checker_failure(
                boundary,
                f"unexpected construction-admission failure: {type(error).__name__}",
            )
        )


def _has_live_capability(value: object) -> bool:
    return (
        type(value) is OracleCommitmentCapability
        and value._authority is _CAPABILITY_TOKEN
        and type(value._checked_construction)
        is CheckedOracleCommitmentConstruction
        and value._checked_construction._authority is _CHECKED_CONSTRUCTION_TOKEN
    )


_ADVICE_TOKEN = object()


def _derive_run_invocation_id(
    construction_id: SemanticId,
    case: ClassicalCommittedCase,
) -> SemanticId:
    """Derive the invocation coordinate from the exact source/target pair."""

    return semantic_id(
        "oracle-commitment-invocation",
        "classical-fri.oracle-commitment-invocation.v1",
        {
            "construction_id": construction_id.to_term(),
            "source_execution_id": case.native_trace.identity.to_term(),
            "target_execution_id": case.fresh_run.identity.to_term(),
        },
    )


class OracleCommitmentAdvice:
    """One owner-local salt assignment bound to one admitted invocation."""

    __slots__ = (
        "_authority",
        "_construction_id",
        "_invocation_id",
        "_salts_by_layer",
    )

    def __init__(
        self,
        construction_id: SemanticId,
        invocation_id: SemanticId,
        salts_by_layer: tuple[tuple[bytes, ...], ...],
        *,
        _token: object,
    ) -> None:
        if _token is not _ADVICE_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "oracle-construction:advice-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-038",
                "construction advice requires a live admitted construction",
            )
        _semantic_ref(construction_id, "construction_id")
        _semantic_ref(invocation_id, "invocation_id")
        expected_counts = tuple(
            domain.order // 2 for domain in CLASSICAL_DOMAINS[:FOLD_ROUNDS]
        )
        if (
            type(salts_by_layer) is not tuple
            or len(salts_by_layer) != FOLD_ROUNDS
            or any(
                type(layer_salts) is not tuple
                or len(layer_salts) != expected_counts[layer]
                or any(
                    not isinstance(salt, bytes) or len(salt) != SALT_BYTES
                    for salt in layer_salts
                )
                for layer, layer_salts in enumerate(salts_by_layer)
            )
        ):
            raise malformed(
                "oracle-construction:advice-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-039",
                "owner advice requires exact 32, 16, and 8 leaf-salt tables",
            )
        self._authority = _ADVICE_TOKEN
        self._construction_id = construction_id
        self._invocation_id = invocation_id
        self._salts_by_layer = salts_by_layer

    @property
    def construction_id(self) -> SemanticId:
        return self._construction_id

    @property
    def invocation_id(self) -> SemanticId:
        return self._invocation_id

    @property
    def salts_by_layer(self) -> tuple[tuple[bytes, ...], ...]:
        return self._salts_by_layer

    def __repr__(self) -> str:
        return (
            "OracleCommitmentAdvice("
            f"construction_id={self.construction_id.to_text()}, "
            f"invocation_id={self.invocation_id.to_text()}, owner_local=True)"
        )

    def __copy__(self) -> None:
        raise TypeError("owner-local commitment advice cannot be copied")

    def __deepcopy__(self, memo: object) -> None:
        raise TypeError("owner-local commitment advice cannot be copied")

    def __reduce__(self) -> None:
        raise TypeError("owner-local commitment advice cannot be serialized")

    def __reduce_ex__(self, protocol: int) -> None:
        raise TypeError("owner-local commitment advice cannot be serialized")

    def __getstate__(self) -> None:
        raise TypeError("owner-local commitment advice has no portable state")


def form_oracle_commitment_advice(
    capability: object,
    case: object,
    salts_by_layer: object,
) -> OracleCommitmentAdvice:
    """Bind exact salt tables to one concrete source/target invocation pair."""

    if not _has_live_capability(capability):
        raise ModelFailure(
            OutcomeClass.MISSING_DEPENDENCY,
            "oracle-construction:advice-formation",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-040",
            "advice formation requires the live construction capability",
        )
    if type(case) is not ClassicalCommittedCase:
        raise ModelFailure(
            OutcomeClass.KIND_MISMATCH,
            "oracle-construction:advice-formation",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-057",
            "advice formation requires the exact source/target case carrier",
        )
    invocation_id = _derive_run_invocation_id(capability.construction_id, case)
    if type(salts_by_layer) is not tuple:
        raise malformed(
            "oracle-construction:advice-formation",
            "FRI-IOR-CLASSICAL-CONSTRUCTION-039",
            "owner advice requires exact immutable layer salt tables",
        )
    return OracleCommitmentAdvice(
        capability.construction_id,
        invocation_id,
        salts_by_layer,
        _token=_ADVICE_TOKEN,
    )


@dataclass(frozen=True, slots=True)
class ResourceUsageSnapshot:
    field_operations: int
    hash_calls: int
    hash_bytes: int
    merkle_nodes: int
    transcript_frames: int
    sampler_attempts: int
    grinding_trials: int
    logical_query_occurrences: int
    unique_openings: int
    proof_bytes: int

    @classmethod
    def from_mapping(cls, value: object) -> ResourceUsageSnapshot:
        if not isinstance(value, dict):
            raise malformed(
                "oracle-construction:resource-snapshot",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-041",
                "a resource snapshot requires the exact counter mapping",
            )
        expected_keys = tuple(ResourceLimits(0, 0, 0, 0, 0, 0, 0, 0, 0, 0).to_term())
        if tuple(value) != expected_keys or any(
            type(value[key]) is not int or value[key] < 0 for key in expected_keys
        ):
            raise malformed(
                "oracle-construction:resource-snapshot",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-041",
                "a resource snapshot requires every canonical non-negative coordinate",
            )
        return cls(**value)

    def to_term(self) -> dict[str, int]:
        return {
            "field_operations": self.field_operations,
            "hash_calls": self.hash_calls,
            "hash_bytes": self.hash_bytes,
            "merkle_nodes": self.merkle_nodes,
            "transcript_frames": self.transcript_frames,
            "sampler_attempts": self.sampler_attempts,
            "grinding_trials": self.grinding_trials,
            "logical_query_occurrences": self.logical_query_occurrences,
            "unique_openings": self.unique_openings,
            "proof_bytes": self.proof_bytes,
        }


@dataclass(frozen=True, slots=True)
class RunOccurrenceOpeningBinding:
    occurrence_ordinal: int
    occurrence_id: SemanticId
    opening_table_index: int
    opening_id: SemanticId

    def __post_init__(self) -> None:
        if (
            type(self.occurrence_ordinal) is not int
            or not 0 <= self.occurrence_ordinal < LAYER_QUERY_OCCURRENCES
            or type(self.opening_table_index) is not int
            or not 0 <= self.opening_table_index < LAYER_QUERY_OCCURRENCES
        ):
            raise malformed(
                "oracle-construction:run-map-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-042",
                "a run map requires bounded occurrence and opening coordinates",
            )
        _semantic_ref(self.occurrence_id, "occurrence_id")
        _semantic_ref(self.opening_id, "opening_id")

    def to_term(self) -> dict[str, Any]:
        return {
            "occurrence_ordinal": self.occurrence_ordinal,
            "occurrence_id": self.occurrence_id.to_term(),
            "opening_table_index": self.opening_table_index,
            "opening_id": self.opening_id.to_term(),
        }


_RUN_RECEIPT_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class OracleCommitmentRunReceipt:
    """Portable inert evidence for one checked source/target execution pair."""

    construction_id: SemanticId
    source_core_id: SemanticId
    target_core_id: SemanticId
    invocation_id: SemanticId
    source_execution_id: SemanticId
    target_execution_id: SemanticId
    public_environment_id: SemanticId
    publication_root_ids: tuple[SemanticId, ...]
    public_opening_ids: tuple[SemanticId, ...]
    occurrence_opening_map: tuple[RunOccurrenceOpeningBinding, ...]
    source_outcome: str
    target_outcome: str
    validation_limits: ResourceLimits
    source_resource_usage: ResourceUsageSnapshot
    target_resource_usage: ResourceUsageSnapshot
    construction_resource_usage: ResourceUsageSnapshot

    def __init__(
        self,
        *,
        construction_id: SemanticId,
        source_core_id: SemanticId,
        target_core_id: SemanticId,
        invocation_id: SemanticId,
        source_execution_id: SemanticId,
        target_execution_id: SemanticId,
        public_environment_id: SemanticId,
        publication_root_ids: tuple[SemanticId, ...],
        public_opening_ids: tuple[SemanticId, ...],
        occurrence_opening_map: tuple[RunOccurrenceOpeningBinding, ...],
        validation_limits: ResourceLimits,
        source_resource_usage: ResourceUsageSnapshot,
        target_resource_usage: ResourceUsageSnapshot,
        construction_resource_usage: ResourceUsageSnapshot,
        _token: object,
    ) -> None:
        if _token is not _RUN_RECEIPT_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "oracle-construction:run-receipt-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-043",
                "a run receipt requires the authoritative concrete pair checker",
            )
        for value, where in (
            (construction_id, "construction_id"),
            (source_core_id, "source_core_id"),
            (target_core_id, "target_core_id"),
            (invocation_id, "invocation_id"),
            (source_execution_id, "source_execution_id"),
            (target_execution_id, "target_execution_id"),
            (public_environment_id, "public_environment_id"),
        ):
            _semantic_ref(value, where)
        if (
            type(publication_root_ids) is not tuple
            or len(publication_root_ids) != FOLD_ROUNDS
            or any(
                type(identity) is not SemanticId
                for identity in publication_root_ids
            )
            or type(public_opening_ids) is not tuple
            or not 1 <= len(public_opening_ids) <= LAYER_QUERY_OCCURRENCES
            or any(type(identity) is not SemanticId for identity in public_opening_ids)
            or type(occurrence_opening_map) is not tuple
            or len(occurrence_opening_map) != LAYER_QUERY_OCCURRENCES
            or any(
                type(binding) is not RunOccurrenceOpeningBinding
                for binding in occurrence_opening_map
            )
            or tuple(
                binding.occurrence_ordinal for binding in occurrence_opening_map
            )
            != tuple(range(LAYER_QUERY_OCCURRENCES))
            or {
                binding.opening_table_index for binding in occurrence_opening_map
            }
            != set(range(len(public_opening_ids)))
            or any(
                binding.opening_id
                != public_opening_ids[binding.opening_table_index]
                for binding in occurrence_opening_map
            )
        ):
            raise malformed(
                "oracle-construction:run-receipt-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-058",
                "a receipt requires total roots, logical coordinates, and "
                "physical opening coverage",
            )
        if (
            type(validation_limits) is not ResourceLimits
            or type(source_resource_usage) is not ResourceUsageSnapshot
            or type(target_resource_usage) is not ResourceUsageSnapshot
            or type(construction_resource_usage) is not ResourceUsageSnapshot
        ):
            raise malformed(
                "oracle-construction:run-receipt-formation",
                "FRI-IOR-CLASSICAL-CONSTRUCTION-059",
                "a receipt requires exact immutable limits and three "
                "resource snapshots",
            )
        values = {
            "construction_id": construction_id,
            "source_core_id": source_core_id,
            "target_core_id": target_core_id,
            "invocation_id": invocation_id,
            "source_execution_id": source_execution_id,
            "target_execution_id": target_execution_id,
            "public_environment_id": public_environment_id,
            "publication_root_ids": publication_root_ids,
            "public_opening_ids": public_opening_ids,
            "occurrence_opening_map": occurrence_opening_map,
            "source_outcome": "Accept",
            "target_outcome": "Accept",
            "validation_limits": validation_limits,
            "source_resource_usage": source_resource_usage,
            "target_resource_usage": target_resource_usage,
            "construction_resource_usage": construction_resource_usage,
        }
        for name, value in values.items():
            object.__setattr__(self, name, value)
        encode_term(self.to_term())

    def semantic_receipt_term(self) -> dict[str, Any]:
        return {
            "construction_id": self.construction_id.to_term(),
            "source_core_id": self.source_core_id.to_term(),
            "target_core_id": self.target_core_id.to_term(),
            "invocation_id": self.invocation_id.to_term(),
            "source_execution_id": self.source_execution_id.to_term(),
            "target_execution_id": self.target_execution_id.to_term(),
            "public_environment_id": self.public_environment_id.to_term(),
            "publication_root_ids": [
                identity.to_term() for identity in self.publication_root_ids
            ],
            "public_opening_ids": [
                identity.to_term() for identity in self.public_opening_ids
            ],
            "occurrence_opening_map": [
                entry.to_term() for entry in self.occurrence_opening_map
            ],
            "source_outcome": self.source_outcome,
            "target_outcome": self.target_outcome,
            "conclusion": "ThisExecutionForwardMapped",
        }

    @property
    def semantic_receipt_id(self) -> SemanticId:
        return semantic_id(
            "oracle-commitment-run-receipt",
            "classical-fri.oracle-commitment-run-receipt.v1",
            self.semantic_receipt_term(),
        )

    def validation_basis_term(self) -> dict[str, Any]:
        return {
            "semantic_receipt_id": self.semantic_receipt_id.to_term(),
            "validation_operation": (
                "exact-source-target-replay-and-root-reconstruction.v1"
            ),
            "selected_limits": self.validation_limits.to_term(),
            "source_resource_usage": self.source_resource_usage.to_term(),
            "target_resource_usage": self.target_resource_usage.to_term(),
            "construction_resource_usage": (
                self.construction_resource_usage.to_term()
            ),
        }

    @property
    def validation_basis_id(self) -> SemanticId:
        return semantic_id(
            "oracle-commitment-run-validation-basis",
            "classical-fri.oracle-commitment-run-validation-basis.v1",
            self.validation_basis_term(),
        )

    def to_term(self) -> dict[str, Any]:
        """Return the inert aggregate; the aggregate intentionally has no ID."""

        return {
            "schema": RUN_RECEIPT_SCHEMA,
            "semantic_receipt_id": self.semantic_receipt_id.to_term(),
            "semantic_receipt": self.semantic_receipt_term(),
            "validation_basis_id": self.validation_basis_id.to_term(),
            "validation_basis": self.validation_basis_term(),
        }


@dataclass(frozen=True, slots=True)
class OracleCommitmentRunAdmission:
    result: CheckResult
    receipt: OracleCommitmentRunReceipt | None

    def __post_init__(self) -> None:
        if not isinstance(self.result, CheckResult):
            raise TypeError("run admission requires a CheckResult")
        if self.result.outcome is OutcomeClass.AFFIRMATIVE:
            if type(self.receipt) is not OracleCommitmentRunReceipt:
                raise TypeError(
                    "affirmative run admission requires its checked receipt"
                )
        elif self.receipt is not None:
            raise TypeError("non-affirmative run admission cannot carry a receipt")


def _negative_run(result: CheckResult) -> OracleCommitmentRunAdmission:
    return OracleCommitmentRunAdmission(result, None)


def _run_failure(
    outcome: OutcomeClass,
    code: str,
    detail: str,
) -> OracleCommitmentRunAdmission:
    return _negative_run(
        CheckResult(
            outcome,
            "oracle-construction:run-check",
            code,
            detail,
        )
    )


def _resource_snapshot(result: CheckResult) -> ResourceUsageSnapshot:
    return ResourceUsageSnapshot.from_mapping(result.evidence.get("resources"))


def check_oracle_commitment_run(
    capability: object,
    case: object,
    advice: object,
    limits: object = DEFAULT_CLASSICAL_LIMITS,
) -> OracleCommitmentRunAdmission:
    """Check one exact native-to-committed Fresh execution under live authority."""

    boundary = "oracle-construction:run-check"
    if not _has_live_capability(capability):
        return _run_failure(
            OutcomeClass.MISSING_DEPENDENCY,
            "FRI-IOR-CLASSICAL-CONSTRUCTION-044",
            "concrete construction checking requires the live capability",
        )
    if type(case) is not ClassicalCommittedCase:
        return _run_failure(
            OutcomeClass.MALFORMED,
            "FRI-IOR-CLASSICAL-CONSTRUCTION-045",
            "concrete construction checking requires the exact case carrier",
        )
    if (
        type(advice) is not OracleCommitmentAdvice
        or advice._authority is not _ADVICE_TOKEN
    ):
        return _run_failure(
            OutcomeClass.MISSING_DEPENDENCY,
            "FRI-IOR-CLASSICAL-CONSTRUCTION-046",
            "concrete construction checking requires live owner-local advice",
        )
    if type(limits) is not ResourceLimits:
        return _run_failure(
            OutcomeClass.MALFORMED,
            "FRI-IOR-CLASSICAL-CONSTRUCTION-047",
            "construction checking requires exact immutable resource limits",
        )

    try:
        if advice.construction_id != capability.construction_id:
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-048",
                "owner advice is bound to a different admitted construction",
            )
        if advice.salts_by_layer != case.owner_salts:
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-049",
                "owner advice does not exactly match this construction invocation",
            )
        if advice.invocation_id != _derive_run_invocation_id(
            capability.construction_id,
            case,
        ):
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-060",
                "owner advice is bound to a different source/target invocation pair",
            )
        if (
            type(case.native_trace) is not ClassicalNativeTrace
            or type(case.fresh_run) is not ClassicalCommittedRun
            or case.fresh_run.interpretation != FRESH_INTERPRETATION
        ):
            return _run_failure(
                OutcomeClass.KIND_MISMATCH,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-050",
                "the construction pair must be native source and committed "
                "Fresh target",
            )

        source_result = verify_native_trace(case.native_trace, limits)
        if source_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _negative_run(source_result)
        target_result = verify_committed_run(case.fresh_run, limits)
        if target_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return _negative_run(target_result)

        trace = case.native_trace
        target = case.fresh_run
        proof = target.proof
        if (
            source_result.subject != trace.identity
            or target_result.subject != target.identity
            or source_result.evidence.get("terminal") != "Accept"
            or target_result.evidence.get("terminal") != "Accept"
        ):
            return _run_failure(
                OutcomeClass.CHECKER_FAILURE,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-061",
                "an endpoint checker returned an inconsistent subject or "
                "terminal outcome",
            )
        if (
            trace.native_core_id != capability.checked_construction.source_core_id
            or target.committed_core_id
            != capability.checked_construction.target_core_id
            or target.public_inputs.profile_id
            != capability.checked_construction.source_profile_id
            or proof.committed_core_id
            != capability.checked_construction.target_core_id
        ):
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-051",
                "the concrete runs do not instantiate the admitted endpoint pair",
            )
        if trace.public_environment != target.public_environment:
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-064",
                "source and target runs do not carry the same exact Statement "
                "and application context",
            )

        construction_resources = ResourceCounter(limits)
        rebuilt_trees = tuple(
            build_classical_commitment(
                oracle,
                advice.salts_by_layer[layer],
                construction_resources,
            )
            for layer, oracle in enumerate(trace.oracles)
        )
        rebuilt_roots = tuple(tree.root for tree in rebuilt_trees)
        if rebuilt_roots != proof.roots:
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-052",
                "source oracles and owner advice do not reconstruct all target roots",
            )

        if (
            trace.fold_challenges != target.fold_challenges
            or trace.query_indices != target.query_indices
            or trace.terminal_scalar != proof.terminal_scalar
            or trace.query_occurrences
            != derive_layer_query_occurrences(target.query_indices)
        ):
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-053",
                "Fresh coins, ordered query vector, occurrences, or scalar "
                "do not commute",
            )

        expected_opening_keys = tuple(
            sorted(
                {
                    (occurrence.layer, occurrence.pair_index)
                    for occurrence in trace.query_occurrences
                }
            )
        )
        if tuple(opening.key for opening in proof.opening_table) != expected_opening_keys:
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-065",
                "the target physical opening table is not the canonical "
                "run-derived deduplication of logical openings",
            )
        opening_index_by_key = {
            key: index for index, key in enumerate(expected_opening_keys)
        }

        bindings: list[RunOccurrenceOpeningBinding] = []
        for occurrence, selector in zip(
            trace.query_occurrences,
            proof.occurrence_selectors,
            strict=True,
        ):
            if (
                selector.occurrence_ordinal != occurrence.ordinal
                or selector.opening_index
                != opening_index_by_key[(occurrence.layer, occurrence.pair_index)]
            ):
                return _run_failure(
                    OutcomeClass.REFUSED,
                    "FRI-IOR-CLASSICAL-CONSTRUCTION-054",
                    "an occurrence selector does not preserve its exact "
                    "logical occurrence",
                )
            opening = proof.opening_table[selector.opening_index]
            oracle = trace.oracles[occurrence.layer]
            half = oracle.domain.order // 2
            if (
                opening.key != (occurrence.layer, occurrence.pair_index)
                or opening.positive != oracle.values[occurrence.pair_index]
                or opening.negative
                != oracle.values[occurrence.pair_index + half]
            ):
                return _run_failure(
                    OutcomeClass.REFUSED,
                    "FRI-IOR-CLASSICAL-CONSTRUCTION-055",
                    "an authenticated target opening extracts a different "
                    "logical answer",
                )
            bindings.append(
                RunOccurrenceOpeningBinding(
                    occurrence.ordinal,
                    occurrence.identity,
                    selector.opening_index,
                    opening.identity,
                )
            )

        construction_resources.consume_logical_query_occurrences(
            LAYER_QUERY_OCCURRENCES
        )
        construction_resources.consume_unique_openings(len(proof.opening_table))
        construction_snapshot = ResourceUsageSnapshot.from_mapping(
            construction_resources.snapshot()
        )
        intrinsic = capability.checked_construction.intrinsic_bounds
        if (
            len(rebuilt_roots) != intrinsic.publication_roots
            or len(bindings) != intrinsic.logical_layer_query_occurrences
            or len(proof.opening_table) > intrinsic.max_unique_physical_openings
            or construction_snapshot.hash_calls
            != intrinsic.commitment_leaf_hashes
            + intrinsic.commitment_internal_hashes
        ):
            return _run_failure(
                OutcomeClass.REFUSED,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-056",
                "the concrete construction exceeds or contradicts intrinsic bounds",
            )

        receipt = OracleCommitmentRunReceipt(
            construction_id=capability.construction_id,
            source_core_id=capability.checked_construction.source_core_id,
            target_core_id=capability.checked_construction.target_core_id,
            invocation_id=advice.invocation_id,
            source_execution_id=trace.identity,
            target_execution_id=target.identity,
            public_environment_id=trace.public_environment.identity,
            publication_root_ids=tuple(root.identity for root in proof.roots),
            public_opening_ids=tuple(
                opening.identity for opening in proof.opening_table
            ),
            occurrence_opening_map=tuple(bindings),
            validation_limits=limits,
            source_resource_usage=_resource_snapshot(source_result),
            target_resource_usage=_resource_snapshot(target_result),
            construction_resource_usage=construction_snapshot,
            _token=_RUN_RECEIPT_TOKEN,
        )
        return OracleCommitmentRunAdmission(
            affirmative(
                boundary,
                "FRI-IOR-CLASSICAL-CONSTRUCTION-101",
                "one exact native and committed Fresh execution commutes "
                "under the admitted construction",
                subject=receipt.semantic_receipt_id,
                construction_id=receipt.construction_id,
                validation_basis_id=receipt.validation_basis_id,
                public_environment_id=receipt.public_environment_id,
                publication_roots=len(receipt.publication_root_ids),
                logical_opening_occurrences=len(receipt.occurrence_opening_map),
                unique_physical_openings=len(proof.opening_table),
                scope="one-execution",
            ),
            receipt,
        )
    except ModelFailure as error:
        return _negative_run(error.to_result())
    except Exception as error:  # pragma: no cover - fail-closed boundary
        return _negative_run(
            checker_failure(
                boundary,
                "unexpected concrete construction-checker failure: "
                f"{type(error).__name__}",
            )
        )


__all__ = [
    "AnswerOpeningMapEntry",
    "CheckMapEntry",
    "CheckedOracleCommitmentConstruction",
    "CommitmentAdviceSchema",
    "CONSTRUCTION_NONCLAIMS",
    "EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION",
    "EXACT_ORACLE_COMMITMENT_PROFILE",
    "FreshCoinMapEntry",
    "IntrinsicConstructionBounds",
    "OracleCommitmentAdvice",
    "OracleCommitmentCapability",
    "OracleCommitmentConstructionAdmission",
    "OracleCommitmentConstructionDeclaration",
    "OracleCommitmentConstructionDefect",
    "OracleCommitmentProfile",
    "OracleCommitmentResultRef",
    "OracleCommitmentRunAdmission",
    "OracleCommitmentRunReceipt",
    "OracleCommitmentStaticMaps",
    "OutcomeMapEntry",
    "PublicReplayClosure",
    "PublicationMapEntry",
    "QueryDrawMapEntry",
    "ResourceUsageSnapshot",
    "RunOccurrenceOpeningBinding",
    "ScalarTerminalMap",
    "admit_oracle_commitment_construction",
    "check_oracle_commitment_run",
    "derive_commitment_advice_schema",
    "derive_intrinsic_construction_bounds",
    "derive_oracle_commitment_static_maps",
    "derive_public_replay_closure",
    "elaborate_committed_core",
    "form_oracle_commitment_advice",
]
