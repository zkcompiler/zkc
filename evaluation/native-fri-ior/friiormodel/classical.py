"""Exact finite control for the scalar-terminal classical FRI protocol.

This module is intentionally additive to the earlier structural FRI witness.
It instantiates the three-fold, scalar-terminal shape of Algorithm 1 from
ePrint 2023/1071 over a theorem-shaped Goldilocks subgroup.  The native
logical-oracle protocol, its concrete commitment profile, and Fresh versus
Fiat--Shamir challenge interpretations remain separate semantic subjects.

The executable control establishes only formation, causal scheduling,
authentication, and one-run verifier acceptance.  It does not establish a
FRI proximity theorem, Merkle binding, or Fiat--Shamir security.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
from typing import Any

from .terms import (
    CheckResult,
    ModelFailure,
    ResourceCounter,
    ResourceLimits,
    SemanticId,
    affirmative,
    checker_failure,
    deterministic_limit_failure,
    encode_term,
    malformed,
    refusal,
    semantic_id,
)


GOLDILOCKS_MODULUS = (1 << 64) - (1 << 32) + 1
GOLDILOCKS_GENERATOR = 11
DOMAIN_ORDERS = (64, 32, 16, 8)
DOMAIN_GENERATORS = (512, 262144, 68719476736, 1099511627520)
DEGREE_BOUNDS = (8, 4, 2, 1)
FOLD_ROUNDS = 3
QUERY_REPETITIONS = 4
LAYER_QUERY_OCCURRENCES = FOLD_ROUNDS * QUERY_REPETITIONS
SALT_BYTES = 16
DIGEST_BYTES = hashlib.sha256().digest_size
MAX_FS_SAMPLER_ATTEMPTS = 64

LEAF_HASH_DOMAIN = b"zkc.classical-fri.pair-leaf.v1\x00"
NODE_HASH_DOMAIN = b"zkc.classical-fri.merkle-node.v1\x00"
FS_FOLD_DOMAIN = b"zkc.classical-fri.fs.fold-challenge.v1\x00"
FS_QUERY_DOMAIN = b"zkc.classical-fri.fs.query-index.v1\x00"
SALT_DERIVATION_DOMAIN = b"zkc.classical-fri.owner-salt.v1\x00"
FIELD_CODEC = "unsigned-u64be-less-than-goldilocks-modulus"
PAIR_INDEX_CODEC = "unsigned-u16be"
SALT_CODEC = "exactly-16-opaque-bytes"
DIGEST_CODEC = "exactly-32-sha256-bytes"
TRANSCRIPT_TERM_CODEC = "zkc.fri-ior.closed-finite-term.v1"
PUBLIC_ENVIRONMENT_SCHEMA = "zkc.classical-fri.public-environment.v1"
PUBLIC_INPUT_SCHEMA = "zkc.classical-fri.public-inputs.v1"
PUBLIC_PROOF_SCHEMA = "zkc.classical-fri.public-proof.v1"
FS_PREFIX_SCHEMA = "zkc.classical-fri.fs-prefix.v1"
FRESH_INTERPRETATION = "Fresh"
FIAT_SHAMIR_INTERPRETATION = "FiatShamirStrong"
FS_FOLD_LABELS = ("x0", "x1", "x2")
FS_QUERY_LABELS = ("s0.0", "s0.1", "s0.2", "s0.3")
DEFAULT_STATEMENT = {
    "claim": "degree-below-eight-on-goldilocks-l0",
    "public_instance": 7,
}
DEFAULT_APPLICATION_CONTEXT = {
    "application": "zkc-exact-classical-fri-control",
    "version": 1,
}
DEFAULT_SALT_SEED = b"zkc-classical-fri-owner-seed-v1"


DEFAULT_CLASSICAL_LIMITS = ResourceLimits(
    field_operations=1024,
    hash_calls=256,
    hash_bytes=1 << 16,
    merkle_nodes=192,
    transcript_frames=32,
    sampler_attempts=64,
    grinding_trials=0,
    logical_query_occurrences=LAYER_QUERY_OCCURRENCES,
    unique_openings=LAYER_QUERY_OCCURRENCES,
    proof_bytes=1 << 15,
)


@dataclass(frozen=True, slots=True)
class GoldilocksElement:
    """A canonical element of the Goldilocks prime field."""

    value: int

    def __post_init__(self) -> None:
        if type(self.value) is not int or not 0 <= self.value < GOLDILOCKS_MODULUS:
            raise malformed(
                "classical-fri:field-formation",
                "FRI-IOR-CLASSICAL-FIELD-001",
                "a Goldilocks representative must be an integer below the modulus",
            )

    @classmethod
    def reduce(cls, value: int) -> "GoldilocksElement":
        if type(value) is not int:
            raise malformed(
                "classical-fri:field-formation",
                "FRI-IOR-CLASSICAL-FIELD-001",
                "only an integer can be reduced into the Goldilocks field",
            )
        return cls(value % GOLDILOCKS_MODULUS)

    @classmethod
    def from_bytes(cls, encoded: bytes) -> "GoldilocksElement":
        if not isinstance(encoded, bytes) or len(encoded) != 8:
            raise malformed(
                "classical-fri:field-codec",
                "FRI-IOR-CLASSICAL-FIELD-002",
                "a Goldilocks element requires exactly eight big-endian bytes",
            )
        value = int.from_bytes(encoded, "big")
        if value >= GOLDILOCKS_MODULUS:
            raise malformed(
                "classical-fri:field-codec",
                "FRI-IOR-CLASSICAL-FIELD-002",
                "a Goldilocks encoding must be canonical",
            )
        return cls(value)

    def to_bytes(self) -> bytes:
        return self.value.to_bytes(8, "big")

    def to_term(self) -> int:
        return self.value

    def __int__(self) -> int:
        return self.value

    def __add__(self, other: object) -> "GoldilocksElement":
        if not isinstance(other, GoldilocksElement):
            return NotImplemented
        return GoldilocksElement.reduce(self.value + other.value)

    def __sub__(self, other: object) -> "GoldilocksElement":
        if not isinstance(other, GoldilocksElement):
            return NotImplemented
        return GoldilocksElement.reduce(self.value - other.value)

    def __mul__(self, other: object) -> "GoldilocksElement":
        if not isinstance(other, GoldilocksElement):
            return NotImplemented
        return GoldilocksElement.reduce(self.value * other.value)

    def __neg__(self) -> "GoldilocksElement":
        return GoldilocksElement.reduce(-self.value)

    def __pow__(self, exponent: int) -> "GoldilocksElement":
        if type(exponent) is not int or exponent < 0:
            raise malformed(
                "classical-fri:field-exponentiation",
                "FRI-IOR-CLASSICAL-FIELD-003",
                "a field exponent must be a non-negative integer",
            )
        return GoldilocksElement(pow(self.value, exponent, GOLDILOCKS_MODULUS))

    def inverse(self) -> "GoldilocksElement":
        if self.value == 0:
            raise refusal(
                "classical-fri:field-inverse",
                "FRI-IOR-CLASSICAL-FIELD-004",
                "zero has no field inverse",
            )
        return GoldilocksElement(
            pow(self.value, GOLDILOCKS_MODULUS - 2, GOLDILOCKS_MODULUS)
        )

    def __truediv__(self, other: object) -> "GoldilocksElement":
        if not isinstance(other, GoldilocksElement):
            return NotImplemented
        return self * other.inverse()


ZERO = GoldilocksElement(0)
ONE = GoldilocksElement(1)
TWO_INVERSE = GoldilocksElement(2).inverse()


@dataclass(frozen=True, slots=True)
class ClassicalFriDomain:
    """One exact multiplicative domain in the three-fold squaring chain."""

    layer: int
    generator: GoldilocksElement
    order: int

    def __post_init__(self) -> None:
        if type(self.layer) is not int or not 0 <= self.layer <= FOLD_ROUNDS:
            raise malformed(
                "classical-fri:domain-formation",
                "FRI-IOR-CLASSICAL-PROFILE-001",
                "a classical FRI domain layer must be in [0, 3]",
            )
        if not isinstance(self.generator, GoldilocksElement):
            raise malformed(
                "classical-fri:domain-formation",
                "FRI-IOR-CLASSICAL-PROFILE-002",
                "a domain generator must be a Goldilocks element",
            )
        if type(self.order) is not int or self.order != DOMAIN_ORDERS[self.layer]:
            raise malformed(
                "classical-fri:domain-formation",
                "FRI-IOR-CLASSICAL-PROFILE-003",
                "a domain order must match the exact three-fold profile",
            )
        if (
            self.generator**self.order != ONE
            or self.generator ** (self.order // 2) == ONE
        ):
            raise malformed(
                "classical-fri:domain-formation",
                "FRI-IOR-CLASSICAL-PROFILE-004",
                "the declared generator does not have the exact domain order",
            )

    @property
    def name(self) -> str:
        return f"goldilocks-l{self.layer}"

    def points(self) -> tuple[GoldilocksElement, ...]:
        return tuple(self.generator**index for index in range(self.order))

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer,
            "name": self.name,
            "generator": self.generator.to_term(),
            "order": self.order,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-domain",
            "classical-fri.domain.v1",
            self.to_term(),
        )


CLASSICAL_DOMAINS = tuple(
    ClassicalFriDomain(layer, GoldilocksElement(generator), order)
    for layer, (generator, order) in enumerate(zip(DOMAIN_GENERATORS, DOMAIN_ORDERS))
)


@dataclass(frozen=True, slots=True)
class ClassicalFriProfile:
    """The exact source-shaped finite Algorithm 1 control profile."""

    name: str
    field_modulus: int
    domains: tuple[ClassicalFriDomain, ...]
    degree_bounds: tuple[int, ...]
    query_repetitions: int
    source_anchor: str

    def __post_init__(self) -> None:
        if self.name != "goldilocks-three-fold-scalar-terminal-v1":
            raise malformed(
                "classical-fri:profile-formation",
                "FRI-IOR-CLASSICAL-PROFILE-005",
                "the exact profile name is fixed",
            )
        if self.field_modulus != GOLDILOCKS_MODULUS:
            raise malformed(
                "classical-fri:profile-formation",
                "FRI-IOR-CLASSICAL-PROFILE-006",
                "the exact profile requires the Goldilocks modulus",
            )
        if type(self.domains) is not tuple or self.domains != CLASSICAL_DOMAINS:
            raise malformed(
                "classical-fri:profile-formation",
                "FRI-IOR-CLASSICAL-PROFILE-007",
                "the exact profile requires the complete ordered domain chain",
            )
        if self.degree_bounds != DEGREE_BOUNDS:
            raise malformed(
                "classical-fri:profile-formation",
                "FRI-IOR-CLASSICAL-PROFILE-008",
                "the exact degree chain is (8, 4, 2, 1)",
            )
        if self.query_repetitions != QUERY_REPETITIONS:
            raise malformed(
                "classical-fri:profile-formation",
                "FRI-IOR-CLASSICAL-PROFILE-009",
                "the exact control has four labelled query repetitions",
            )
        if self.source_anchor != "eprint-2023-1071-r7-section-5.7-algorithm-1":
            raise malformed(
                "classical-fri:profile-formation",
                "FRI-IOR-CLASSICAL-PROFILE-010",
                "the exact control must retain its selected source anchor",
            )
        for previous, following in zip(self.domains, self.domains[1:]):
            if previous.generator * previous.generator != following.generator:
                raise malformed(
                    "classical-fri:profile-formation",
                    "FRI-IOR-CLASSICAL-PROFILE-011",
                    "each following domain generator must square from its predecessor",
                )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "field": {
                "name": "goldilocks-prime-field",
                "modulus": self.field_modulus,
                "canonical_codec": "unsigned-u64be-less-than-modulus",
            },
            "domains": [domain.to_term() for domain in self.domains],
            "degree_bounds_exclusive": list(self.degree_bounds),
            "fold_rounds": FOLD_ROUNDS,
            "terminal": "one-base-field-scalar",
            "query_repetitions": self.query_repetitions,
            "source_anchor": self.source_anchor,
            "nonclaims": [
                "no-proximity-theorem",
                "no-commitment-binding",
                "no-fiat-shamir-security",
            ],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-profile",
            "classical-fri.profile.v1",
            self.to_term(),
        )


EXACT_CLASSICAL_FRI_PROFILE = ClassicalFriProfile(
    name="goldilocks-three-fold-scalar-terminal-v1",
    field_modulus=GOLDILOCKS_MODULUS,
    domains=CLASSICAL_DOMAINS,
    degree_bounds=DEGREE_BOUNDS,
    query_repetitions=QUERY_REPETITIONS,
    source_anchor="eprint-2023-1071-r7-section-5.7-algorithm-1",
)


@dataclass(frozen=True, slots=True)
class ClassicalPublicEnvironment:
    """Exact public coordinates shared by native, Fresh, and FS executions.

    The carrier is protocol input, not transcript-derived state.  Strong FS
    additionally absorbs these coordinates, while Fresh receives its coins
    independently from the same public environment.
    """

    statement: bytes
    application_context: bytes
    profile_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_FRI_PROFILE.identity
    )
    schema: str = PUBLIC_ENVIRONMENT_SCHEMA

    def __post_init__(self) -> None:
        if (
            not isinstance(self.statement, bytes)
            or not self.statement
            or not isinstance(self.application_context, bytes)
            or not self.application_context
        ):
            raise malformed(
                "classical-fri:public-environment-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-005",
                "Statement and application context require non-empty canonical term bytes",
            )
        if len(self.statement) > 1 << 14 or len(self.application_context) > 1 << 14:
            raise malformed(
                "classical-fri:public-environment-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-006",
                "a public-environment coordinate exceeds the exact profile bound",
            )
        if not isinstance(self.profile_id, SemanticId):
            raise malformed(
                "classical-fri:public-environment-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-007",
                "the public environment requires a typed profile identity",
            )
        if self.schema != PUBLIC_ENVIRONMENT_SCHEMA:
            raise malformed(
                "classical-fri:public-environment-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-008",
                "the public-environment schema is fixed",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "profile_id": self.profile_id.to_term(),
            "coordinates": [
                {
                    "name": "statement",
                    "semantic_purpose": "Statement",
                    "visibility": "Public",
                    "canonical_value": self.statement.hex(),
                },
                {
                    "name": "application_context",
                    "semantic_purpose": "ApplicationContext",
                    "visibility": "Public",
                    "canonical_value": self.application_context.hex(),
                },
            ],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-public-environment",
            "classical-fri.public-environment.v1",
            self.to_term(),
        )

    def _coordinate_id(self, name: str, purpose: str, value: bytes) -> SemanticId:
        return semantic_id(
            "classical-fri-public-environment-coordinate",
            "classical-fri.public-environment-coordinate.v1",
            {
                "public_environment_id": self.identity.to_term(),
                "name": name,
                "semantic_purpose": purpose,
                "visibility": "Public",
                "canonical_value": value.hex(),
            },
        )

    @property
    def statement_coordinate_id(self) -> SemanticId:
        return self._coordinate_id("statement", "Statement", self.statement)

    @property
    def application_context_coordinate_id(self) -> SemanticId:
        return self._coordinate_id(
            "application_context",
            "ApplicationContext",
            self.application_context,
        )


def form_classical_public_environment(
    statement: Any,
    application_context: Any,
) -> ClassicalPublicEnvironment:
    return ClassicalPublicEnvironment(
        statement=encode_term(statement),
        application_context=encode_term(application_context),
    )


def _public_environment_coordinate_schema() -> list[dict[str, str]]:
    return [
        {
            "name": "statement",
            "semantic_purpose": "Statement",
            "visibility": "Public",
            "value_type": "CanonicalTermBytes",
        },
        {
            "name": "application_context",
            "semantic_purpose": "ApplicationContext",
            "visibility": "Public",
            "value_type": "CanonicalTermBytes",
        },
    ]


@dataclass(frozen=True, slots=True)
class ClassicalScheduleEvent:
    ordinal: int
    kind: str
    subject: str

    def __post_init__(self) -> None:
        if type(self.ordinal) is not int or self.ordinal < 0:
            raise malformed(
                "classical-fri:schedule-formation",
                "FRI-IOR-CLASSICAL-SCHEDULE-001",
                "a schedule ordinal must be a non-negative integer",
            )
        if not isinstance(self.kind, str) or not self.kind:
            raise malformed(
                "classical-fri:schedule-formation",
                "FRI-IOR-CLASSICAL-SCHEDULE-002",
                "a schedule event requires a kind",
            )
        if not isinstance(self.subject, str) or not self.subject:
            raise malformed(
                "classical-fri:schedule-formation",
                "FRI-IOR-CLASSICAL-SCHEDULE-003",
                "a schedule event requires a subject",
            )

    def to_term(self) -> dict[str, Any]:
        return {"ordinal": self.ordinal, "kind": self.kind, "subject": self.subject}


EXACT_NATIVE_SCHEDULE = tuple(
    ClassicalScheduleEvent(index, kind, subject)
    for index, (kind, subject) in enumerate(
        (
            ("FixInitialOracle", "G0"),
            ("FreshChallenge", "x0"),
            ("PublishProverOracle", "G1"),
            ("FreshChallenge", "x1"),
            ("PublishProverOracle", "G2"),
            ("FreshChallenge", "x2"),
            ("PublishTerminalScalar", "C"),
            ("FreshQueryVector", "s0[0..3]"),
            ("LayerQueryBlock", "q[0..11]"),
            ("CheckBlock", "fold[0..11]"),
            ("Terminal", "AcceptOrReject"),
        )
    )
)

EXACT_COMMITTED_SCHEDULE = tuple(
    ClassicalScheduleEvent(index, kind, subject)
    for index, (kind, subject) in enumerate(
        (
            ("PublishMerkleRoot", "M0"),
            ("PublicChallenge", "x0"),
            ("PublishMerkleRoot", "M1"),
            ("PublicChallenge", "x1"),
            ("PublishMerkleRoot", "M2"),
            ("PublicChallenge", "x2"),
            ("PublishTerminalScalar", "C"),
            ("PublicQueryVector", "s0[0..3]"),
            ("PublishOpeningTable", "openings"),
            ("AuthenticationAndFoldChecks", "checks"),
            ("Terminal", "AcceptOrReject"),
        )
    )
)


@dataclass(frozen=True, slots=True)
class ClassicalNativeCore:
    profile_id: SemanticId
    schedule: tuple[ClassicalScheduleEvent, ...]

    def __post_init__(self) -> None:
        if self.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity:
            raise malformed(
                "classical-fri:native-core-formation",
                "FRI-IOR-CLASSICAL-CORE-001",
                "the native Core must bind the exact classical FRI profile",
            )
        if self.schedule != EXACT_NATIVE_SCHEDULE:
            raise malformed(
                "classical-fri:native-core-formation",
                "FRI-IOR-CLASSICAL-CORE-002",
                "the native Core must retain the exact source schedule",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "profile_id": self.profile_id.to_term(),
            "public_environment_schema": PUBLIC_ENVIRONMENT_SCHEMA,
            "public_environment_coordinates": (
                _public_environment_coordinate_schema()
            ),
            "schedule": [event.to_term() for event in self.schedule],
            "oracle_layers": ["G0", "G1", "G2"],
            "terminal": "C:GoldilocksElement",
            "query_occurrences": LAYER_QUERY_OCCURRENCES,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-native-core",
            "classical-fri.native-core.v1",
            self.to_term(),
        )


EXACT_CLASSICAL_NATIVE_CORE = ClassicalNativeCore(
    EXACT_CLASSICAL_FRI_PROFILE.identity,
    EXACT_NATIVE_SCHEDULE,
)


@dataclass(frozen=True, slots=True)
class ClassicalCommittedCore:
    profile_id: SemanticId
    source_core_id: SemanticId
    schedule: tuple[ClassicalScheduleEvent, ...]
    commitment_profile: str

    def __post_init__(self) -> None:
        if self.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity:
            raise malformed(
                "classical-fri:committed-core-formation",
                "FRI-IOR-CLASSICAL-CORE-003",
                "the committed Core must bind the exact classical FRI profile",
            )
        if self.source_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity:
            raise malformed(
                "classical-fri:committed-core-formation",
                "FRI-IOR-CLASSICAL-CORE-004",
                "the committed Core must name the exact native source Core",
            )
        if self.schedule != EXACT_COMMITTED_SCHEDULE:
            raise malformed(
                "classical-fri:committed-core-formation",
                "FRI-IOR-CLASSICAL-CORE-005",
                "the committed Core must retain the exact committed schedule",
            )
        if self.commitment_profile != "salted-sha256-antipodal-pairs-single-root-v1":
            raise malformed(
                "classical-fri:committed-core-formation",
                "FRI-IOR-CLASSICAL-CORE-006",
                "the committed Core requires its exact commitment profile",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "profile_id": self.profile_id.to_term(),
            "source_core_id": self.source_core_id.to_term(),
            "public_environment_schema": PUBLIC_ENVIRONMENT_SCHEMA,
            "public_environment_coordinates": (
                _public_environment_coordinate_schema()
            ),
            "schedule": [event.to_term() for event in self.schedule],
            "commitment_profile": self.commitment_profile,
            "roots": ["M0", "M1", "M2"],
            "terminal": "C:GoldilocksElement",
            "opening_layout": "deduplicated-table-with-12-occurrence-selectors",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-committed-core",
            "classical-fri.committed-core.v1",
            self.to_term(),
        )


EXACT_CLASSICAL_COMMITTED_CORE = ClassicalCommittedCore(
    EXACT_CLASSICAL_FRI_PROFILE.identity,
    EXACT_CLASSICAL_NATIVE_CORE.identity,
    EXACT_COMMITTED_SCHEDULE,
    "salted-sha256-antipodal-pairs-single-root-v1",
)


@dataclass(frozen=True, slots=True)
class ClassicalLogicalOracle:
    """One immutable total logical oracle, prior to commitment compilation."""

    layer: int
    domain: ClassicalFriDomain
    origin: str
    values: tuple[GoldilocksElement, ...]

    def __post_init__(self) -> None:
        if type(self.layer) is not int or not 0 <= self.layer < FOLD_ROUNDS:
            raise malformed(
                "classical-fri:oracle-formation",
                "FRI-IOR-CLASSICAL-ORACLE-001",
                "a logical oracle layer must be one of 0, 1, or 2",
            )
        if not isinstance(self.domain, ClassicalFriDomain):
            raise malformed(
                "classical-fri:oracle-formation",
                "FRI-IOR-CLASSICAL-ORACLE-002",
                "a logical oracle requires a formed classical FRI domain",
            )
        if self.origin not in ("InitialOracle", "ProverOracle"):
            raise malformed(
                "classical-fri:oracle-formation",
                "FRI-IOR-CLASSICAL-ORACLE-003",
                "an oracle origin must be InitialOracle or ProverOracle",
            )
        if (
            type(self.values) is not tuple
            or len(self.values) > DOMAIN_ORDERS[0]
            or any(not isinstance(value, GoldilocksElement) for value in self.values)
        ):
            raise malformed(
                "classical-fri:oracle-formation",
                "FRI-IOR-CLASSICAL-ORACLE-004",
                "oracle values must be a bounded tuple of Goldilocks elements",
            )

    @property
    def name(self) -> str:
        return f"G{self.layer}"

    def publication_observation(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "origin": self.origin,
            "publication_mode": "LogicalAccess",
            "domain_id": self.domain.identity,
        }

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer,
            "name": self.name,
            "domain_id": self.domain.identity.to_term(),
            "origin": self.origin,
            "values": [value.to_term() for value in self.values],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-logical-oracle",
            "classical-fri.logical-oracle.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class LayerQueryOccurrence:
    """One labelled layer query containing one complete antipodal fibre."""

    ordinal: int
    repetition: int
    layer: int
    sampled_index: int
    mate_index: int
    pair_index: int
    parent_index: int

    def __post_init__(self) -> None:
        integers = (
            self.ordinal,
            self.repetition,
            self.layer,
            self.sampled_index,
            self.mate_index,
            self.pair_index,
            self.parent_index,
        )
        if any(type(value) is not int or value < 0 for value in integers):
            raise malformed(
                "classical-fri:query-occurrence-formation",
                "FRI-IOR-CLASSICAL-QUERY-001",
                "query-occurrence coordinates must be non-negative integers",
            )
        if self.ordinal >= LAYER_QUERY_OCCURRENCES:
            raise malformed(
                "classical-fri:query-occurrence-formation",
                "FRI-IOR-CLASSICAL-QUERY-002",
                "a query occurrence ordinal must be below twelve",
            )
        if self.repetition >= QUERY_REPETITIONS or self.layer >= FOLD_ROUNDS:
            raise malformed(
                "classical-fri:query-occurrence-formation",
                "FRI-IOR-CLASSICAL-QUERY-003",
                "query repetition and layer are outside the exact profile",
            )
        if (
            self.sampled_index >= DOMAIN_ORDERS[self.layer]
            or self.mate_index >= DOMAIN_ORDERS[self.layer]
            or self.pair_index >= DOMAIN_ORDERS[self.layer] // 2
            or self.parent_index >= DOMAIN_ORDERS[self.layer + 1]
        ):
            raise malformed(
                "classical-fri:query-occurrence-formation",
                "FRI-IOR-CLASSICAL-QUERY-004",
                "a query occurrence index is outside its layer domain",
            )

    @property
    def label(self) -> str:
        return f"query.{self.repetition}.layer.{self.layer}"

    def to_term(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal,
            "label": self.label,
            "repetition": self.repetition,
            "layer": self.layer,
            "sampled_index": self.sampled_index,
            "mate_index": self.mate_index,
            "pair_index": self.pair_index,
            "parent_index": self.parent_index,
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-layer-query-occurrence",
            "classical-fri.layer-query-occurrence.v1",
            self.to_term(),
        )


def derive_layer_query_occurrences(
    query_indices: tuple[int, ...],
) -> tuple[LayerQueryOccurrence, ...]:
    """Expand four initial-domain indices into twelve labelled layer queries."""

    if (
        type(query_indices) is not tuple
        or len(query_indices) != QUERY_REPETITIONS
        or any(
            type(index) is not int or not 0 <= index < DOMAIN_ORDERS[0]
            for index in query_indices
        )
    ):
        raise malformed(
            "classical-fri:query-vector-formation",
            "FRI-IOR-CLASSICAL-QUERY-005",
            "the exact query vector contains four order-64 indices",
        )
    occurrences: list[LayerQueryOccurrence] = []
    for repetition, initial_index in enumerate(query_indices):
        current_index = initial_index
        for layer in range(FOLD_ROUNDS):
            order = DOMAIN_ORDERS[layer]
            half = order // 2
            pair_index = current_index % half
            occurrences.append(
                LayerQueryOccurrence(
                    ordinal=repetition * FOLD_ROUNDS + layer,
                    repetition=repetition,
                    layer=layer,
                    sampled_index=current_index,
                    mate_index=(current_index + half) % order,
                    pair_index=pair_index,
                    parent_index=pair_index,
                )
            )
            current_index = pair_index
    return tuple(occurrences)


@dataclass(frozen=True, slots=True)
class ClassicalNativeTrace:
    """A complete native three-fold execution trace."""

    profile: ClassicalFriProfile
    native_core_id: SemanticId
    public_environment: ClassicalPublicEnvironment
    oracles: tuple[ClassicalLogicalOracle, ...]
    fold_challenges: tuple[GoldilocksElement, ...]
    terminal_scalar: GoldilocksElement
    query_indices: tuple[int, ...]
    query_occurrences: tuple[LayerQueryOccurrence, ...]
    schedule: tuple[ClassicalScheduleEvent, ...] = field(default=EXACT_NATIVE_SCHEDULE)

    def __post_init__(self) -> None:
        if not isinstance(self.profile, ClassicalFriProfile):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-001",
                "a native trace requires a formed classical FRI profile",
            )
        if not isinstance(self.native_core_id, SemanticId):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-002",
                "a native trace requires a typed native Core identity",
            )
        if not isinstance(self.public_environment, ClassicalPublicEnvironment):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-008",
                "a native trace requires formed Statement and application-context coordinates",
            )
        if type(self.oracles) is not tuple or len(self.oracles) != FOLD_ROUNDS:
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-003",
                "a native trace contains exactly G0, G1, and G2",
            )
        if not isinstance(self.terminal_scalar, GoldilocksElement):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-004",
                "the exact terminal material is one Goldilocks scalar",
            )
        if (
            type(self.fold_challenges) is not tuple
            or len(self.fold_challenges) != FOLD_ROUNDS
            or any(
                not isinstance(challenge, GoldilocksElement)
                for challenge in self.fold_challenges
            )
        ):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-005",
                "a native trace requires three base-field fold challenges",
            )
        if (
            type(self.query_occurrences) is not tuple
            or len(self.query_occurrences) != LAYER_QUERY_OCCURRENCES
        ):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-006",
                "a native trace requires twelve layer-query occurrences",
            )
        if type(self.schedule) is not tuple or any(
            not isinstance(event, ClassicalScheduleEvent) for event in self.schedule
        ):
            raise malformed(
                "classical-fri:trace-formation",
                "FRI-IOR-CLASSICAL-FORMATION-007",
                "a native trace schedule requires formed events",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "profile_id": self.profile.identity.to_term(),
            "native_core_id": self.native_core_id.to_term(),
            "public_environment_id": self.public_environment.identity.to_term(),
            "oracles": [oracle.to_term() for oracle in self.oracles],
            "fold_challenges": [value.to_term() for value in self.fold_challenges],
            "terminal_scalar": self.terminal_scalar.to_term(),
            "query_indices": list(self.query_indices),
            "query_occurrences": [
                occurrence.to_term() for occurrence in self.query_occurrences
            ],
            "schedule": [event.to_term() for event in self.schedule],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-native-trace",
            "classical-fri.native-trace.v1",
            self.to_term(),
        )


DEFAULT_SOURCE_COEFFICIENTS = tuple(
    GoldilocksElement(value) for value in (3, 5, 7, 11, 13, 17, 19, 23)
)
DEFAULT_FRESH_CHALLENGES = tuple(GoldilocksElement(value) for value in (29, 31, 37))
DEFAULT_QUERY_INDICES = (5, 17, 17, 42)


def evaluate_polynomial(
    coefficients: tuple[GoldilocksElement, ...],
    point: GoldilocksElement,
) -> GoldilocksElement:
    if type(coefficients) is not tuple or any(
        not isinstance(value, GoldilocksElement) for value in coefficients
    ):
        raise malformed(
            "classical-fri:polynomial-evaluation",
            "FRI-IOR-CLASSICAL-FIELD-005",
            "polynomial coefficients must be a tuple of field elements",
        )
    if not isinstance(point, GoldilocksElement):
        raise malformed(
            "classical-fri:polynomial-evaluation",
            "FRI-IOR-CLASSICAL-FIELD-006",
            "a polynomial evaluation point must be a field element",
        )
    result = ZERO
    for coefficient in reversed(coefficients):
        result = result * point + coefficient
    return result


def binary_fold(
    point: GoldilocksElement,
    positive: GoldilocksElement,
    negative: GoldilocksElement,
    challenge: GoldilocksElement,
    resources: ResourceCounter | None = None,
) -> GoldilocksElement:
    """Evaluate the binary fibre interpolant at the fold challenge."""

    if any(
        not isinstance(value, GoldilocksElement)
        for value in (point, positive, negative, challenge)
    ):
        raise malformed(
            "classical-fri:binary-fold",
            "FRI-IOR-CLASSICAL-FIELD-007",
            "binary folding requires four Goldilocks elements",
        )
    if point == ZERO:
        raise refusal(
            "classical-fri:binary-fold",
            "FRI-IOR-CLASSICAL-FIELD-008",
            "a multiplicative-domain fibre cannot be rooted at zero",
        )
    if resources is not None:
        resources.consume_field_operations(8)
    even = (positive + negative) * TWO_INVERSE
    odd = (positive - negative) * TWO_INVERSE / point
    return even + challenge * odd


def _fold_coefficients(
    coefficients: tuple[GoldilocksElement, ...],
    challenge: GoldilocksElement,
) -> tuple[GoldilocksElement, ...]:
    if (
        type(coefficients) is not tuple
        or not coefficients
        or len(coefficients) % 2
        or any(not isinstance(value, GoldilocksElement) for value in coefficients)
        or not isinstance(challenge, GoldilocksElement)
    ):
        raise malformed(
            "classical-fri:honest-fold",
            "FRI-IOR-CLASSICAL-FIELD-009",
            "honest coefficient folding requires an even non-empty coefficient tuple",
        )
    return tuple(
        coefficients[index] + challenge * coefficients[index + 1]
        for index in range(0, len(coefficients), 2)
    )


def derive_honest_native_trace(
    source_coefficients: tuple[GoldilocksElement, ...] = DEFAULT_SOURCE_COEFFICIENTS,
    fold_challenges: tuple[GoldilocksElement, ...] = DEFAULT_FRESH_CHALLENGES,
    query_indices: tuple[int, ...] = DEFAULT_QUERY_INDICES,
    *,
    statement: Any = DEFAULT_STATEMENT,
    application_context: Any = DEFAULT_APPLICATION_CONTEXT,
    terminal_scalar_override: GoldilocksElement | None = None,
) -> ClassicalNativeTrace:
    """Deterministically generate one honest or terminal-mutated native trace."""

    if (
        type(source_coefficients) is not tuple
        or len(source_coefficients) != DEGREE_BOUNDS[0]
        or any(
            not isinstance(coefficient, GoldilocksElement)
            for coefficient in source_coefficients
        )
    ):
        raise malformed(
            "classical-fri:honest-generation",
            "FRI-IOR-CLASSICAL-GENERATION-001",
            "the deterministic source polynomial has exactly eight coefficients",
        )
    if (
        type(fold_challenges) is not tuple
        or len(fold_challenges) != FOLD_ROUNDS
        or any(
            not isinstance(challenge, GoldilocksElement)
            for challenge in fold_challenges
        )
    ):
        raise malformed(
            "classical-fri:honest-generation",
            "FRI-IOR-CLASSICAL-GENERATION-002",
            "honest generation requires three base-field challenges",
        )
    occurrences = derive_layer_query_occurrences(query_indices)
    coefficient_layers = [source_coefficients]
    for challenge in fold_challenges:
        coefficient_layers.append(_fold_coefficients(coefficient_layers[-1], challenge))
    if len(coefficient_layers[-1]) != 1:
        raise RuntimeError("the exact three-fold generator failed to reach one scalar")
    oracle_layers = tuple(
        ClassicalLogicalOracle(
            layer=layer,
            domain=CLASSICAL_DOMAINS[layer],
            origin="InitialOracle" if layer == 0 else "ProverOracle",
            values=tuple(
                evaluate_polynomial(coefficient_layers[layer], point)
                for point in CLASSICAL_DOMAINS[layer].points()
            ),
        )
        for layer in range(FOLD_ROUNDS)
    )
    terminal = coefficient_layers[-1][0]
    if terminal_scalar_override is not None:
        if not isinstance(terminal_scalar_override, GoldilocksElement):
            raise malformed(
                "classical-fri:honest-generation",
                "FRI-IOR-CLASSICAL-GENERATION-003",
                "a terminal override must remain one Goldilocks scalar",
            )
        terminal = terminal_scalar_override
    return ClassicalNativeTrace(
        profile=EXACT_CLASSICAL_FRI_PROFILE,
        native_core_id=EXACT_CLASSICAL_NATIVE_CORE.identity,
        public_environment=form_classical_public_environment(
            statement,
            application_context,
        ),
        oracles=oracle_layers,
        fold_challenges=fold_challenges,
        terminal_scalar=terminal,
        query_indices=query_indices,
        query_occurrences=occurrences,
    )


def _formed_counter(limits: ResourceLimits) -> ResourceCounter:
    if type(limits) is not ResourceLimits:
        raise malformed(
            "classical-fri:resource-formation",
            "FRI-IOR-CLASSICAL-RESOURCE-001",
            "classical FRI verification requires exact ResourceLimits",
        )
    return ResourceCounter(limits)


def verify_native_trace(
    trace: object,
    limits: ResourceLimits = DEFAULT_CLASSICAL_LIMITS,
) -> CheckResult:
    """Verify native formation, exact schedule, and all twelve fold checks."""

    boundary = "classical-fri:native-verification"
    try:
        resources = _formed_counter(limits)
        if not isinstance(trace, ClassicalNativeTrace):
            raise malformed(
                boundary,
                "FRI-IOR-CLASSICAL-NATIVE-001",
                "native verification requires a ClassicalNativeTrace",
            )
        if trace.profile != EXACT_CLASSICAL_FRI_PROFILE:
            raise refusal(
                "classical-fri:native-profile",
                "FRI-IOR-CLASSICAL-NATIVE-002",
                "the trace substituted the exact classical FRI profile",
            )
        if trace.native_core_id != EXACT_CLASSICAL_NATIVE_CORE.identity:
            raise refusal(
                "classical-fri:native-core",
                "FRI-IOR-CLASSICAL-NATIVE-003",
                "the trace substituted its native Core identity",
            )
        if trace.public_environment.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity:
            raise refusal(
                "classical-fri:native-public-environment",
                "FRI-IOR-CLASSICAL-NATIVE-009",
                "the native public environment substituted the exact profile coordinate",
            )
        if trace.schedule != EXACT_NATIVE_SCHEDULE:
            raise refusal(
                "classical-fri:native-schedule",
                "FRI-IOR-CLASSICAL-NATIVE-004",
                "the trace changed the exact fixation/challenge/publication order",
            )
        for layer, oracle in enumerate(trace.oracles):
            if not isinstance(oracle, ClassicalLogicalOracle):
                raise malformed(
                    "classical-fri:native-oracle",
                    "FRI-IOR-CLASSICAL-NATIVE-005",
                    "every native oracle must use the exact carrier",
                )
            expected_origin = "InitialOracle" if layer == 0 else "ProverOracle"
            if (
                oracle.layer != layer
                or oracle.domain != CLASSICAL_DOMAINS[layer]
                or oracle.origin != expected_origin
            ):
                raise refusal(
                    "classical-fri:native-oracle",
                    "FRI-IOR-CLASSICAL-NATIVE-006",
                    "an oracle changed its layer, domain, or causal origin",
                )
            if len(oracle.values) != oracle.domain.order:
                raise refusal(
                    "classical-fri:native-oracle-totality",
                    "FRI-IOR-CLASSICAL-NATIVE-007",
                    "a logical oracle must answer every and only its exact domain",
                )
        expected_occurrences = derive_layer_query_occurrences(trace.query_indices)
        if trace.query_occurrences != expected_occurrences:
            raise refusal(
                "classical-fri:native-query-plan",
                "FRI-IOR-CLASSICAL-NATIVE-008",
                "the twelve labelled layer-query occurrences were changed",
            )
        resources.consume_logical_query_occurrences(LAYER_QUERY_OCCURRENCES)
        points = tuple(domain.points() for domain in CLASSICAL_DOMAINS)
        for occurrence in trace.query_occurrences:
            oracle = trace.oracles[occurrence.layer]
            positive = oracle.values[occurrence.pair_index]
            negative = oracle.values[occurrence.pair_index + oracle.domain.order // 2]
            folded = binary_fold(
                points[occurrence.layer][occurrence.pair_index],
                positive,
                negative,
                trace.fold_challenges[occurrence.layer],
                resources,
            )
            if occurrence.layer < FOLD_ROUNDS - 1:
                target = trace.oracles[occurrence.layer + 1].values[
                    occurrence.parent_index
                ]
            else:
                target = trace.terminal_scalar
            if folded != target:
                if occurrence.layer == 0:
                    fold_code = "FRI-IOR-CLASSICAL-NATIVE-020"
                elif occurrence.layer == 1:
                    fold_code = "FRI-IOR-CLASSICAL-NATIVE-021"
                else:
                    fold_code = "FRI-IOR-CLASSICAL-NATIVE-022"
                raise refusal(
                    f"classical-fri:fold-{occurrence.layer}",
                    fold_code,
                    "a labelled binary-fold equation does not match its next-layer value",
                )
        return affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-NATIVE-100",
            "the exact three-fold scalar-terminal native trace accepts",
            subject=trace.identity,
            native_core_id=trace.native_core_id,
            public_environment_id=trace.public_environment.identity,
            statement_coordinate_id=(
                trace.public_environment.statement_coordinate_id
            ),
            application_context_coordinate_id=(
                trace.public_environment.application_context_coordinate_id
            ),
            query_repetitions=QUERY_REPETITIONS,
            layer_query_occurrences=LAYER_QUERY_OCCURRENCES,
            oracle_value_occurrences=2 * LAYER_QUERY_OCCURRENCES,
            terminal="Accept",
            resources=resources.snapshot(),
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - deliberate fail-closed seam
        return checker_failure(boundary, f"unexpected native verifier fault: {error}")


@dataclass(frozen=True, slots=True)
class ClassicalCommitmentProfile:
    """Exact salted pair-leaf, binary-tree, single-root commitment profile."""

    name: str
    hash_name: str
    field_codec: str
    pair_index_codec: str
    salt_bytes: int
    digest_bytes: int
    leaf_domain: bytes
    node_domain: bytes

    def __post_init__(self) -> None:
        if self.name != "salted-sha256-antipodal-pairs-single-root-v1":
            raise malformed(
                "classical-fri:commitment-profile-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-001",
                "the exact commitment profile name is fixed",
            )
        if self.hash_name != "sha256":
            raise malformed(
                "classical-fri:commitment-profile-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-002",
                "the exact commitment profile uses SHA-256",
            )
        if (
            self.field_codec != FIELD_CODEC
            or self.pair_index_codec != PAIR_INDEX_CODEC
            or self.salt_bytes != SALT_BYTES
            or self.digest_bytes != DIGEST_BYTES
            or self.leaf_domain != LEAF_HASH_DOMAIN
            or self.node_domain != NODE_HASH_DOMAIN
        ):
            raise malformed(
                "classical-fri:commitment-profile-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-003",
                "the exact commitment codec or hash framing was changed",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "hash": self.hash_name,
            "field_codec": self.field_codec,
            "pair_index_codec": self.pair_index_codec,
            "salt_codec": SALT_CODEC,
            "digest_codec": DIGEST_CODEC,
            "salt_bytes": self.salt_bytes,
            "digest_bytes": self.digest_bytes,
            "leaf_domain": self.leaf_domain.hex(),
            "node_domain": self.node_domain.hex(),
            "leaf_payload": [
                "domain-separator",
                "layer-u8",
                "pair-index-u16be",
                "positive-u64be",
                "negative-u64be",
                "salt-16-bytes",
            ],
            "node_payload": ["domain-separator", "left-digest", "right-digest"],
            "root": "one-final-digest",
            "path": "leaf-to-root-siblings-with-orientation-derived-from-pair-index",
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-commitment-profile",
            "classical-fri.commitment-profile.v1",
            self.to_term(),
        )


EXACT_CLASSICAL_COMMITMENT_PROFILE = ClassicalCommitmentProfile(
    name="salted-sha256-antipodal-pairs-single-root-v1",
    hash_name="sha256",
    field_codec=FIELD_CODEC,
    pair_index_codec=PAIR_INDEX_CODEC,
    salt_bytes=SALT_BYTES,
    digest_bytes=DIGEST_BYTES,
    leaf_domain=LEAF_HASH_DOMAIN,
    node_domain=NODE_HASH_DOMAIN,
)


def _validate_digest(value: object, boundary: str) -> bytes:
    if not isinstance(value, bytes) or len(value) != DIGEST_BYTES:
        raise malformed(
            boundary,
            "FRI-IOR-CLASSICAL-COMMITMENT-004",
            "a SHA-256 digest must contain exactly 32 bytes",
        )
    return value


@dataclass(frozen=True, slots=True)
class ClassicalMerkleRoot:
    layer: int
    digest: bytes
    commitment_profile_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_COMMITMENT_PROFILE.identity
    )

    def __post_init__(self) -> None:
        if type(self.layer) is not int or not 0 <= self.layer < FOLD_ROUNDS:
            raise malformed(
                "classical-fri:root-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-005",
                "a commitment root layer must be 0, 1, or 2",
            )
        _validate_digest(self.digest, "classical-fri:root-formation")
        if not isinstance(self.commitment_profile_id, SemanticId):
            raise malformed(
                "classical-fri:root-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-006",
                "a commitment root requires a typed profile identity",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer,
            "digest": self.digest.hex(),
            "commitment_profile_id": self.commitment_profile_id.to_term(),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-merkle-root",
            "classical-fri.merkle-root.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ClassicalPairOpening:
    layer: int
    pair_index: int
    positive: GoldilocksElement
    negative: GoldilocksElement
    salt: bytes
    authentication_path: tuple[bytes, ...]
    commitment_profile_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_COMMITMENT_PROFILE.identity
    )

    def __post_init__(self) -> None:
        if type(self.layer) is not int or not 0 <= self.layer < FOLD_ROUNDS:
            raise malformed(
                "classical-fri:opening-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-007",
                "an opening layer must be 0, 1, or 2",
            )
        if (
            type(self.pair_index) is not int
            or not 0 <= self.pair_index < DOMAIN_ORDERS[self.layer] // 2
        ):
            raise malformed(
                "classical-fri:opening-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-008",
                "an opening pair index is outside its exact layer",
            )
        if not isinstance(self.positive, GoldilocksElement) or not isinstance(
            self.negative, GoldilocksElement
        ):
            raise malformed(
                "classical-fri:opening-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-009",
                "an opening contains two canonical field elements",
            )
        if not isinstance(self.salt, bytes) or len(self.salt) != SALT_BYTES:
            raise malformed(
                "classical-fri:opening-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-010",
                "an opening salt contains exactly sixteen bytes",
            )
        if (
            type(self.authentication_path) is not tuple
            or len(self.authentication_path) > 6
            or any(
                not isinstance(digest, bytes) or len(digest) != DIGEST_BYTES
                for digest in self.authentication_path
            )
        ):
            raise malformed(
                "classical-fri:opening-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-011",
                "an opening path is a bounded tuple of SHA-256 digests",
            )
        if not isinstance(self.commitment_profile_id, SemanticId):
            raise malformed(
                "classical-fri:opening-formation",
                "FRI-IOR-CLASSICAL-COMMITMENT-012",
                "an opening requires a typed commitment profile identity",
            )

    @property
    def key(self) -> tuple[int, int]:
        return (self.layer, self.pair_index)

    def to_term(self) -> dict[str, Any]:
        return {
            "layer": self.layer,
            "pair_index": self.pair_index,
            "positive": self.positive.to_term(),
            "negative": self.negative.to_term(),
            "salt": self.salt.hex(),
            "authentication_path": [
                digest.hex() for digest in self.authentication_path
            ],
            "commitment_profile_id": self.commitment_profile_id.to_term(),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-pair-opening",
            "classical-fri.pair-opening.v1",
            self.to_term(),
        )


@dataclass(frozen=True, slots=True)
class ClassicalCommitmentTree:
    domain: ClassicalFriDomain
    values: tuple[GoldilocksElement, ...]
    salts: tuple[bytes, ...]
    levels: tuple[tuple[bytes, ...], ...]
    root: ClassicalMerkleRoot

    def open_pair(self, pair_index: int) -> ClassicalPairOpening:
        if type(pair_index) is not int or not 0 <= pair_index < len(self.salts):
            raise malformed(
                "classical-fri:opening-generation",
                "FRI-IOR-CLASSICAL-COMMITMENT-013",
                "an opening index is outside the tree",
            )
        running = pair_index
        path: list[bytes] = []
        for level in self.levels[:-1]:
            path.append(level[running ^ 1])
            running //= 2
        half = self.domain.order // 2
        return ClassicalPairOpening(
            layer=self.domain.layer,
            pair_index=pair_index,
            positive=self.values[pair_index],
            negative=self.values[pair_index + half],
            salt=self.salts[pair_index],
            authentication_path=tuple(path),
        )


def _hash(payload: bytes, resources: ResourceCounter | None, *, node: bool) -> bytes:
    if resources is not None:
        resources.consume_hash(len(payload), merkle_nodes=1 if node else 0)
    return hashlib.sha256(payload).digest()


def _leaf_payload(
    layer: int,
    pair_index: int,
    positive: GoldilocksElement,
    negative: GoldilocksElement,
    salt: bytes,
) -> bytes:
    return (
        LEAF_HASH_DOMAIN
        + bytes((layer,))
        + pair_index.to_bytes(2, "big")
        + positive.to_bytes()
        + negative.to_bytes()
        + salt
    )


def build_classical_commitment(
    oracle: ClassicalLogicalOracle,
    salts: tuple[bytes, ...],
    resources: ResourceCounter | None = None,
) -> ClassicalCommitmentTree:
    if not isinstance(oracle, ClassicalLogicalOracle):
        raise malformed(
            "classical-fri:commitment-generation",
            "FRI-IOR-CLASSICAL-COMMITMENT-014",
            "commitment generation requires a logical oracle",
        )
    half = oracle.domain.order // 2
    if (
        len(oracle.values) != oracle.domain.order
        or type(salts) is not tuple
        or len(salts) != half
        or any(not isinstance(salt, bytes) or len(salt) != SALT_BYTES for salt in salts)
    ):
        raise malformed(
            "classical-fri:commitment-generation",
            "FRI-IOR-CLASSICAL-COMMITMENT-015",
            "commitment generation requires one exact salt per antipodal pair",
        )
    leaves = tuple(
        _hash(
            _leaf_payload(
                oracle.layer,
                pair_index,
                oracle.values[pair_index],
                oracle.values[pair_index + half],
                salts[pair_index],
            ),
            resources,
            node=True,
        )
        for pair_index in range(half)
    )
    levels = [leaves]
    while len(levels[-1]) > 1:
        current = levels[-1]
        levels.append(
            tuple(
                _hash(
                    NODE_HASH_DOMAIN + current[index] + current[index + 1],
                    resources,
                    node=True,
                )
                for index in range(0, len(current), 2)
            )
        )
    root = ClassicalMerkleRoot(oracle.layer, levels[-1][0])
    return ClassicalCommitmentTree(
        oracle.domain,
        oracle.values,
        salts,
        tuple(levels),
        root,
    )


def _verify_opening(
    domain: ClassicalFriDomain,
    root: ClassicalMerkleRoot,
    opening: ClassicalPairOpening,
    resources: ResourceCounter,
) -> None:
    if root.commitment_profile_id != EXACT_CLASSICAL_COMMITMENT_PROFILE.identity:
        raise refusal(
            "classical-fri:opening-profile",
            "FRI-IOR-CLASSICAL-COMMITMENT-016",
            "a root substituted the exact commitment profile",
        )
    if opening.commitment_profile_id != EXACT_CLASSICAL_COMMITMENT_PROFILE.identity:
        raise refusal(
            "classical-fri:opening-profile",
            "FRI-IOR-CLASSICAL-COMMITMENT-017",
            "an opening substituted the exact commitment profile",
        )
    if root.layer != domain.layer or opening.layer != domain.layer:
        raise refusal(
            "classical-fri:opening-layer",
            "FRI-IOR-CLASSICAL-COMMITMENT-018",
            "an opening or root is attached to the wrong oracle layer",
        )
    expected_depth = (domain.order // 2).bit_length() - 1
    if len(opening.authentication_path) != expected_depth:
        raise refusal(
            "classical-fri:opening-path",
            "FRI-IOR-CLASSICAL-COMMITMENT-019",
            "an opening path has the wrong exact depth",
        )
    digest = _hash(
        _leaf_payload(
            opening.layer,
            opening.pair_index,
            opening.positive,
            opening.negative,
            opening.salt,
        ),
        resources,
        node=True,
    )
    running = opening.pair_index
    for sibling in opening.authentication_path:
        if running & 1:
            payload = NODE_HASH_DOMAIN + sibling + digest
        else:
            payload = NODE_HASH_DOMAIN + digest + sibling
        digest = _hash(payload, resources, node=True)
        running //= 2
    if digest != root.digest:
        raise refusal(
            "classical-fri:opening-authentication",
            "FRI-IOR-CLASSICAL-COMMITMENT-020",
            "a pair opening does not authenticate to its declared root",
        )


@dataclass(frozen=True, slots=True)
class ClassicalCommittedPublicInputs:
    """Committed-protocol view of the shared public environment."""

    statement: bytes
    application_context: bytes
    profile_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_FRI_PROFILE.identity
    )
    committed_core_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_COMMITTED_CORE.identity
    )
    schema: str = PUBLIC_INPUT_SCHEMA

    def __post_init__(self) -> None:
        if (
            not isinstance(self.statement, bytes)
            or not self.statement
            or not isinstance(self.application_context, bytes)
            or not self.application_context
        ):
            raise malformed(
                "classical-fri:public-input-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-001",
                "statement and application context must be non-empty canonical term bytes",
            )
        if len(self.statement) > 1 << 14 or len(self.application_context) > 1 << 14:
            raise malformed(
                "classical-fri:public-input-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-002",
                "public input term bytes exceed the exact profile bound",
            )
        if not isinstance(self.profile_id, SemanticId) or not isinstance(
            self.committed_core_id, SemanticId
        ):
            raise malformed(
                "classical-fri:public-input-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-003",
                "public inputs require typed profile and committed Core identities",
            )
        if self.schema != PUBLIC_INPUT_SCHEMA:
            raise malformed(
                "classical-fri:public-input-formation",
                "FRI-IOR-CLASSICAL-PUBLIC-004",
                "the public-input schema is fixed",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "profile_id": self.profile_id.to_term(),
            "committed_core_id": self.committed_core_id.to_term(),
            "statement": self.statement.hex(),
            "application_context": self.application_context.hex(),
        }

    @property
    def public_environment(self) -> ClassicalPublicEnvironment:
        """Recover the native/Fresh/FS environment without a second author."""

        return ClassicalPublicEnvironment(
            statement=self.statement,
            application_context=self.application_context,
            profile_id=self.profile_id,
        )

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-public-inputs",
            "classical-fri.public-inputs.v1",
            self.to_term(),
        )


def form_classical_public_inputs(
    statement: Any,
    application_context: Any,
) -> ClassicalCommittedPublicInputs:
    return ClassicalCommittedPublicInputs(
        statement=encode_term(statement),
        application_context=encode_term(application_context),
    )


@dataclass(frozen=True, slots=True)
class ClassicalOccurrenceSelector:
    occurrence_ordinal: int
    opening_index: int

    def __post_init__(self) -> None:
        if (
            type(self.occurrence_ordinal) is not int
            or not 0 <= self.occurrence_ordinal < LAYER_QUERY_OCCURRENCES
            or type(self.opening_index) is not int
            or self.opening_index < 0
        ):
            raise malformed(
                "classical-fri:selector-formation",
                "FRI-IOR-CLASSICAL-PROOF-001",
                "a selector requires a valid occurrence ordinal and opening index",
            )

    def to_term(self) -> dict[str, int]:
        return {
            "occurrence_ordinal": self.occurrence_ordinal,
            "opening_index": self.opening_index,
        }


@dataclass(frozen=True, slots=True)
class ClassicalCommittedProof:
    """Public-only proof carrier; it contains no full oracle or salt table."""

    roots: tuple[ClassicalMerkleRoot, ...]
    terminal_scalar: GoldilocksElement
    opening_table: tuple[ClassicalPairOpening, ...]
    occurrence_selectors: tuple[ClassicalOccurrenceSelector, ...]
    committed_core_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_COMMITTED_CORE.identity
    )
    schema: str = PUBLIC_PROOF_SCHEMA

    def __post_init__(self) -> None:
        if (
            type(self.roots) is not tuple
            or len(self.roots) != FOLD_ROUNDS
            or any(not isinstance(root, ClassicalMerkleRoot) for root in self.roots)
        ):
            raise malformed(
                "classical-fri:proof-formation",
                "FRI-IOR-CLASSICAL-PROOF-002",
                "a classical FRI proof contains exactly three formed roots",
            )
        if not isinstance(self.terminal_scalar, GoldilocksElement):
            raise malformed(
                "classical-fri:proof-formation",
                "FRI-IOR-CLASSICAL-PROOF-003",
                "the exact proof terminal is one Goldilocks scalar",
            )
        if (
            type(self.opening_table) is not tuple
            or len(self.opening_table) > LAYER_QUERY_OCCURRENCES
            or any(
                not isinstance(opening, ClassicalPairOpening)
                for opening in self.opening_table
            )
        ):
            raise malformed(
                "classical-fri:proof-formation",
                "FRI-IOR-CLASSICAL-PROOF-004",
                "the proof opening table must be a bounded tuple of pair openings",
            )
        if (
            type(self.occurrence_selectors) is not tuple
            or len(self.occurrence_selectors) != LAYER_QUERY_OCCURRENCES
            or any(
                not isinstance(selector, ClassicalOccurrenceSelector)
                for selector in self.occurrence_selectors
            )
        ):
            raise malformed(
                "classical-fri:proof-formation",
                "FRI-IOR-CLASSICAL-PROOF-005",
                "the proof requires exactly twelve formed occurrence selectors",
            )
        if not isinstance(self.committed_core_id, SemanticId):
            raise malformed(
                "classical-fri:proof-formation",
                "FRI-IOR-CLASSICAL-PROOF-006",
                "a proof requires a typed committed Core identity",
            )
        if self.schema != PUBLIC_PROOF_SCHEMA:
            raise malformed(
                "classical-fri:proof-formation",
                "FRI-IOR-CLASSICAL-PROOF-007",
                "the public-proof schema is fixed",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "committed_core_id": self.committed_core_id.to_term(),
            "roots": [root.to_term() for root in self.roots],
            "terminal_scalar": self.terminal_scalar.to_term(),
            "opening_table": [opening.to_term() for opening in self.opening_table],
            "occurrence_selectors": [
                selector.to_term() for selector in self.occurrence_selectors
            ],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-public-proof",
            "classical-fri.public-proof.v1",
            self.to_term(),
        )


def encode_classical_public_inputs(
    public_inputs: ClassicalCommittedPublicInputs,
) -> bytes:
    """Return the exact canonical bytes of the JSON-safe public-input term."""

    if not isinstance(public_inputs, ClassicalCommittedPublicInputs):
        raise malformed(
            "classical-fri:public-input-encoding",
            "FRI-IOR-CLASSICAL-PUBLIC-009",
            "public-input encoding requires the exact formed carrier",
        )
    return encode_term(public_inputs.to_term())


def encode_classical_proof(proof: ClassicalCommittedProof) -> bytes:
    """Return the exact canonical bytes of the JSON-safe public-proof term."""

    if not isinstance(proof, ClassicalCommittedProof):
        raise malformed(
            "classical-fri:proof-encoding",
            "FRI-IOR-CLASSICAL-PROOF-008",
            "proof encoding requires the exact formed carrier",
        )
    return encode_term(proof.to_term())


@dataclass(frozen=True, slots=True)
class ClassicalFiatShamirValues:
    """The seven deterministic values sampled from one strong FS transcript."""

    fold_challenges: tuple[GoldilocksElement, ...]
    query_indices: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.fold_challenges) is not tuple
            or len(self.fold_challenges) != FOLD_ROUNDS
            or any(
                not isinstance(value, GoldilocksElement)
                for value in self.fold_challenges
            )
        ):
            raise malformed(
                "classical-fri:fs-values-formation",
                "FRI-IOR-CLASSICAL-FS-001",
                "Fiat--Shamir values require exactly three Goldilocks challenges",
            )
        derive_layer_query_occurrences(self.query_indices)

    def to_term(self) -> dict[str, Any]:
        return {
            "fold_challenges": [
                challenge.to_term() for challenge in self.fold_challenges
            ],
            "query_indices": list(self.query_indices),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-fiat-shamir-values",
            "classical-fri.fiat-shamir-values.v1",
            self.to_term(),
        )


def classical_fiat_shamir_prefix_term(
    public_inputs: ClassicalCommittedPublicInputs,
    roots: tuple[ClassicalMerkleRoot, ...],
    fold_challenges: tuple[GoldilocksElement, ...],
    terminal_scalar: GoldilocksElement | None,
    *,
    purpose: str,
    label: str,
    attempt: int,
) -> dict[str, Any]:
    """Build the exact JSON-safe prefix term hashed by the FS samplers.

    Fold challenge ``xi`` sees roots through ``Mi`` and earlier challenges.
    Every query index sees all roots, all challenges, and the terminal scalar.
    The complete public-input term is embedded rather than merely named, so
    statement and application-context bytes are strongly bound.
    """

    if not isinstance(public_inputs, ClassicalCommittedPublicInputs):
        raise malformed(
            "classical-fri:fs-prefix-formation",
            "FRI-IOR-CLASSICAL-FS-002",
            "an FS prefix requires formed public inputs",
        )
    if type(roots) is not tuple or any(
        not isinstance(root, ClassicalMerkleRoot) for root in roots
    ):
        raise malformed(
            "classical-fri:fs-prefix-formation",
            "FRI-IOR-CLASSICAL-FS-003",
            "an FS prefix root sequence requires formed Merkle roots",
        )
    if type(fold_challenges) is not tuple or any(
        not isinstance(challenge, GoldilocksElement) for challenge in fold_challenges
    ):
        raise malformed(
            "classical-fri:fs-prefix-formation",
            "FRI-IOR-CLASSICAL-FS-004",
            "an FS prefix challenge sequence requires Goldilocks elements",
        )
    if type(attempt) is not int or not 0 <= attempt < MAX_FS_SAMPLER_ATTEMPTS:
        raise malformed(
            "classical-fri:fs-prefix-formation",
            "FRI-IOR-CLASSICAL-FS-005",
            "an FS sampler attempt is outside the exact finite bound",
        )
    if purpose == "fold-challenge":
        try:
            index = FS_FOLD_LABELS.index(label)
        except ValueError as error:
            raise malformed(
                "classical-fri:fs-prefix-formation",
                "FRI-IOR-CLASSICAL-FS-006",
                "a fold prefix requires one exact fold label",
            ) from error
        if (
            len(roots) != index + 1
            or len(fold_challenges) != index
            or terminal_scalar is not None
        ):
            raise malformed(
                "classical-fri:fs-prefix-formation",
                "FRI-IOR-CLASSICAL-FS-007",
                "a fold prefix exposes exactly the causally preceding transcript",
            )
    elif purpose == "query-index":
        if (
            label not in FS_QUERY_LABELS
            or len(roots) != FOLD_ROUNDS
            or len(fold_challenges) != FOLD_ROUNDS
            or not isinstance(terminal_scalar, GoldilocksElement)
        ):
            raise malformed(
                "classical-fri:fs-prefix-formation",
                "FRI-IOR-CLASSICAL-FS-008",
                "a query prefix exposes the complete committed proof prefix",
            )
    else:
        raise malformed(
            "classical-fri:fs-prefix-formation",
            "FRI-IOR-CLASSICAL-FS-009",
            "an FS prefix purpose is either fold-challenge or query-index",
        )
    return {
        "schema": FS_PREFIX_SCHEMA,
        "public_inputs": public_inputs.to_term(),
        "committed_core_id": public_inputs.committed_core_id.to_term(),
        "purpose": purpose,
        "label": label,
        "roots": [root.to_term() for root in roots],
        "fold_challenges": [challenge.to_term() for challenge in fold_challenges],
        "terminal_scalar": (
            None if terminal_scalar is None else terminal_scalar.to_term()
        ),
        "attempt": attempt,
    }


def _sample_fs_fold_challenge(
    public_inputs: ClassicalCommittedPublicInputs,
    roots: tuple[ClassicalMerkleRoot, ...],
    fold_challenges: tuple[GoldilocksElement, ...],
    *,
    label: str,
    resources: ResourceCounter | None,
) -> GoldilocksElement:
    for attempt in range(MAX_FS_SAMPLER_ATTEMPTS):
        prefix = classical_fiat_shamir_prefix_term(
            public_inputs,
            roots,
            fold_challenges,
            None,
            purpose="fold-challenge",
            label=label,
            attempt=attempt,
        )
        payload = FS_FOLD_DOMAIN + encode_term(prefix)
        if resources is not None:
            resources.consume_transcript_frames(1)
            resources.consume_sampler_attempts(1)
            resources.consume_hash(len(payload))
        candidate = int.from_bytes(hashlib.sha256(payload).digest()[:8], "big")
        if candidate < GOLDILOCKS_MODULUS:
            return GoldilocksElement(candidate)
    raise deterministic_limit_failure(
        "classical-fri:fs-fold-sampling",
        "FRI-IOR-CLASSICAL-FS-011",
        "the bounded canonical field sampler exhausted all attempts",
    )


def _sample_fs_query_index(
    public_inputs: ClassicalCommittedPublicInputs,
    roots: tuple[ClassicalMerkleRoot, ...],
    fold_challenges: tuple[GoldilocksElement, ...],
    terminal_scalar: GoldilocksElement,
    *,
    label: str,
    resources: ResourceCounter | None,
) -> int:
    prefix = classical_fiat_shamir_prefix_term(
        public_inputs,
        roots,
        fold_challenges,
        terminal_scalar,
        purpose="query-index",
        label=label,
        attempt=0,
    )
    payload = FS_QUERY_DOMAIN + encode_term(prefix)
    if resources is not None:
        resources.consume_transcript_frames(1)
        resources.consume_sampler_attempts(1)
        resources.consume_hash(len(payload))
    # 256 is divisible by 64, so this is an exact uniform order-64 sampler.
    return hashlib.sha256(payload).digest()[0] & (DOMAIN_ORDERS[0] - 1)


def derive_fiat_shamir_values(
    public_inputs: ClassicalCommittedPublicInputs,
    roots: tuple[ClassicalMerkleRoot, ...],
    terminal_scalar: GoldilocksElement,
    resources: ResourceCounter | None = None,
) -> ClassicalFiatShamirValues:
    """Derive all fold challenges and query indices from the exact prefix."""

    if (
        type(roots) is not tuple
        or len(roots) != FOLD_ROUNDS
        or any(not isinstance(root, ClassicalMerkleRoot) for root in roots)
        or not isinstance(terminal_scalar, GoldilocksElement)
    ):
        raise malformed(
            "classical-fri:fs-derivation",
            "FRI-IOR-CLASSICAL-FS-012",
            "FS derivation requires three roots and one terminal scalar",
        )
    challenges: list[GoldilocksElement] = []
    for layer, label in enumerate(FS_FOLD_LABELS):
        challenges.append(
            _sample_fs_fold_challenge(
                public_inputs,
                roots[: layer + 1],
                tuple(challenges),
                label=label,
                resources=resources,
            )
        )
    challenge_tuple = tuple(challenges)
    queries = tuple(
        _sample_fs_query_index(
            public_inputs,
            roots,
            challenge_tuple,
            terminal_scalar,
            label=label,
            resources=resources,
        )
        for label in FS_QUERY_LABELS
    )
    return ClassicalFiatShamirValues(challenge_tuple, queries)


def classical_protocol_id(interpretation: str) -> SemanticId:
    """Identify Fresh and strong FS as protocols over one committed Core."""

    if interpretation not in (FRESH_INTERPRETATION, FIAT_SHAMIR_INTERPRETATION):
        raise malformed(
            "classical-fri:protocol-formation",
            "FRI-IOR-CLASSICAL-RUN-001",
            "the challenge interpretation is Fresh or FiatShamirStrong",
        )
    return semantic_id(
        "classical-fri-protocol",
        "classical-fri.protocol.v1",
        {
            "committed_core_id": EXACT_CLASSICAL_COMMITTED_CORE.identity.to_term(),
            "challenge_interpretation": interpretation,
            "fiat_shamir_prefix_schema": (
                FS_PREFIX_SCHEMA
                if interpretation == FIAT_SHAMIR_INTERPRETATION
                else None
            ),
        },
    )


@dataclass(frozen=True, slots=True)
class ClassicalCommittedRun:
    """One public committed execution; no complete oracle or owner salt table."""

    public_inputs: ClassicalCommittedPublicInputs
    proof: ClassicalCommittedProof
    interpretation: str
    fold_challenges: tuple[GoldilocksElement, ...]
    query_indices: tuple[int, ...]
    committed_core_id: SemanticId = field(
        default_factory=lambda: EXACT_CLASSICAL_COMMITTED_CORE.identity
    )
    schedule: tuple[ClassicalScheduleEvent, ...] = field(
        default=EXACT_COMMITTED_SCHEDULE
    )

    def __post_init__(self) -> None:
        if not isinstance(self.public_inputs, ClassicalCommittedPublicInputs):
            raise malformed(
                "classical-fri:run-formation",
                "FRI-IOR-CLASSICAL-RUN-002",
                "a committed run requires formed public inputs",
            )
        if not isinstance(self.proof, ClassicalCommittedProof):
            raise malformed(
                "classical-fri:run-formation",
                "FRI-IOR-CLASSICAL-RUN-003",
                "a committed run requires a formed public proof",
            )
        classical_protocol_id(self.interpretation)
        if (
            type(self.fold_challenges) is not tuple
            or len(self.fold_challenges) != FOLD_ROUNDS
            or any(
                not isinstance(challenge, GoldilocksElement)
                for challenge in self.fold_challenges
            )
        ):
            raise malformed(
                "classical-fri:run-formation",
                "FRI-IOR-CLASSICAL-RUN-004",
                "a committed run requires three formed fold challenges",
            )
        derive_layer_query_occurrences(self.query_indices)
        if not isinstance(self.committed_core_id, SemanticId):
            raise malformed(
                "classical-fri:run-formation",
                "FRI-IOR-CLASSICAL-RUN-005",
                "a committed run requires a typed committed Core identity",
            )
        if self.schedule != EXACT_COMMITTED_SCHEDULE:
            raise malformed(
                "classical-fri:run-formation",
                "FRI-IOR-CLASSICAL-RUN-006",
                "a committed run uses the exact committed schedule",
            )

    @property
    def protocol_id(self) -> SemanticId:
        return classical_protocol_id(self.interpretation)

    @property
    def public_environment(self) -> ClassicalPublicEnvironment:
        return self.public_inputs.public_environment

    def to_term(self) -> dict[str, Any]:
        return {
            "public_inputs_id": self.public_inputs.identity.to_term(),
            "proof_id": self.proof.identity.to_term(),
            "protocol_id": self.protocol_id.to_term(),
            "committed_core_id": self.committed_core_id.to_term(),
            "interpretation": self.interpretation,
            "fold_challenges": [
                challenge.to_term() for challenge in self.fold_challenges
            ],
            "query_indices": list(self.query_indices),
            "schedule": [event.to_term() for event in self.schedule],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "classical-fri-committed-run",
            "classical-fri.committed-run.v1",
            self.to_term(),
        )


def _opening_value_at_index(
    opening: ClassicalPairOpening,
    index: int,
    domain: ClassicalFriDomain,
) -> GoldilocksElement:
    if index == opening.pair_index:
        return opening.positive
    if index == opening.pair_index + domain.order // 2:
        return opening.negative
    raise refusal(
        "classical-fri:fold-target",
        "FRI-IOR-CLASSICAL-COMMITTED-021",
        "the selected next-layer opening does not contain the fold target index",
    )


def _verify_committed_run_with_resources(
    run: object,
    resources: ResourceCounter,
    *,
    fs_values_are_derived: bool,
) -> CheckResult:
    """Execute with one evaluator-owned counter and optional derived FS values."""

    boundary = "classical-fri:committed-verification"
    try:
        if not isinstance(run, ClassicalCommittedRun):
            raise malformed(
                boundary,
                "FRI-IOR-CLASSICAL-COMMITTED-001",
                "committed verification requires a ClassicalCommittedRun",
            )
        if (
            run.public_inputs.profile_id != EXACT_CLASSICAL_FRI_PROFILE.identity
            or run.public_inputs.committed_core_id
            != EXACT_CLASSICAL_COMMITTED_CORE.identity
        ):
            raise refusal(
                "classical-fri:committed-public-input-profile",
                "FRI-IOR-CLASSICAL-COMMITTED-002",
                "public inputs substituted the exact profile or committed Core",
            )
        public_environment = run.public_environment
        if (
            run.committed_core_id != EXACT_CLASSICAL_COMMITTED_CORE.identity
            or run.proof.committed_core_id != EXACT_CLASSICAL_COMMITTED_CORE.identity
        ):
            raise refusal(
                "classical-fri:committed-core",
                "FRI-IOR-CLASSICAL-COMMITTED-003",
                "the run or proof substituted the exact committed Core",
            )
        if run.schedule != EXACT_COMMITTED_SCHEDULE:
            raise refusal(
                "classical-fri:committed-schedule",
                "FRI-IOR-CLASSICAL-COMMITTED-004",
                "the run changed the exact committed schedule",
            )
        for layer, root in enumerate(run.proof.roots):
            if (
                root.layer != layer
                or root.commitment_profile_id
                != EXACT_CLASSICAL_COMMITMENT_PROFILE.identity
            ):
                raise refusal(
                    "classical-fri:committed-roots",
                    "FRI-IOR-CLASSICAL-COMMITTED-005",
                    "roots must cover M0, M1, and M2 under the exact profile",
                )

        if run.interpretation == FIAT_SHAMIR_INTERPRETATION:
            if not fs_values_are_derived:
                expected = derive_fiat_shamir_values(
                    run.public_inputs,
                    run.proof.roots,
                    run.proof.terminal_scalar,
                    resources,
                )
                if (
                    run.fold_challenges != expected.fold_challenges
                    or run.query_indices != expected.query_indices
                ):
                    raise refusal(
                        "classical-fri:fiat-shamir-interpretation",
                        "FRI-IOR-CLASSICAL-FS-013",
                        "the supplied values are not the exact strong-FS interpretation",
                    )
        elif run.interpretation != FRESH_INTERPRETATION:
            raise malformed(
                "classical-fri:challenge-interpretation",
                "FRI-IOR-CLASSICAL-COMMITTED-006",
                "the run challenge interpretation is not supported",
            )

        occurrences = derive_layer_query_occurrences(run.query_indices)
        proof_bytes = len(encode_classical_proof(run.proof))
        resources.consume_query_opening_resources(
            logical_query_occurrences=LAYER_QUERY_OCCURRENCES,
            unique_openings=len(run.proof.opening_table),
            proof_bytes=proof_bytes,
        )
        opening_keys = tuple(opening.key for opening in run.proof.opening_table)
        expected_keys = tuple(
            sorted(
                {
                    (occurrence.layer, occurrence.pair_index)
                    for occurrence in occurrences
                }
            )
        )
        if opening_keys != expected_keys:
            raise refusal(
                "classical-fri:opening-table",
                "FRI-IOR-CLASSICAL-COMMITTED-007",
                "the opening table must be sorted, unique, complete, and contain no extras",
            )
        if tuple(
            selector.occurrence_ordinal for selector in run.proof.occurrence_selectors
        ) != tuple(range(LAYER_QUERY_OCCURRENCES)):
            raise refusal(
                "classical-fri:occurrence-selectors",
                "FRI-IOR-CLASSICAL-COMMITTED-008",
                "selectors must preserve all twelve labelled occurrence ordinals",
            )
        selected_openings: list[ClassicalPairOpening] = []
        for occurrence, selector in zip(
            occurrences,
            run.proof.occurrence_selectors,
        ):
            if selector.opening_index >= len(run.proof.opening_table):
                raise refusal(
                    "classical-fri:occurrence-selectors",
                    "FRI-IOR-CLASSICAL-COMMITTED-009",
                    "an occurrence selector points outside the opening table",
                )
            opening = run.proof.opening_table[selector.opening_index]
            if opening.key != (occurrence.layer, occurrence.pair_index):
                raise refusal(
                    "classical-fri:occurrence-selectors",
                    "FRI-IOR-CLASSICAL-COMMITTED-010",
                    "an occurrence selector names the wrong layer pair",
                )
            selected_openings.append(opening)

        for opening in run.proof.opening_table:
            _verify_opening(
                CLASSICAL_DOMAINS[opening.layer],
                run.proof.roots[opening.layer],
                opening,
                resources,
            )

        points = tuple(domain.points() for domain in CLASSICAL_DOMAINS)
        for occurrence, opening in zip(occurrences, selected_openings):
            folded = binary_fold(
                points[occurrence.layer][occurrence.pair_index],
                opening.positive,
                opening.negative,
                run.fold_challenges[occurrence.layer],
                resources,
            )
            if occurrence.layer < FOLD_ROUNDS - 1:
                next_opening = selected_openings[occurrence.ordinal + 1]
                target = _opening_value_at_index(
                    next_opening,
                    occurrence.parent_index,
                    CLASSICAL_DOMAINS[occurrence.layer + 1],
                )
            else:
                target = run.proof.terminal_scalar
            if folded != target:
                if occurrence.layer == 0:
                    fold_code = "FRI-IOR-CLASSICAL-COMMITTED-021"
                elif occurrence.layer == 1:
                    fold_code = "FRI-IOR-CLASSICAL-COMMITTED-022"
                else:
                    fold_code = "FRI-IOR-CLASSICAL-COMMITTED-023"
                raise refusal(
                    f"classical-fri:fold-{occurrence.layer}",
                    fold_code,
                    "an authenticated binary fold does not match its next-layer value",
                )
        return affirmative(
            boundary,
            "FRI-IOR-CLASSICAL-COMMITTED-100",
            "the exact public committed classical FRI run accepts",
            subject=run.identity,
            protocol_id=run.protocol_id,
            committed_core_id=run.committed_core_id,
            public_inputs_id=run.public_inputs.identity,
            public_environment_id=public_environment.identity,
            statement_coordinate_id=public_environment.statement_coordinate_id,
            application_context_coordinate_id=(
                public_environment.application_context_coordinate_id
            ),
            proof_id=run.proof.identity,
            interpretation=run.interpretation,
            query_repetitions=QUERY_REPETITIONS,
            layer_query_occurrences=LAYER_QUERY_OCCURRENCES,
            authenticated_oracle_values=2 * LAYER_QUERY_OCCURRENCES,
            unique_openings=len(run.proof.opening_table),
            terminal="Accept",
            resources=resources.snapshot(),
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - deliberate fail-closed seam
        return checker_failure(
            boundary, f"unexpected committed verifier fault: {error}"
        )


def verify_committed_run(
    run: object,
    limits: ResourceLimits = DEFAULT_CLASSICAL_LIMITS,
) -> CheckResult:
    """Authenticate and execute one Fresh or strong-FS public run."""

    try:
        return _verify_committed_run_with_resources(
            run,
            _formed_counter(limits),
            fs_values_are_derived=False,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - deliberate fail-closed seam
        return checker_failure(
            "classical-fri:committed-verification",
            f"unexpected committed verifier fault: {error}",
        )


def verify_committed_fresh(
    public_inputs: object,
    proof: object,
    fold_challenges: object,
    query_indices: object,
    limits: ResourceLimits = DEFAULT_CLASSICAL_LIMITS,
) -> CheckResult:
    """Form and verify one public-coin run with environment-supplied coins."""

    try:
        run = ClassicalCommittedRun(
            public_inputs=public_inputs,
            proof=proof,
            interpretation=FRESH_INTERPRETATION,
            fold_challenges=fold_challenges,
            query_indices=query_indices,
        )
        return verify_committed_run(run, limits)
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - deliberate fail-closed seam
        return checker_failure(
            "classical-fri:fresh-verification",
            f"unexpected Fresh verifier fault: {error}",
        )


def verify_committed_fiat_shamir(
    public_inputs: object,
    proof: object,
    limits: ResourceLimits = DEFAULT_CLASSICAL_LIMITS,
) -> CheckResult:
    """Form and verify one strong-FS run from public inputs and public proof."""

    try:
        resources = _formed_counter(limits)
        if not isinstance(
            public_inputs, ClassicalCommittedPublicInputs
        ) or not isinstance(proof, ClassicalCommittedProof):
            raise malformed(
                "classical-fri:fiat-shamir-verification",
                "FRI-IOR-CLASSICAL-FS-014",
                "strong-FS verification requires exact public carriers",
            )
        values = derive_fiat_shamir_values(
            public_inputs,
            proof.roots,
            proof.terminal_scalar,
            resources,
        )
        run = ClassicalCommittedRun(
            public_inputs=public_inputs,
            proof=proof,
            interpretation=FIAT_SHAMIR_INTERPRETATION,
            fold_challenges=values.fold_challenges,
            query_indices=values.query_indices,
        )
        return _verify_committed_run_with_resources(
            run,
            resources,
            fs_values_are_derived=True,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - deliberate fail-closed seam
        return checker_failure(
            "classical-fri:fiat-shamir-verification",
            f"unexpected Fiat--Shamir verifier fault: {error}",
        )


@dataclass(frozen=True, slots=True)
class ClassicalCommittedCase:
    """Deterministic public runs plus explicitly owner-only generation salts."""

    native_trace: ClassicalNativeTrace
    fresh_run: ClassicalCommittedRun
    fiat_shamir_run: ClassicalCommittedRun
    owner_salts: tuple[tuple[bytes, ...], ...]

    def __post_init__(self) -> None:
        if not isinstance(self.native_trace, ClassicalNativeTrace):
            raise malformed(
                "classical-fri:case-formation",
                "FRI-IOR-CLASSICAL-CASE-001",
                "a case requires its exact native trace",
            )
        if not isinstance(self.fresh_run, ClassicalCommittedRun) or not isinstance(
            self.fiat_shamir_run, ClassicalCommittedRun
        ):
            raise malformed(
                "classical-fri:case-formation",
                "FRI-IOR-CLASSICAL-CASE-002",
                "a case requires formed Fresh and Fiat--Shamir runs",
            )
        if (
            self.fresh_run.interpretation != FRESH_INTERPRETATION
            or self.fiat_shamir_run.interpretation != FIAT_SHAMIR_INTERPRETATION
            or self.fresh_run.public_inputs != self.fiat_shamir_run.public_inputs
            or self.fresh_run.proof != self.fiat_shamir_run.proof
            or self.fresh_run.committed_core_id
            != self.fiat_shamir_run.committed_core_id
        ):
            raise malformed(
                "classical-fri:case-formation",
                "FRI-IOR-CLASSICAL-CASE-003",
                "Fresh and FS must interpret one public proof over one committed Core",
            )
        if (
            self.native_trace.public_environment
            != self.fresh_run.public_environment
            or self.native_trace.public_environment
            != self.fiat_shamir_run.public_environment
        ):
            raise malformed(
                "classical-fri:case-formation",
                "FRI-IOR-CLASSICAL-CASE-005",
                "native, Fresh, and FS runs must share one exact public environment",
            )
        if (
            type(self.owner_salts) is not tuple
            or len(self.owner_salts) != FOLD_ROUNDS
            or any(
                type(layer_salts) is not tuple
                or len(layer_salts) != DOMAIN_ORDERS[layer] // 2
                or any(
                    not isinstance(salt, bytes) or len(salt) != SALT_BYTES
                    for salt in layer_salts
                )
                for layer, layer_salts in enumerate(self.owner_salts)
            )
        ):
            raise malformed(
                "classical-fri:case-formation",
                "FRI-IOR-CLASSICAL-CASE-004",
                "owner salts require one exact table per committed layer",
            )


def _derive_owner_salts(
    salt_seed: bytes,
) -> tuple[tuple[bytes, ...], ...]:
    if not isinstance(salt_seed, bytes) or not salt_seed:
        raise malformed(
            "classical-fri:owner-salt-generation",
            "FRI-IOR-CLASSICAL-GENERATION-004",
            "deterministic salt generation requires a non-empty byte seed",
        )
    return tuple(
        tuple(
            hashlib.sha256(
                SALT_DERIVATION_DOMAIN
                + len(salt_seed).to_bytes(2, "big")
                + salt_seed
                + bytes((layer,))
                + pair_index.to_bytes(2, "big")
            ).digest()[:SALT_BYTES]
            for pair_index in range(DOMAIN_ORDERS[layer] // 2)
        )
        for layer in range(FOLD_ROUNDS)
    )


def build_honest_classical_case(
    statement: Any = DEFAULT_STATEMENT,
    application_context: Any = DEFAULT_APPLICATION_CONTEXT,
    source_coefficients: tuple[GoldilocksElement, ...] = DEFAULT_SOURCE_COEFFICIENTS,
    *,
    salt_seed: bytes = DEFAULT_SALT_SEED,
    salts_by_layer: tuple[tuple[bytes, ...], ...] | None = None,
    terminal_scalar_override: GoldilocksElement | None = None,
) -> ClassicalCommittedCase:
    """Generate deterministic native, Fresh, and strong-FS exact controls.

    ``salts_by_layer`` and the retained ``owner_salts`` are generation-owner
    material.  They are deliberately absent from both public run carriers and
    every verification entry point.
    """

    if (
        type(source_coefficients) is not tuple
        or len(source_coefficients) != DEGREE_BOUNDS[0]
        or any(
            not isinstance(coefficient, GoldilocksElement)
            for coefficient in source_coefficients
        )
    ):
        raise malformed(
            "classical-fri:committed-generation",
            "FRI-IOR-CLASSICAL-GENERATION-005",
            "the source polynomial has exactly eight Goldilocks coefficients",
        )
    if terminal_scalar_override is not None and not isinstance(
        terminal_scalar_override, GoldilocksElement
    ):
        raise malformed(
            "classical-fri:committed-generation",
            "FRI-IOR-CLASSICAL-GENERATION-006",
            "a terminal override remains one Goldilocks scalar",
        )
    owner_salts = (
        _derive_owner_salts(salt_seed) if salts_by_layer is None else salts_by_layer
    )
    if type(owner_salts) is not tuple or len(owner_salts) != FOLD_ROUNDS:
        raise malformed(
            "classical-fri:committed-generation",
            "FRI-IOR-CLASSICAL-GENERATION-007",
            "commitment generation requires three exact owner salt tables",
        )

    public_inputs = form_classical_public_inputs(statement, application_context)
    coefficient_layers: list[tuple[GoldilocksElement, ...]] = [source_coefficients]
    oracle_layers: list[ClassicalLogicalOracle] = []
    trees: list[ClassicalCommitmentTree] = []
    challenges: list[GoldilocksElement] = []
    for layer in range(FOLD_ROUNDS):
        oracle = ClassicalLogicalOracle(
            layer=layer,
            domain=CLASSICAL_DOMAINS[layer],
            origin="InitialOracle" if layer == 0 else "ProverOracle",
            values=tuple(
                evaluate_polynomial(coefficient_layers[layer], point)
                for point in CLASSICAL_DOMAINS[layer].points()
            ),
        )
        oracle_layers.append(oracle)
        tree = build_classical_commitment(oracle, owner_salts[layer])
        trees.append(tree)
        challenge = _sample_fs_fold_challenge(
            public_inputs,
            tuple(item.root for item in trees),
            tuple(challenges),
            label=FS_FOLD_LABELS[layer],
            resources=None,
        )
        challenges.append(challenge)
        coefficient_layers.append(_fold_coefficients(coefficient_layers[-1], challenge))
    if len(coefficient_layers[-1]) != 1:
        raise RuntimeError("exact committed generation did not reach one scalar")
    terminal_scalar = coefficient_layers[-1][0]
    if terminal_scalar_override is not None:
        terminal_scalar = terminal_scalar_override
    roots = tuple(tree.root for tree in trees)
    challenge_tuple = tuple(challenges)
    query_indices = tuple(
        _sample_fs_query_index(
            public_inputs,
            roots,
            challenge_tuple,
            terminal_scalar,
            label=label,
            resources=None,
        )
        for label in FS_QUERY_LABELS
    )
    occurrences = derive_layer_query_occurrences(query_indices)
    native_trace = ClassicalNativeTrace(
        profile=EXACT_CLASSICAL_FRI_PROFILE,
        native_core_id=EXACT_CLASSICAL_NATIVE_CORE.identity,
        public_environment=public_inputs.public_environment,
        oracles=tuple(oracle_layers),
        fold_challenges=challenge_tuple,
        terminal_scalar=terminal_scalar,
        query_indices=query_indices,
        query_occurrences=occurrences,
    )

    required_keys = tuple(
        sorted(
            {(occurrence.layer, occurrence.pair_index) for occurrence in occurrences}
        )
    )
    opening_table = tuple(
        trees[layer].open_pair(pair_index) for layer, pair_index in required_keys
    )
    opening_index_by_key = {
        opening.key: index for index, opening in enumerate(opening_table)
    }
    selectors = tuple(
        ClassicalOccurrenceSelector(
            occurrence.ordinal,
            opening_index_by_key[(occurrence.layer, occurrence.pair_index)],
        )
        for occurrence in occurrences
    )
    proof = ClassicalCommittedProof(
        roots=roots,
        terminal_scalar=terminal_scalar,
        opening_table=opening_table,
        occurrence_selectors=selectors,
    )
    fresh_run = ClassicalCommittedRun(
        public_inputs=public_inputs,
        proof=proof,
        interpretation=FRESH_INTERPRETATION,
        fold_challenges=challenge_tuple,
        query_indices=query_indices,
    )
    fiat_shamir_run = ClassicalCommittedRun(
        public_inputs=public_inputs,
        proof=proof,
        interpretation=FIAT_SHAMIR_INTERPRETATION,
        fold_challenges=challenge_tuple,
        query_indices=query_indices,
    )
    return ClassicalCommittedCase(
        native_trace=native_trace,
        fresh_run=fresh_run,
        fiat_shamir_run=fiat_shamir_run,
        owner_salts=owner_salts,
    )
