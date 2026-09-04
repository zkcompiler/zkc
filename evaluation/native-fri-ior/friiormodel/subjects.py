"""Typed semantic subjects for the selected native-to-Fiat--Shamir factorization.

The objects in this module are immutable semantic subjects identified from
closed canonical terms.  They are not executions, proof artifacts, evidence
records, or theorem results.  Classes whose names end in ``Declaration`` state
obligations that later checkers must discharge; their mere formation never
asserts that those obligations hold.  The separately admitted checked
Fiat--Shamir construction establishes only its explicit structural law.

The factorization has three Core subjects.  Native FRI grants logical-oracle
access and has neither commitments nor work.  Committed FRI replaces logical
access with caps, openings, and authentication, but still has no work step.
The work-augmented committed Core inserts a fresh work seed, nonce publication,
and deterministic work check before query randomness.  Fresh and
Fiat--Shamir Protocols share exactly that last Core and differ only in their
challenge-interpretation subjects.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, ClassVar

from .commitment import EXACT_COMMITMENT_PROFILE
from .profile import EXACT_ALGEBRA_PROFILE
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    SemanticId,
    affirmative,
    semantic_id,
)
from .transcript import (
    CANONICAL_CONSTRUCTION_PLAN,
    DERIVE_CHALLENGE,
    EXACT_GRINDING_PROFILE,
    QUERY_OCCURRENCES,
    QUERY_SEED,
    SAMPLE_OCCURRENCES,
    TranscriptConstructionPlan,
)


NATIVE_CORE_SCHEMA = "zkc.native-fri-ior.native-core.v1"
COMMITTED_CORE_SCHEMA = "zkc.native-fri-ior.committed-core.v1"
WORK_AUGMENTED_CORE_SCHEMA = (
    "zkc.native-fri-ior.work-augmented-committed-core.v1"
)
CHALLENGE_INTERPRETATION_SCHEMA = (
    "zkc.native-fri-ior.challenge-interpretation.v1"
)
PROTOCOL_SCHEMA = "zkc.native-fri-ior.protocol.v1"
COMMITMENT_COMPILATION_SCHEMA = (
    "zkc.native-fri-ior.checked-commitment-compilation-declaration.v1"
)
GRINDING_AUGMENTATION_SCHEMA = (
    "zkc.native-fri-ior.checked-grinding-augmentation-declaration.v1"
)
FIAT_SHAMIR_CONSTRUCTION_SCHEMA = (
    "zkc.native-fri-ior.checked-fiat-shamir-construction-declaration.v1"
)
ADMITTED_FIAT_SHAMIR_CONSTRUCTION_SCHEMA = (
    "zkc.native-fri-ior.checked-fiat-shamir-construction.v1"
)

DECLARATION_STATUS = "requirements-declared-not-discharged"

NATIVE_CORE_NONCLAIMS = (
    "proximity-soundness",
    "proximity-completeness",
    "outer-computation-relation",
    "commitment-binding-hiding-or-extractability",
    "work-amplification",
    "adversary-strategy-non-anticipation",
)
COMMITTED_CORE_NONCLAIMS = (
    "native-to-committed-correspondence",
    "commitment-binding-hiding-or-extractability",
    "proximity-soundness-or-completeness",
    "outer-computation-relation",
    "work-amplification",
)
WORK_AUGMENTED_CORE_NONCLAIMS = (
    "committed-to-work-augmented-correspondence",
    "soundness-amplification-from-work",
    "expected-honest-work-bound",
    "proximity-soundness-or-completeness",
    "outer-computation-relation",
)
FRESH_INTERPRETATION_NONCLAIMS = (
    "fresh-coin-quality-or-independence-proof",
    "protocol-soundness-or-completeness",
    "knowledge-or-zero-knowledge",
)
FIAT_SHAMIR_INTERPRETATION_NONCLAIMS = (
    "random-oracle-instantiation-security",
    "classical-rom-or-qrom-security",
    "knowledge-soundness-or-extraction",
    "protocol-property-transport",
)
PROTOCOL_NONCLAIMS = (
    "protocol-soundness-or-completeness",
    "knowledge-or-zero-knowledge",
    "outer-computation-relation",
)
COMMITMENT_COMPILATION_NONCLAIMS = (
    "proof-that-the-declared-requirements-hold",
    "commitment-binding-hiding-or-extractability",
    "native-property-transport",
    "cryptographic-security",
)
GRINDING_AUGMENTATION_NONCLAIMS = (
    "proof-that-the-declared-requirements-hold",
    "soundness-amplification-from-work",
    "expected-honest-work-bound",
    "protocol-property-transport",
)
FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS = (
    "proof-that-the-declared-requirements-hold",
    "classical-rom-security",
    "qrom-security",
    "knowledge-soundness-or-extraction",
    "protocol-property-transport",
    "structural-admission-is-not-a-security-proof",
)

COMMITMENT_COMPILATION_CAPABILITIES = (
    "logical-oracle-publication-map",
    "commitment-advice-ownership",
    "ordered-cap-construction",
    "query-occurrence-map-preserving-order-and-multiplicity",
    "opening-selection-and-authentication",
    "source-answer-extraction",
    "public-target-replay-without-logical-oracle-carriers",
)
COMMITMENT_COMPILATION_REQUIREMENTS = (
    "complete-source-and-target-occurrence-coverage",
    "exact-profile-and-codec-agreement",
    "causality-preservation",
    "typed-answer-to-opening-correspondence",
    "decision-map",
    "constructed-trace-commutation",
)
GRINDING_AUGMENTATION_CAPABILITIES = (
    "preserved-committed-occurrence-map",
    "inserted-work-seed-challenge",
    "inserted-nonce-publication",
    "inserted-deterministic-work-check",
    "post-work-query-suffix-map",
)
GRINDING_AUGMENTATION_REQUIREMENTS = (
    "all-committed-checks-preserved",
    "work-seed-after-terminal-material",
    "nonce-and-work-check-before-query-randomness",
    "constructed-valid-work-trace-commutation",
    "invalid-work-rejection-is-target-only",
)
FIAT_SHAMIR_CONSTRUCTION_CAPABILITIES = (
    "statement-and-application-context-binding",
    "typed-publication-framing",
    "domain-separated-challenge-derivation",
    "bounded-rejection-sampling",
    "work-seed-and-construction-internal-query-seed-separation",
    "ordered-query-occurrence-derivation",
)
FIAT_SHAMIR_CONSTRUCTION_REQUIREMENTS = (
    "source-and-target-share-exactly-one-core-identity",
    "every-required-publication-influences-each-dependent-challenge",
    "work-check-precedes-query-randomness",
    "exact-transcript-plan-admission",
    "fresh-to-derived-challenge-correspondence",
)

_NATIVE_EVENT_SCHEDULE = (
    "publish-initial-logical-oracle",
    "fresh-fold-challenge-0",
    "publish-prover-logical-oracle",
    "fresh-fold-challenge-1",
    "publish-terminal-polynomial",
    "sample-fresh-ordered-query-occurrence-vector",
    "answer-logical-oracle-queries",
    "check-fold-round-0",
    "check-fold-round-1-terminal-evaluation",
    "check-terminal-degree",
    "emit-accept-or-reject",
)
_COMMITTED_EVENT_SCHEDULE = (
    "publish-cap-0",
    "fresh-fold-challenge-0",
    "publish-cap-1",
    "fresh-fold-challenge-1",
    "publish-terminal-polynomial",
    "sample-fresh-ordered-query-occurrence-vector",
    "publish-opening-table-and-occurrence-selectors",
    "check-opening-coverage-and-authentication",
    "check-fold-round-0",
    "check-fold-round-1-terminal-evaluation",
    "check-terminal-degree",
    "emit-accept-or-reject",
)
_WORK_AUGMENTED_EVENT_SCHEDULE = (
    "publish-cap-0",
    "fresh-fold-challenge-0",
    "publish-cap-1",
    "fresh-fold-challenge-1",
    "publish-terminal-polynomial",
    "fresh-work-seed",
    "publish-grinding-nonce",
    "check-work-seed-and-nonce",
    "sample-fresh-ordered-query-occurrence-vector",
    "publish-opening-table-and-occurrence-selectors",
    "check-opening-coverage-and-authentication",
    "check-fold-round-0",
    "check-fold-round-1-terminal-evaluation",
    "check-terminal-degree",
    "emit-accept-or-reject",
)
_AUGMENTED_CHALLENGES = (
    "fold-challenge[0]",
    "fold-challenge[1]",
    "work-seed",
    "query-occurrences",
)
_AUGMENTED_CHALLENGE_TYPES = (
    ("fold-challenge[0]", "F97Extension2"),
    ("fold-challenge[1]", "F97Extension2"),
    ("work-seed", "Bytes32"),
    (
        "query-occurrences",
        "OrderedQueryOccurrenceVector<length=4,index-domain=D0,with-replacement>",
    ),
)
_AUGMENTED_ACCEPTANCE_AFFECTING_PUBLIC_OCCURRENCES = (
    "statement",
    "application-context",
    "cap[0]",
    "fold-challenge[0]",
    "cap[1]",
    "fold-challenge[1]",
    "terminal-polynomial",
    "work-seed",
    "grinding-nonce",
    "query-occurrences",
    "opening-table-and-occurrence-selectors",
)
_PUBLIC_CONTEXT_PORTS = (
    ("statement", "Statement"),
    ("application-context", "ApplicationBinding"),
)

TRANSCRIPT_FRAME = "TranscriptFrame"
DERIVED_CHALLENGE = "DerivedChallenge"
DETERMINISTIC_SAMPLE = "DeterministicSample"
POST_FINAL_CHALLENGE_PUBLIC_RESPONSE = "PostFinalChallengePublicResponse"
_PROTECTION_DISPOSITIONS = frozenset(
    {
        TRANSCRIPT_FRAME,
        DERIVED_CHALLENGE,
        DETERMINISTIC_SAMPLE,
        POST_FINAL_CHALLENGE_PUBLIC_RESPONSE,
    }
)


def _semantic_ref(identity: SemanticId) -> dict[str, Any]:
    return identity.to_term()


def _public_context_port_terms() -> list[dict[str, str]]:
    return [
        {
            "occurrence": occurrence,
            "port_kind": "Context",
            "owner": "PublicEnvironment",
            "visibility": "Public",
            "multiplicity": "ExactlyOne",
            "semantic_purpose": purpose,
            "value_type": "ClosedFiniteTerm",
        }
        for occurrence, purpose in _PUBLIC_CONTEXT_PORTS
    ]


def _raise_kind_mismatch(where: str, expected: str) -> None:
    raise ModelFailure(
        OutcomeClass.KIND_MISMATCH,
        "subjects:endpoint-formation",
        "FRI-IOR-SUBJECT-001",
        f"{where} requires a {expected} semantic subject",
    )


def transcript_plan_identity(plan: TranscriptConstructionPlan) -> SemanticId:
    """Return the semantic identity owned by the typed transcript plan."""

    if not isinstance(plan, TranscriptConstructionPlan):
        raise ModelFailure(
            OutcomeClass.MALFORMED,
            "subjects:transcript-plan-identity",
            "FRI-IOR-SUBJECT-009",
            "transcript-plan identity requires a TranscriptConstructionPlan",
        )
    return plan.identity


class _SemanticSubject:
    """Shared identity operation; concrete terms remain class-owned."""

    SUBJECT_KIND: ClassVar[str]
    IDENTITY_DOMAIN: ClassVar[str]

    def to_term(self) -> dict[str, Any]:
        raise NotImplementedError

    @property
    def identity(self) -> SemanticId:
        return semantic_id(self.SUBJECT_KIND, self.IDENTITY_DOMAIN, self.to_term())


@dataclass(frozen=True, slots=True)
class NativeFriCore(_SemanticSubject):
    """Native logical-oracle FRI with no commitment or work capability."""

    algebra_profile_id: SemanticId = EXACT_ALGEBRA_PROFILE.identity

    SUBJECT_KIND: ClassVar[str] = "native-fri-core"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.core.native.v1"

    def __post_init__(self) -> None:
        if (
            not isinstance(self.algebra_profile_id, SemanticId)
            or self.algebra_profile_id.subject_kind != "fri-algebra-profile"
        ):
            _raise_kind_mismatch("algebra_profile_id", "FriAlgebraProfile identity")

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": NATIVE_CORE_SCHEMA,
            "algebra_profile_id": _semantic_ref(self.algebra_profile_id),
            "public_context_ports": _public_context_port_terms(),
            "oracle_publication": {
                "mode": "LogicalAccess",
                "origins": ["InitialOracle", "ProverOracle"],
                "fixation": "immutable-exact-domain-function",
                "public_observation": "access-metadata-not-full-carrier",
            },
            "event_schedule": list(_NATIVE_EVENT_SCHEDULE),
            "query_model": {
                "capability": "declared-logical-query-access",
                "occurrences": "ordered-with-multiplicity",
                "fresh_randomness": (
                    "ordered-query-occurrence-vector-with-replacement"
                ),
                "query_seed": "absent-from-native-core",
                "physical_openings": "absent",
            },
            "checks": [
                "exact-domain-oracle-admission",
                "declared-dependency-order",
                "sampled-fold-consistency",
                "terminal-evaluation",
                "terminal-degree",
            ],
            "excluded_capabilities": [
                "commitment-caps",
                "proof-supplied-openings",
                "authentication",
                "work-seed",
                "grinding-nonce",
                "work-check",
            ],
            "terminal": "AcceptOrReject",
            "nonclaims": list(NATIVE_CORE_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class CommittedFriCore(_SemanticSubject):
    """Public committed FRI with authenticated openings and no work step."""

    algebra_profile_id: SemanticId = EXACT_ALGEBRA_PROFILE.identity
    commitment_profile_id: SemanticId = EXACT_COMMITMENT_PROFILE.identity

    SUBJECT_KIND: ClassVar[str] = "committed-fri-core"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.core.committed.v1"

    def __post_init__(self) -> None:
        expected = (
            (
                self.algebra_profile_id,
                "fri-algebra-profile",
                "algebra_profile_id",
                "typed FriAlgebraProfile identity",
            ),
            (
                self.commitment_profile_id,
                "fri-commitment-profile",
                "commitment_profile_id",
                "typed FriCommitmentProfile identity",
            ),
        )
        for value, subject_kind, field_name, label in expected:
            if (
                not isinstance(value, SemanticId)
                or value.subject_kind != subject_kind
            ):
                _raise_kind_mismatch(field_name, label)

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": COMMITTED_CORE_SCHEMA,
            "algebra_profile_id": _semantic_ref(self.algebra_profile_id),
            "commitment_profile_id": _semantic_ref(self.commitment_profile_id),
            "public_context_ports": _public_context_port_terms(),
            "publication_model": {
                "oracle_publication": "absent",
                "caps": ["cap[0]", "cap[1]"],
                "opening_source": "proof-supplied-public-material",
                "private_logical_oracle_capability": "absent",
            },
            "event_schedule": list(_COMMITTED_EVENT_SCHEDULE),
            "query_model": {
                "logical_occurrences": "ordered-with-multiplicity",
                "fresh_randomness": (
                    "ordered-query-occurrence-vector-with-replacement"
                ),
                "query_seed": "absent-from-committed-core",
                "physical_openings": "canonical-deduplicated-table",
                "occurrence_selectors": "total-over-logical-occurrences",
            },
            "checks": [
                "opening-coverage",
                "cap-authentication",
                "sampled-fold-consistency",
                "terminal-evaluation",
                "terminal-degree",
            ],
            "excluded_capabilities": [
                "logical-oracle-access",
                "work-seed",
                "grinding-nonce",
                "work-check",
            ],
            "terminal": "AcceptOrReject",
            "nonclaims": list(COMMITTED_CORE_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class WorkAugmentedCommittedFriCore(_SemanticSubject):
    """Committed FRI with an explicit pre-query deterministic work gate."""

    committed_core: CommittedFriCore = field(default_factory=CommittedFriCore)
    grinding_profile_id: SemanticId = EXACT_GRINDING_PROFILE.identity
    public_coin: bool = True
    challenge_occurrences: tuple[str, ...] = _AUGMENTED_CHALLENGES
    acceptance_affecting_public_occurrences: tuple[str, ...] = (
        _AUGMENTED_ACCEPTANCE_AFFECTING_PUBLIC_OCCURRENCES
    )

    SUBJECT_KIND: ClassVar[str] = "work-augmented-committed-fri-core"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.core.work-augmented-committed.v1"

    def __post_init__(self) -> None:
        if type(self.committed_core) is not CommittedFriCore:
            _raise_kind_mismatch("committed_core", "CommittedFriCore")
        if (
            not isinstance(self.grinding_profile_id, SemanticId)
            or self.grinding_profile_id.subject_kind != "fri-grinding-profile"
        ):
            _raise_kind_mismatch(
                "grinding_profile_id",
                "FriGrindingProfile identity",
            )
        if type(self.public_coin) is not bool:
            _raise_kind_mismatch("public_coin", "boolean")
        for value, where in (
            (self.challenge_occurrences, "challenge_occurrences"),
            (
                self.acceptance_affecting_public_occurrences,
                "acceptance_affecting_public_occurrences",
            ),
        ):
            if not isinstance(value, tuple) or not all(
                isinstance(item, str) and item for item in value
            ):
                _raise_kind_mismatch(where, "canonical text sequence")

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": WORK_AUGMENTED_CORE_SCHEMA,
            "preserved_committed_core_id": _semantic_ref(
                self.committed_core.identity
            ),
            "grinding_profile_id": _semantic_ref(self.grinding_profile_id),
            "public_context_ports": self.committed_core.to_term()[
                "public_context_ports"
            ],
            "event_schedule": list(_WORK_AUGMENTED_EVENT_SCHEDULE),
            "challenge_contract": {
                "public_coin": self.public_coin,
                "occurrences": list(self.challenge_occurrences),
                "occurrence_types": [
                    {"occurrence": occurrence, "value_type": value_type}
                    for occurrence, value_type in _AUGMENTED_CHALLENGE_TYPES
                ],
                "source": "abstract-verifier-public-coin-interface",
            },
            "acceptance_affecting_public_occurrences": list(
                self.acceptance_affecting_public_occurrences
            ),
            "inserted_work_effects": {
                "placement": "after-terminal-material-before-query-randomness",
                "work_seed": "fresh-public-bytes32-challenge",
                "nonce": "prover-publication-selected-grinding-nonce-type",
                "check": "selected-grinding-profile-total-predicate",
                "failure": "Reject",
            },
            "preserved_checks": list(
                self.committed_core.to_term()["checks"]
            ),
            "additional_check": "work-seed-and-nonce",
            "terminal": "AcceptOrReject",
            "nonclaims": list(WORK_AUGMENTED_CORE_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class FreshChallengeInterpretation(_SemanticSubject):
    """Verifier-fresh interpretation of every augmented-Core challenge."""

    core: WorkAugmentedCommittedFriCore = field(
        default_factory=WorkAugmentedCommittedFriCore
    )

    SUBJECT_KIND: ClassVar[str] = "challenge-interpretation"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.challenge-interpretation.v1"

    def __post_init__(self) -> None:
        if type(self.core) is not WorkAugmentedCommittedFriCore:
            _raise_kind_mismatch(
                "core",
                "WorkAugmentedCommittedFriCore",
            )
        if self.core.challenge_occurrences != _AUGMENTED_CHALLENGES:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "subjects:challenge-interpretation-formation",
                "FRI-IOR-SUBJECT-033",
                "the Fresh interpretation must resolve the Core-owned challenge inventory exactly",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": CHALLENGE_INTERPRETATION_SCHEMA,
            "kind": "Fresh",
            "core_id": _semantic_ref(self.core.identity),
            "challenge_occurrences": list(self.core.challenge_occurrences),
            "resolution": [
                {
                    "occurrence": "fold-challenge[0]",
                    "source": "verifier-fresh-public-coin",
                    "value_type": "F97Extension2",
                },
                {
                    "occurrence": "fold-challenge[1]",
                    "source": "verifier-fresh-public-coin",
                    "value_type": "F97Extension2",
                },
                {
                    "occurrence": "work-seed",
                    "source": "verifier-fresh-public-coin",
                    "value_type": "Bytes32",
                },
                {
                    "occurrence": "query-occurrences",
                    "source": "verifier-fresh-direct-uniform-sampling",
                    "value_type": (
                        "OrderedQueryOccurrenceVector<length=4,index-domain=D0,with-replacement>"
                    ),
                },
            ],
            "nonclaims": list(FRESH_INTERPRETATION_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class FiatShamirChallengeInterpretation(_SemanticSubject):
    """The exact typed transcript interpretation of augmented-Core coins."""

    core: WorkAugmentedCommittedFriCore = field(
        default_factory=WorkAugmentedCommittedFriCore
    )
    construction_plan: TranscriptConstructionPlan = CANONICAL_CONSTRUCTION_PLAN

    SUBJECT_KIND: ClassVar[str] = "challenge-interpretation"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.challenge-interpretation.v1"

    def __post_init__(self) -> None:
        if type(self.core) is not WorkAugmentedCommittedFriCore:
            _raise_kind_mismatch(
                "core",
                "WorkAugmentedCommittedFriCore",
            )
        if self.core.challenge_occurrences != _AUGMENTED_CHALLENGES:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "subjects:challenge-interpretation-formation",
                "FRI-IOR-SUBJECT-033",
                "the Fiat--Shamir interpretation must resolve the Core-owned challenge inventory exactly",
            )
        if type(self.construction_plan) is not TranscriptConstructionPlan:
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:challenge-interpretation-formation",
                "FRI-IOR-SUBJECT-002",
                "Fiat--Shamir interpretation requires a transcript plan",
            )
        if (
            self.construction_plan.identity
            != CANONICAL_CONSTRUCTION_PLAN.identity
        ):
            raise ModelFailure(
                OutcomeClass.UNSUPPORTED,
                "subjects:challenge-interpretation-formation",
                "FRI-IOR-SUBJECT-003",
                "the challenge interpretation uses an unsupported transcript plan",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": CHALLENGE_INTERPRETATION_SCHEMA,
            "kind": "FiatShamir",
            "core_id": _semantic_ref(self.core.identity),
            "challenge_occurrences": list(self.core.challenge_occurrences),
            "transcript_construction_plan_id": _semantic_ref(
                transcript_plan_identity(self.construction_plan)
            ),
            "transcript_construction": self.construction_plan.to_term(),
            "core_query_resolution": {
                "core_occurrence": "query-occurrences",
                "core_value_type": (
                    "OrderedQueryOccurrenceVector<length=4,index-domain=D0,with-replacement>"
                ),
                "construction_internal_state": "query-seed",
                "transcript_result_occurrence": "query-occurrences",
                "rule": "derive-seed-then-expand-ordered-occurrences",
            },
            "nonclaims": list(FIAT_SHAMIR_INTERPRETATION_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class FreshWorkAugmentedProtocol(_SemanticSubject):
    """Fresh-coin Protocol over the work-augmented committed Core."""

    core: WorkAugmentedCommittedFriCore = field(
        default_factory=WorkAugmentedCommittedFriCore
    )
    challenge_interpretation: FreshChallengeInterpretation = field(
        default_factory=FreshChallengeInterpretation
    )

    SUBJECT_KIND: ClassVar[str] = "fri-protocol"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.protocol.v1"

    def __post_init__(self) -> None:
        if type(self.core) is not WorkAugmentedCommittedFriCore:
            _raise_kind_mismatch(
                "core",
                "WorkAugmentedCommittedFriCore",
            )
        if type(self.challenge_interpretation) is not FreshChallengeInterpretation:
            _raise_kind_mismatch(
                "challenge_interpretation",
                "FreshChallengeInterpretation",
            )
        if self.challenge_interpretation.core.identity != self.core.identity:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "subjects:protocol-formation",
                "FRI-IOR-SUBJECT-004",
                "the fresh challenge interpretation names a different Core",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": PROTOCOL_SCHEMA,
            "core_id": _semantic_ref(self.core.identity),
            "challenge_interpretation_id": _semantic_ref(
                self.challenge_interpretation.identity
            ),
            "factorization": "ProtocolEqualsCorePlusChallengeInterpretation",
            "nonclaims": list(PROTOCOL_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class FiatShamirWorkAugmentedProtocol(_SemanticSubject):
    """Fiat--Shamir Protocol over the same work-augmented committed Core."""

    core: WorkAugmentedCommittedFriCore = field(
        default_factory=WorkAugmentedCommittedFriCore
    )
    challenge_interpretation: FiatShamirChallengeInterpretation = field(
        default_factory=FiatShamirChallengeInterpretation
    )

    SUBJECT_KIND: ClassVar[str] = "fri-protocol"
    IDENTITY_DOMAIN: ClassVar[str] = "fri-ior.protocol.v1"

    def __post_init__(self) -> None:
        if type(self.core) is not WorkAugmentedCommittedFriCore:
            _raise_kind_mismatch(
                "core",
                "WorkAugmentedCommittedFriCore",
            )
        if (
            type(self.challenge_interpretation)
            is not FiatShamirChallengeInterpretation
        ):
            _raise_kind_mismatch(
                "challenge_interpretation",
                "FiatShamirChallengeInterpretation",
            )
        if self.challenge_interpretation.core.identity != self.core.identity:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "subjects:protocol-formation",
                "FRI-IOR-SUBJECT-004",
                "the Fiat--Shamir challenge interpretation names a different Core",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": PROTOCOL_SCHEMA,
            "core_id": _semantic_ref(self.core.identity),
            "challenge_interpretation_id": _semantic_ref(
                self.challenge_interpretation.identity
            ),
            "factorization": "ProtocolEqualsCorePlusChallengeInterpretation",
            "nonclaims": list(PROTOCOL_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class CheckedCommitmentCompilationDeclaration(_SemanticSubject):
    """Requirements for compiling native logical access to public openings."""

    source: NativeFriCore = field(default_factory=NativeFriCore)
    target: CommittedFriCore = field(default_factory=CommittedFriCore)

    SUBJECT_KIND: ClassVar[str] = "commitment-compilation-declaration"
    IDENTITY_DOMAIN: ClassVar[str] = (
        "fri-ior.construction.commitment-compilation.v1"
    )

    def __post_init__(self) -> None:
        if type(self.source) is not NativeFriCore:
            _raise_kind_mismatch("source", "NativeFriCore")
        if type(self.target) is not CommittedFriCore:
            _raise_kind_mismatch("target", "CommittedFriCore")

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": COMMITMENT_COMPILATION_SCHEMA,
            "declaration_status": DECLARATION_STATUS,
            "source_core_id": _semantic_ref(self.source.identity),
            "target_core_id": _semantic_ref(self.target.identity),
            "required_capabilities": list(COMMITMENT_COMPILATION_CAPABILITIES),
            "admission_requirements": list(COMMITMENT_COMPILATION_REQUIREMENTS),
            "nonclaims": list(COMMITMENT_COMPILATION_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class CheckedGrindingAugmentationDeclaration(_SemanticSubject):
    """Requirements for inserting the target-visible pre-query work gate."""

    source: CommittedFriCore = field(default_factory=CommittedFriCore)
    target: WorkAugmentedCommittedFriCore = field(
        default_factory=WorkAugmentedCommittedFriCore
    )

    SUBJECT_KIND: ClassVar[str] = "grinding-augmentation-declaration"
    IDENTITY_DOMAIN: ClassVar[str] = (
        "fri-ior.construction.grinding-augmentation.v1"
    )

    def __post_init__(self) -> None:
        if type(self.source) is not CommittedFriCore:
            _raise_kind_mismatch("source", "CommittedFriCore")
        if type(self.target) is not WorkAugmentedCommittedFriCore:
            _raise_kind_mismatch(
                "target",
                "WorkAugmentedCommittedFriCore",
            )
        if self.target.committed_core.identity != self.source.identity:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "subjects:construction-formation",
                "FRI-IOR-SUBJECT-005",
                "the grinding target does not preserve its declared source Core",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": GRINDING_AUGMENTATION_SCHEMA,
            "declaration_status": DECLARATION_STATUS,
            "source_core_id": _semantic_ref(self.source.identity),
            "target_core_id": _semantic_ref(self.target.identity),
            "required_capabilities": list(GRINDING_AUGMENTATION_CAPABILITIES),
            "admission_requirements": list(GRINDING_AUGMENTATION_REQUIREMENTS),
            "nonclaims": list(GRINDING_AUGMENTATION_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class CheckedFiatShamirConstructionDeclaration(_SemanticSubject):
    """Same-Core Fresh-to-derived challenge-construction requirements."""

    source: FreshWorkAugmentedProtocol = field(
        default_factory=FreshWorkAugmentedProtocol
    )
    target: FiatShamirWorkAugmentedProtocol = field(
        default_factory=FiatShamirWorkAugmentedProtocol
    )

    SUBJECT_KIND: ClassVar[str] = "fiat-shamir-construction-declaration"
    IDENTITY_DOMAIN: ClassVar[str] = (
        "fri-ior.construction.fiat-shamir.v1"
    )

    def __post_init__(self) -> None:
        if type(self.source) is not FreshWorkAugmentedProtocol:
            _raise_kind_mismatch(
                "source",
                "FreshWorkAugmentedProtocol",
            )
        if type(self.target) is not FiatShamirWorkAugmentedProtocol:
            _raise_kind_mismatch(
                "target",
                "FiatShamirWorkAugmentedProtocol",
            )
        if self.source.core.identity != self.target.core.identity:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                "subjects:construction-formation",
                "FRI-IOR-SUBJECT-006",
                "Fiat--Shamir construction endpoints must share one Core identity",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": FIAT_SHAMIR_CONSTRUCTION_SCHEMA,
            "declaration_status": DECLARATION_STATUS,
            "source_protocol_id": _semantic_ref(self.source.identity),
            "target_protocol_id": _semantic_ref(self.target.identity),
            "shared_core_id": _semantic_ref(self.source.core.identity),
            "source_challenge_interpretation_id": _semantic_ref(
                self.source.challenge_interpretation.identity
            ),
            "target_challenge_interpretation_id": _semantic_ref(
                self.target.challenge_interpretation.identity
            ),
            "required_capabilities": list(FIAT_SHAMIR_CONSTRUCTION_CAPABILITIES),
            "admission_requirements": list(FIAT_SHAMIR_CONSTRUCTION_REQUIREMENTS),
            "nonclaims": list(FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class PublicOccurrenceProtection:
    """Total-map entry for one acceptance-affecting public occurrence.

    A post-final-challenge response has no transcript position because no later
    verifier coin can depend on it.  Its explicit disposition keeps it inside
    the total map instead of silently treating absence as success.
    """

    core_occurrence: str
    transcript_occurrence: str | None
    transcript_position: int | None
    protected_dependents: tuple[str, ...]
    disposition: str

    def __post_init__(self) -> None:
        if not isinstance(self.core_occurrence, str) or not self.core_occurrence:
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-010",
                "a protection-map entry requires a Core occurrence name",
            )
        if self.transcript_occurrence is not None and (
            not isinstance(self.transcript_occurrence, str)
            or not self.transcript_occurrence
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-011",
                "a transcript occurrence must be nonempty text or absent",
            )
        if self.transcript_position is not None and (
            type(self.transcript_position) is not int
            or self.transcript_position < 0
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-012",
                "a transcript position must be a non-negative integer or absent",
            )
        if (self.transcript_occurrence is None) != (
            self.transcript_position is None
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-013",
                "transcript occurrence and position must be present or absent together",
            )
        if not isinstance(self.protected_dependents, tuple) or not all(
            isinstance(item, str) and item
            for item in self.protected_dependents
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-014",
                "protected dependents must be a canonical text sequence",
            )
        if len(set(self.protected_dependents)) != len(
            self.protected_dependents
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-015",
                "protected dependents must not contain duplicates",
            )
        if self.disposition not in _PROTECTION_DISPOSITIONS:
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-016",
                "a protection-map entry has an unknown disposition",
            )
        if self.disposition == POST_FINAL_CHALLENGE_PUBLIC_RESPONSE and (
            self.transcript_occurrence is not None
            or self.protected_dependents
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:protection-map-formation",
                "FRI-IOR-SUBJECT-017",
                "a post-final-challenge response has no transcript position or dependents",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "core_occurrence": self.core_occurrence,
            "transcript_occurrence": self.transcript_occurrence,
            "transcript_position": self.transcript_position,
            "protected_dependents": list(self.protected_dependents),
            "disposition": self.disposition,
        }


def _plan_disposition(kind: str) -> str:
    if kind == "AbsorbPublication":
        return TRANSCRIPT_FRAME
    if kind == "DeriveChallenge":
        return DERIVED_CHALLENGE
    if kind == "SampleOccurrences":
        return DETERMINISTIC_SAMPLE
    raise ModelFailure(
        OutcomeClass.REFUSED,
        "subjects:fiat-shamir-admission",
        "FRI-IOR-SUBJECT-018",
        "a public Core occurrence maps to a non-public transcript step",
    )


def _expected_protection_map(
    core_term: dict[str, Any],
    plan: TranscriptConstructionPlan,
) -> tuple[PublicOccurrenceProtection, ...]:
    occurrences = core_term.get("acceptance_affecting_public_occurrences")
    if not isinstance(occurrences, list) or not all(
        isinstance(item, str) and item for item in occurrences
    ):
        raise ModelFailure(
            OutcomeClass.MALFORMED,
            "subjects:fiat-shamir-admission",
            "FRI-IOR-SUBJECT-019",
            "the Core lacks a formed acceptance-affecting occurrence inventory",
        )
    if len(set(occurrences)) != len(occurrences):
        raise ModelFailure(
            OutcomeClass.REFUSED,
            "subjects:fiat-shamir-admission",
            "FRI-IOR-SUBJECT-020",
            "the Core occurrence inventory contains duplicates",
        )
    context_ports = core_term.get("public_context_ports")
    if context_ports != _public_context_port_terms():
        raise ModelFailure(
            OutcomeClass.REFUSED,
            "subjects:fiat-shamir-admission",
            "FRI-IOR-SUBJECT-036",
            (
                "the Core does not expose the exact public Statement and "
                "ApplicationBinding context-port occurrences"
            ),
        )
    if any(port["occurrence"] not in occurrences for port in context_ports):
        raise ModelFailure(
            OutcomeClass.REFUSED,
            "subjects:fiat-shamir-admission",
            "FRI-IOR-SUBJECT-036",
            "a public Context occurrence is absent from the protection inventory",
        )
    plan_by_occurrence = {
        step.occurrence: (index, step)
        for index, step in enumerate(plan.steps)
    }
    if len(plan_by_occurrence) != len(plan.steps):
        raise ModelFailure(
            OutcomeClass.REFUSED,
            "subjects:fiat-shamir-admission",
            "FRI-IOR-SUBJECT-021",
            "the transcript plan contains duplicate occurrences",
        )

    # The Core owns the ordered vector, not the construction's byte seed.
    # Require the selected plan to expose the exact two-step resolution rather
    # than accepting `query-occurrences` merely because its text happens to
    # match a plan occurrence.
    if QUERY_OCCURRENCES in occurrences:
        seed_resolution = plan_by_occurrence.get(QUERY_SEED)
        vector_resolution = plan_by_occurrence.get(QUERY_OCCURRENCES)
        if (
            seed_resolution is None
            or vector_resolution is None
            or seed_resolution[1].kind != DERIVE_CHALLENGE
            or vector_resolution[1].kind != SAMPLE_OCCURRENCES
            or seed_resolution[0] >= vector_resolution[0]
            or QUERY_OCCURRENCES
            not in seed_resolution[1].protected_occurrences
        ):
            raise ModelFailure(
                OutcomeClass.REFUSED,
                "subjects:fiat-shamir-admission",
                "FRI-IOR-SUBJECT-035",
                (
                    "the transcript plan does not derive an internal query seed "
                    "and expand it into the Core-owned ordered query vector"
                ),
            )

    expected: list[PublicOccurrenceProtection] = []
    for occurrence in occurrences:
        if occurrence == "opening-table-and-occurrence-selectors":
            expected.append(
                PublicOccurrenceProtection(
                    occurrence,
                    None,
                    None,
                    (),
                    POST_FINAL_CHALLENGE_PUBLIC_RESPONSE,
                )
            )
            continue
        resolved = plan_by_occurrence.get(occurrence)
        if resolved is None:
            raise ModelFailure(
                OutcomeClass.REFUSED,
                "subjects:fiat-shamir-admission",
                "FRI-IOR-SUBJECT-022",
                "an acceptance-affecting Core occurrence has no transcript disposition",
            )
        position, step = resolved
        expected.append(
            PublicOccurrenceProtection(
                occurrence,
                step.occurrence,
                position,
                step.protected_occurrences,
                _plan_disposition(step.kind),
            )
        )
    return tuple(expected)


_ADMISSION_TOKEN = object()


@dataclass(frozen=True, slots=True, init=False)
class CheckedFiatShamirConstruction(_SemanticSubject):
    """Structurally admitted same-Core Fresh-to-Fiat--Shamir construction.

    The normal API creates instances through
    :func:`admit_fiat_shamir_construction`.  Its module-private token is a
    construction convention, not a security boundary.  Admission checks exact
    endpoint identities, public-coin source semantics, transcript-plan
    identity, and total occurrence protection.  It establishes none of the
    cryptographic properties listed in ``nonclaims``.
    """

    declaration_id: SemanticId
    core_id: SemanticId
    transcript_plan_id: SemanticId
    source_protocol_id: SemanticId
    target_protocol_id: SemanticId
    protection_map: tuple[PublicOccurrenceProtection, ...]

    SUBJECT_KIND: ClassVar[str] = "checked-fiat-shamir-construction"
    IDENTITY_DOMAIN: ClassVar[str] = (
        "fri-ior.construction.checked-fiat-shamir.v1"
    )

    def __init__(
        self,
        declaration_id: SemanticId,
        core_id: SemanticId,
        transcript_plan_id: SemanticId,
        source_protocol_id: SemanticId,
        target_protocol_id: SemanticId,
        protection_map: tuple[PublicOccurrenceProtection, ...],
        *,
        _token: object,
    ) -> None:
        if _token is not _ADMISSION_TOKEN:
            raise ModelFailure(
                OutcomeClass.MISSING_DEPENDENCY,
                "subjects:fiat-shamir-admission",
                "FRI-IOR-SUBJECT-023",
                "a checked construction requires the structural admission operation",
            )
        for value, where in (
            (declaration_id, "declaration_id"),
            (core_id, "core_id"),
            (transcript_plan_id, "transcript_plan_id"),
            (source_protocol_id, "source_protocol_id"),
            (target_protocol_id, "target_protocol_id"),
        ):
            if not isinstance(value, SemanticId):
                _raise_kind_mismatch(where, "SemanticId")
        if not isinstance(protection_map, tuple) or not all(
            isinstance(item, PublicOccurrenceProtection)
            for item in protection_map
        ):
            raise ModelFailure(
                OutcomeClass.MALFORMED,
                "subjects:fiat-shamir-admission",
                "FRI-IOR-SUBJECT-024",
                "a checked construction requires a typed protection map",
            )
        object.__setattr__(self, "declaration_id", declaration_id)
        object.__setattr__(self, "core_id", core_id)
        object.__setattr__(self, "transcript_plan_id", transcript_plan_id)
        object.__setattr__(self, "source_protocol_id", source_protocol_id)
        object.__setattr__(self, "target_protocol_id", target_protocol_id)
        object.__setattr__(self, "protection_map", protection_map)

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": ADMITTED_FIAT_SHAMIR_CONSTRUCTION_SCHEMA,
            "admission_law": "exact-public-coin-total-protection-map.v1",
            "declaration_id": _semantic_ref(self.declaration_id),
            "work_augmented_committed_core_id": _semantic_ref(self.core_id),
            "transcript_plan_id": _semantic_ref(self.transcript_plan_id),
            "fresh_protocol_id": _semantic_ref(self.source_protocol_id),
            "fiat_shamir_protocol_id": _semantic_ref(self.target_protocol_id),
            "public_occurrence_protection_map": [
                item.to_term() for item in self.protection_map
            ],
            "admission_scope": "structural-construction-only",
            "nonclaims": list(FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS),
        }


@dataclass(frozen=True, slots=True)
class FiatShamirConstructionAdmission:
    """Stable result plus the checked subject only on affirmation."""

    result: CheckResult
    checked_construction: CheckedFiatShamirConstruction | None

    def __post_init__(self) -> None:
        if not isinstance(self.result, CheckResult):
            raise TypeError("construction admission requires a CheckResult")
        if self.result.outcome is OutcomeClass.AFFIRMATIVE:
            if not isinstance(
                self.checked_construction,
                CheckedFiatShamirConstruction,
            ):
                raise TypeError("affirmative admission requires a checked construction")
        elif self.checked_construction is not None:
            raise TypeError("non-affirmative admission cannot carry a checked construction")


def admit_fiat_shamir_construction(
    declaration: object,
    protection_map: object,
) -> FiatShamirConstructionAdmission:
    """Check exact endpoints, public-coin premise, and total protection map."""

    boundary = "subjects:fiat-shamir-admission"
    try:
        if type(declaration) is not CheckedFiatShamirConstructionDeclaration:
            return FiatShamirConstructionAdmission(
                CheckResult(
                    OutcomeClass.KIND_MISMATCH,
                    boundary,
                    "FRI-IOR-SUBJECT-025",
                    "admission requires a Fiat--Shamir construction declaration",
                ),
                None,
            )
        if not isinstance(protection_map, tuple) or not all(
            type(item) is PublicOccurrenceProtection
            for item in protection_map
        ):
            return FiatShamirConstructionAdmission(
                CheckResult(
                    OutcomeClass.MALFORMED,
                    boundary,
                    "FRI-IOR-SUBJECT-026",
                    "admission requires a typed protection-map tuple",
                ),
                None,
            )

        source = declaration.source
        target = declaration.target
        source_core_term = source.core.to_term()
        target_core_term = target.core.to_term()
        source_core_id = semantic_id(
            WorkAugmentedCommittedFriCore.SUBJECT_KIND,
            WorkAugmentedCommittedFriCore.IDENTITY_DOMAIN,
            source_core_term,
        )
        target_core_id = semantic_id(
            WorkAugmentedCommittedFriCore.SUBJECT_KIND,
            WorkAugmentedCommittedFriCore.IDENTITY_DOMAIN,
            target_core_term,
        )
        if source_core_id != target_core_id:
            raise ModelFailure(
                OutcomeClass.KIND_MISMATCH,
                boundary,
                "FRI-IOR-SUBJECT-034",
                "Fiat--Shamir endpoints do not share one Core identity",
            )
        challenge_contract = source_core_term.get("challenge_contract")
        if (
            not isinstance(challenge_contract, dict)
            or challenge_contract.get("public_coin") is not True
        ):
            raise ModelFailure(
                OutcomeClass.REFUSED,
                boundary,
                "FRI-IOR-SUBJECT-027",
                "the source Core does not declare an exact public-coin contract",
            )

        plan = target.challenge_interpretation.construction_plan
        plan_id = transcript_plan_identity(plan)
        exact_plan_id = transcript_plan_identity(CANONICAL_CONSTRUCTION_PLAN)
        expected_map = _expected_protection_map(source_core_term, plan)
        candidate_occurrences = tuple(
            item.core_occurrence for item in protection_map
        )
        expected_occurrences = tuple(
            item.core_occurrence for item in expected_map
        )
        if (
            candidate_occurrences != expected_occurrences
            or len(set(candidate_occurrences)) != len(candidate_occurrences)
        ):
            raise ModelFailure(
                OutcomeClass.REFUSED,
                boundary,
                "FRI-IOR-SUBJECT-028",
                "the public-occurrence protection map is not exact and total",
            )
        if protection_map != expected_map:
            raise ModelFailure(
                OutcomeClass.REFUSED,
                boundary,
                "FRI-IOR-SUBJECT-029",
                "a public occurrence has the wrong transcript position or dependents",
            )

        if source_core_id != WORK_AUGMENTED_COMMITTED_FRI_CORE.identity:
            raise ModelFailure(
                OutcomeClass.UNSUPPORTED,
                boundary,
                "FRI-IOR-SUBJECT-030",
                "the construction names an unsupported augmented Core identity",
            )
        if plan_id != exact_plan_id:
            raise ModelFailure(
                OutcomeClass.UNSUPPORTED,
                boundary,
                "FRI-IOR-SUBJECT-031",
                "the construction names an unsupported transcript-plan identity",
            )
        source_protocol_id = semantic_id(
            FreshWorkAugmentedProtocol.SUBJECT_KIND,
            FreshWorkAugmentedProtocol.IDENTITY_DOMAIN,
            source.to_term(),
        )
        target_protocol_id = semantic_id(
            FiatShamirWorkAugmentedProtocol.SUBJECT_KIND,
            FiatShamirWorkAugmentedProtocol.IDENTITY_DOMAIN,
            target.to_term(),
        )
        if (
            source_protocol_id != FRESH_WORK_AUGMENTED_PROTOCOL.identity
            or target_protocol_id != FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity
        ):
            raise ModelFailure(
                OutcomeClass.UNSUPPORTED,
                boundary,
                "FRI-IOR-SUBJECT-032",
                "the construction names unsupported Fresh or Fiat--Shamir Protocol IDs",
            )

        declaration_id = semantic_id(
            CheckedFiatShamirConstructionDeclaration.SUBJECT_KIND,
            CheckedFiatShamirConstructionDeclaration.IDENTITY_DOMAIN,
            declaration.to_term(),
        )
        checked = CheckedFiatShamirConstruction(
            declaration_id,
            source_core_id,
            plan_id,
            source_protocol_id,
            target_protocol_id,
            protection_map,
            _token=_ADMISSION_TOKEN,
        )
        return FiatShamirConstructionAdmission(
            affirmative(
                boundary,
                "FRI-IOR-SUBJECT-101",
                "the exact same-Core public-coin Fiat--Shamir construction is structurally admitted",
                subject=checked.identity,
                core_id=source_core_id,
                transcript_plan_id=plan_id,
                source_protocol_id=source_protocol_id,
                target_protocol_id=target_protocol_id,
                mapped_public_occurrences=len(protection_map),
            ),
            checked,
        )
    except ModelFailure as error:
        return FiatShamirConstructionAdmission(error.to_result(), None)


NATIVE_FRI_CORE = NativeFriCore()
COMMITTED_FRI_CORE = CommittedFriCore()
WORK_AUGMENTED_COMMITTED_FRI_CORE = WorkAugmentedCommittedFriCore(
    COMMITTED_FRI_CORE
)
FRESH_CHALLENGE_INTERPRETATION = FreshChallengeInterpretation(
    WORK_AUGMENTED_COMMITTED_FRI_CORE
)
FIAT_SHAMIR_CHALLENGE_INTERPRETATION = FiatShamirChallengeInterpretation(
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
    CANONICAL_CONSTRUCTION_PLAN,
)
FRESH_WORK_AUGMENTED_PROTOCOL = FreshWorkAugmentedProtocol(
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
    FRESH_CHALLENGE_INTERPRETATION,
)
FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL = FiatShamirWorkAugmentedProtocol(
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
    FIAT_SHAMIR_CHALLENGE_INTERPRETATION,
)
COMMITMENT_COMPILATION_DECLARATION = CheckedCommitmentCompilationDeclaration(
    NATIVE_FRI_CORE,
    COMMITTED_FRI_CORE,
)
GRINDING_AUGMENTATION_DECLARATION = CheckedGrindingAugmentationDeclaration(
    COMMITTED_FRI_CORE,
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
)
FIAT_SHAMIR_CONSTRUCTION_DECLARATION = CheckedFiatShamirConstructionDeclaration(
    FRESH_WORK_AUGMENTED_PROTOCOL,
    FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
)
CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP = _expected_protection_map(
    WORK_AUGMENTED_COMMITTED_FRI_CORE.to_term(),
    CANONICAL_CONSTRUCTION_PLAN,
)
_CANONICAL_FIAT_SHAMIR_ADMISSION = admit_fiat_shamir_construction(
    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
    CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP,
)
if _CANONICAL_FIAT_SHAMIR_ADMISSION.checked_construction is None:
    raise RuntimeError("canonical Fiat--Shamir construction failed admission")
CHECKED_FIAT_SHAMIR_CONSTRUCTION = (
    _CANONICAL_FIAT_SHAMIR_ADMISSION.checked_construction
)

_SELECTED_SUBJECT_TYPES = (
    NativeFriCore,
    CommittedFriCore,
    WorkAugmentedCommittedFriCore,
    FreshChallengeInterpretation,
    FiatShamirChallengeInterpretation,
    FreshWorkAugmentedProtocol,
    FiatShamirWorkAugmentedProtocol,
    CheckedCommitmentCompilationDeclaration,
    CheckedGrindingAugmentationDeclaration,
    CheckedFiatShamirConstructionDeclaration,
    CheckedFiatShamirConstruction,
)


def admit_selected_subject(candidate: object) -> CheckResult:
    """Admit one formed selected semantic subject, never an ID-shaped proxy."""

    if isinstance(candidate, SemanticId):
        return CheckResult(
            OutcomeClass.KIND_MISMATCH,
            "subjects:admission",
            "FRI-IOR-SUBJECT-007",
            "subject admission requires a declaration, not a SemanticId proxy",
        )
    if not isinstance(candidate, _SELECTED_SUBJECT_TYPES):
        return CheckResult(
            OutcomeClass.MALFORMED,
            "subjects:admission",
            "FRI-IOR-SUBJECT-008",
            "subject admission requires a selected semantic declaration",
        )
    try:
        identity = candidate.identity
        return affirmative(
            "subjects:admission",
            "FRI-IOR-SUBJECT-100",
            "the selected semantic subject is formed",
            subject=identity,
            schema=candidate.to_term()["schema"],
        )
    except ModelFailure as error:
        return error.to_result()


__all__ = [
    "ADMITTED_FIAT_SHAMIR_CONSTRUCTION_SCHEMA",
    "CANONICAL_PUBLIC_OCCURRENCE_PROTECTION_MAP",
    "CHALLENGE_INTERPRETATION_SCHEMA",
    "COMMITTED_CORE_NONCLAIMS",
    "COMMITTED_FRI_CORE",
    "COMMITMENT_COMPILATION_CAPABILITIES",
    "COMMITMENT_COMPILATION_DECLARATION",
    "COMMITMENT_COMPILATION_NONCLAIMS",
    "COMMITMENT_COMPILATION_REQUIREMENTS",
    "CheckedCommitmentCompilationDeclaration",
    "CheckedFiatShamirConstruction",
    "CheckedFiatShamirConstructionDeclaration",
    "CheckedGrindingAugmentationDeclaration",
    "CommittedFriCore",
    "DECLARATION_STATUS",
    "FIAT_SHAMIR_CHALLENGE_INTERPRETATION",
    "FIAT_SHAMIR_CONSTRUCTION_CAPABILITIES",
    "CHECKED_FIAT_SHAMIR_CONSTRUCTION",
    "FIAT_SHAMIR_CONSTRUCTION_DECLARATION",
    "FIAT_SHAMIR_CONSTRUCTION_NONCLAIMS",
    "FIAT_SHAMIR_CONSTRUCTION_REQUIREMENTS",
    "FIAT_SHAMIR_INTERPRETATION_NONCLAIMS",
    "FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL",
    "FRESH_CHALLENGE_INTERPRETATION",
    "FRESH_INTERPRETATION_NONCLAIMS",
    "FRESH_WORK_AUGMENTED_PROTOCOL",
    "FiatShamirChallengeInterpretation",
    "FiatShamirConstructionAdmission",
    "FiatShamirWorkAugmentedProtocol",
    "FreshChallengeInterpretation",
    "FreshWorkAugmentedProtocol",
    "GRINDING_AUGMENTATION_CAPABILITIES",
    "GRINDING_AUGMENTATION_DECLARATION",
    "GRINDING_AUGMENTATION_NONCLAIMS",
    "GRINDING_AUGMENTATION_REQUIREMENTS",
    "NATIVE_CORE_NONCLAIMS",
    "NATIVE_FRI_CORE",
    "NativeFriCore",
    "POST_FINAL_CHALLENGE_PUBLIC_RESPONSE",
    "PROTOCOL_NONCLAIMS",
    "WORK_AUGMENTED_COMMITTED_FRI_CORE",
    "WORK_AUGMENTED_CORE_NONCLAIMS",
    "WorkAugmentedCommittedFriCore",
    "PublicOccurrenceProtection",
    "admit_fiat_shamir_construction",
    "admit_selected_subject",
    "transcript_plan_identity",
]
