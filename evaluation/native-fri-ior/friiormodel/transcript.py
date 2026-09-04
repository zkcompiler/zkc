"""Exact typed SHA-256 Fiat--Shamir transcript for the finite FRI witness.

The construction represented here belongs to the *committed* FRI protocol.
It does not claim that native FRI contains a random oracle or a grinding
round.  In particular, grinding has an explicit Core-visible ``work_seed``
challenge: Fiat--Shamir derives that challenge from the protected transcript,
the prover then publishes a nonce, and the verifier checks the pair before it
derives the separate query randomness.

All transcript payloads are injectively framed by namespace and codec.  The
fold challenges use bounded big-endian rejection sampling into ``F_97^2``.
The sixteen-element query domain instead admits exact one-draw power-of-two
sampling from a big-endian ``u16``; it has no rejection-exhaustion branch.
Mapping opposite points onto one authenticated pair is a later
commitment-compilation operation, not transcript sampling.  The four query
occurrences retain their ordinals, so equal-valued draws are not silently
deduplicated.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import Any

from .commitment import DIGEST_BYTES, EXACT_COMMITMENT_PROFILE, MerkleCap
from .field import MODULUS, Fp, Fp2, canonical_polynomial
from .profile import (
    D0,
    DEFAULT_VALIDATION_LIMITS,
    EXACT_ALGEBRA_PROFILE,
    EXACT_PROFILE,
    SemanticLaw,
)
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    SemanticId,
    affirmative,
    checker_failure,
    encode_term,
    malformed,
    refused,
    semantic_id,
    unsupported,
)


MODEL = "FriIorTypedSha256FiatShamir.v1"
HASH_SUITE = "sha256.v1"
FRAMING = "typed-length-delimited-big-endian.v1"
GRINDING_PROFILE_NAME = "zkc.fri-ior.sha256-leading-zero-work.v1"

STATEMENT = "statement"
APPLICATION_CONTEXT = "application-context"
CAP0 = "cap[0]"
BETA0 = "fold-challenge[0]"
CAP1 = "cap[1]"
BETA1 = "fold-challenge[1]"
TERMINAL = "terminal-polynomial"
WORK_SEED = "work-seed"
GRINDING_NONCE = "grinding-nonce"
WORK_CHECK = "work-check"
QUERY_SEED = "query-seed"
QUERY_OCCURRENCES = "query-occurrences"

ABSORB_PUBLICATION = "AbsorbPublication"
DERIVE_CHALLENGE = "DeriveChallenge"
CHECK_WORK = "CheckWork"
SAMPLE_OCCURRENCES = "SampleOccurrences"

CLOSED_TERM_CODEC = "closed-finite-term.v1"
CAP_CODEC = "sha256-two-node-cap.v1"
FP2_CODEC = "fp97-extension2-u8-pair.v1"
TERMINAL_CODEC = "ascending-fp2-coefficients.v1"
SEED_CODEC = "bytes32.v1"
NONCE_CODEC = "u32be.v1"
QUERY_INDEX_CODEC = "u16be-low-bits-initial-domain-index.v1"

FP2_SAMPLER = "sha256-u16be-rejection-fp97-extension2.v1"
SEED_SAMPLER = "sha256-bytes32.v1"
QUERY_SAMPLER = "sha256-u16be-low-bits-power-of-two-range.v1"
WORK_RULE = "sha256-leading-zero-bits.v1"

STATEMENT_NAMESPACE = "zkc/fri-ior/statement/v1"
APPLICATION_CONTEXT_NAMESPACE = "zkc/fri-ior/application-context/v1"
CAP0_NAMESPACE = "zkc/fri-ior/cap/0/v1"
BETA0_NAMESPACE = "zkc/fri-ior/fold-challenge/0/v1"
CAP1_NAMESPACE = "zkc/fri-ior/cap/1/v1"
BETA1_NAMESPACE = "zkc/fri-ior/fold-challenge/1/v1"
TERMINAL_NAMESPACE = "zkc/fri-ior/terminal-polynomial/v1"
WORK_SEED_NAMESPACE = "zkc/fri-ior/work-seed/v1"
GRINDING_NONCE_NAMESPACE = "zkc/fri-ior/grinding-nonce/v1"
WORK_CHECK_NAMESPACE = "zkc/fri-ior/work-check/v1"
QUERY_SEED_NAMESPACE = "zkc/fri-ior/query-seed/v1"
QUERY_OCCURRENCES_NAMESPACE = "zkc/fri-ior/query-occurrences/v1"

GRINDING_BITS = 2
GRINDING_NONCE_BYTES = 4
QUERY_DOMAIN_SIZE = D0.order

_GENESIS_DOMAIN = b"zkc.fri-ior.transcript-genesis.v1\x00"
_ABSORB_DOMAIN = b"zkc.fri-ior.transcript-absorb.v1\x00"
_SQUEEZE_DOMAIN = b"zkc.fri-ior.transcript-squeeze.v1\x00"
_QUERY_EXPAND_DOMAIN = b"zkc.fri-ior.query-expand.v1\x00"
_WORK_DOMAIN = b"zkc.fri-ior.work-check.v1\x00"


TRANSCRIPT_HASH_STATE_LAW = SemanticLaw(
    name="sha256-typed-transcript-state",
    version=1,
    parameters=(
        ("hash", HASH_SUITE),
        ("genesis-domain-hex", _GENESIS_DOMAIN.hex()),
        ("absorb-domain-hex", _ABSORB_DOMAIN.hex()),
        ("squeeze-domain-hex", _SQUEEZE_DOMAIN.hex()),
        ("digest-bytes", DIGEST_BYTES),
    ),
    clauses=(
        "genesis-hashes-the-selected-model-and-semantic-dependency-identities",
        "absorb-hashes-domain-then-prior-state-then-one-typed-frame",
        "squeeze-hashes-domain-then-prior-state-then-one-typed-attempt-frame",
        "every-successful-squeeze-digest-becomes-the-next-transcript-state",
    ),
)

TRANSCRIPT_FRAMING_LAW = SemanticLaw(
    name="typed-length-delimited-transcript-framing",
    version=1,
    parameters=(
        ("framing", FRAMING),
        ("byte-order", "big-endian"),
        ("namespace-length-bytes", 2),
        ("codec-length-bytes", 2),
        ("payload-length-bytes", 4),
        ("namespace-and-codec-alphabet", "ascii"),
    ),
    clauses=(
        "frame-is-namespace-length-namespace-codec-length-codec-payload-length-payload",
        "namespace-and-codec-must-be-nonempty",
        "lengths-must-fit-their-fixed-width-unsigned-encodings",
    ),
)

TRANSCRIPT_CODEC_LAW = SemanticLaw(
    name="fri-publication-and-challenge-codecs",
    version=1,
    parameters=(
        ("closed-term", CLOSED_TERM_CODEC),
        ("cap", CAP_CODEC),
        ("fp2", FP2_CODEC),
        ("terminal", TERMINAL_CODEC),
        ("seed", SEED_CODEC),
        ("nonce", NONCE_CODEC),
        ("query-index", QUERY_INDEX_CODEC),
    ),
    clauses=(
        "closed-values-use-the-canonical-closed-finite-term-codec",
        "caps-use-the-selected-commitment-profile-term",
        "fp2-values-encode-real-byte-then-imaginary-byte",
        "terminal-coefficients-encode-in-ascending-degree-order",
        "seeds-are-exactly-one-sha256-digest",
        "nonces-use-the-selected-grinding-profile-width",
        "query-ordinals-use-u16-big-endian",
    ),
)

FP2_REJECTION_SAMPLER_LAW = SemanticLaw(
    name="sha256-u16be-rejection-fp97-extension2",
    version=1,
    parameters=(
        ("sampler", FP2_SAMPLER),
        ("candidate-bytes", 2),
        ("byte-order", "big-endian"),
        ("field-cardinality", MODULUS * MODULUS),
        ("attempt-codec", "u16be"),
    ),
    clauses=(
        "each-attempt-squeezes-under-the-challenge-namespace",
        "candidates-at-or-above-the-largest-multiple-of-field-cardinality-are-rejected",
        "accepted-residue-quotient-is-real-and-remainder-is-imaginary",
        "attempt-budget-is-validation-resource-state-not-semantic-plan-state",
    ),
)

SEED_DERIVATION_LAW = SemanticLaw(
    name="sha256-bytes32-seed-derivation",
    version=1,
    parameters=(
        ("sampler", SEED_SAMPLER),
        ("attempt", 0),
        ("seed-bytes", DIGEST_BYTES),
    ),
    clauses=(
        "seed-is-the-single-squeeze-digest-at-attempt-zero",
        "the-selected-namespace-distinguishes-work-and-query-seeds",
    ),
)

QUERY_SEED_EXPANSION_LAW = SemanticLaw(
    name="sha256-seed-to-ordered-query-vector",
    version=1,
    parameters=(
        ("sampler", QUERY_SAMPLER),
        ("expansion-domain-hex", _QUERY_EXPAND_DOMAIN.hex()),
        ("query-domain-size", QUERY_DOMAIN_SIZE),
        ("query-count", EXACT_ALGEBRA_PROFILE.ordered_query_count),
        ("ordinal-codec", "u16be"),
        ("candidate-bytes", 2),
    ),
    clauses=(
        "each-vector-ordinal-is-expanded-by-a-separate-domain-separated-hash",
        "the-low-bits-select-an-index-because-the-domain-size-is-a-power-of-two",
        "vector-order-and-multiplicity-are-preserved",
        "query-seed-is-construction-internal-and-not-a-core-challenge",
    ),
)

EXACT_TRANSCRIPT_LAWS = (
    TRANSCRIPT_HASH_STATE_LAW,
    TRANSCRIPT_FRAMING_LAW,
    TRANSCRIPT_CODEC_LAW,
    FP2_REJECTION_SAMPLER_LAW,
    SEED_DERIVATION_LAW,
    QUERY_SEED_EXPANSION_LAW,
)

WORK_PREDICATE_LAW = SemanticLaw(
    name="sha256-leading-zero-work-predicate",
    version=1,
    parameters=(
        ("hash", HASH_SUITE),
        ("work-domain-hex", _WORK_DOMAIN.hex()),
        ("namespace", WORK_CHECK_NAMESPACE),
        ("codec", WORK_RULE),
        ("nonce-bytes", GRINDING_NONCE_BYTES),
        ("difficulty-leading-zero-bits", GRINDING_BITS),
    ),
    clauses=(
        "work-payload-is-work-seed-followed-by-big-endian-nonce",
        "work-digest-hashes-domain-then-one-typed-work-frame",
        "work-accepts-exactly-when-the-leading-difficulty-bits-are-zero",
    ),
)


@dataclass(frozen=True, slots=True)
class GrindingProfile:
    """The immutable semantic owner of the inserted work predicate."""

    name: str
    hash_suite: str
    nonce_bytes: int
    difficulty_bits: int
    work_law_id: SemanticId

    def __post_init__(self) -> None:
        if (
            not isinstance(self.name, str)
            or not self.name
            or not isinstance(self.hash_suite, str)
            or not self.hash_suite
            or type(self.nonce_bytes) is not int
            or not 1 <= self.nonce_bytes <= 8
            or type(self.difficulty_bits) is not int
            or not 1 <= self.difficulty_bits <= 8 * DIGEST_BYTES
            or not isinstance(self.work_law_id, SemanticId)
            or self.work_law_id.subject_kind != "fri-ior-semantic-law"
        ):
            raise malformed(
                "transcript:grinding-profile-formation",
                "FRI-IOR-TRANSCRIPT-048",
                "a grinding profile requires exact bounded semantics and one typed work law",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "hash_suite": self.hash_suite,
            "nonce_bytes": self.nonce_bytes,
            "difficulty_leading_zero_bits": self.difficulty_bits,
            "work_law_id": self.work_law_id.to_term(),
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "fri-grinding-profile",
            "fri-ior.grinding-profile.v1",
            self.to_term(),
        )


EXACT_GRINDING_PROFILE = GrindingProfile(
    name=GRINDING_PROFILE_NAME,
    hash_suite=HASH_SUITE,
    nonce_bytes=GRINDING_NONCE_BYTES,
    difficulty_bits=GRINDING_BITS,
    work_law_id=WORK_PREDICATE_LAW.identity,
)

MAX_GRINDING_NONCE = (1 << (8 * EXACT_GRINDING_PROFILE.nonce_bytes)) - 1


def _require_nonempty_text(value: Any, boundary: str, field: str) -> None:
    if not isinstance(value, str) or not value:
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-002",
            f"{field} must be non-empty text",
        )


@dataclass(frozen=True, slots=True)
class TranscriptPlanStep:
    """One typed source, challenge, check, or local sampling step."""

    kind: str
    occurrence: str
    namespace: str
    codec: str
    sampler: str | None
    feeds_transcript_state: bool
    protected_occurrences: tuple[str, ...]

    def __post_init__(self) -> None:
        boundary = "transcript:plan-formation"
        for field_name in ("kind", "occurrence", "namespace", "codec"):
            _require_nonempty_text(getattr(self, field_name), boundary, field_name)
        if self.sampler is not None:
            _require_nonempty_text(self.sampler, boundary, "sampler")
        if type(self.feeds_transcript_state) is not bool:
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-002",
                "feeds_transcript_state must be a boolean",
            )
        if not isinstance(self.protected_occurrences, tuple) or not all(
            isinstance(item, str) and item for item in self.protected_occurrences
        ):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-002",
                "protected occurrences must be a canonical text sequence",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "occurrence": self.occurrence,
            "namespace": self.namespace,
            "codec": self.codec,
            "sampler": self.sampler,
            "feeds_transcript_state": self.feeds_transcript_state,
            "protected_occurrences": list(self.protected_occurrences),
        }


@dataclass(frozen=True, slots=True)
class TranscriptConstructionPlan:
    """The fixed transcript-profile plan, below Core-level FS admission."""

    model: str
    algebra_profile_id: SemanticId
    commitment_profile_id: SemanticId
    grinding_profile_id: SemanticId
    semantic_law_ids: tuple[SemanticId, ...]
    query_domain_size: int
    query_count: int
    steps: tuple[TranscriptPlanStep, ...]

    def __post_init__(self) -> None:
        boundary = "transcript:plan-formation"
        _require_nonempty_text(self.model, boundary, "model")
        expected_kinds = (
            (self.algebra_profile_id, "fri-algebra-profile"),
            (self.commitment_profile_id, "fri-commitment-profile"),
            (self.grinding_profile_id, "fri-grinding-profile"),
        )
        if any(
            not isinstance(identity, SemanticId)
            or identity.subject_kind != expected_kind
            for identity, expected_kind in expected_kinds
        ):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-002",
                "a transcript plan requires typed algebra, commitment, and grinding identities",
            )
        if (
            type(self.semantic_law_ids) is not tuple
            or not self.semantic_law_ids
            or any(
                not isinstance(identity, SemanticId)
                or identity.subject_kind != "fri-ior-semantic-law"
                for identity in self.semantic_law_ids
            )
            or len(set(self.semantic_law_ids)) != len(self.semantic_law_ids)
        ):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-002",
                "a transcript plan requires one canonical unique semantic-law ID sequence",
            )
        for field_name in ("query_domain_size", "query_count"):
            value = getattr(self, field_name)
            if type(value) is not int or value <= 0:
                raise malformed(
                    boundary,
                    "FRI-IOR-TRANSCRIPT-002",
                    f"{field_name} must be a positive integer",
                )
        if not isinstance(self.steps, tuple) or not all(
            isinstance(step, TranscriptPlanStep) for step in self.steps
        ):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-002",
                "plan steps must be a canonical TranscriptPlanStep sequence",
            )

    def to_term(self) -> dict[str, Any]:
        """Return exactly the semantic preimage; request limits are absent."""

        return {
            "model": self.model,
            "algebra_profile_id": self.algebra_profile_id.to_term(),
            "commitment_profile_id": self.commitment_profile_id.to_term(),
            "grinding_profile_id": self.grinding_profile_id.to_term(),
            "semantic_law_ids": [
                identity.to_term() for identity in self.semantic_law_ids
            ],
            "query_domain_size": self.query_domain_size,
            "query_count": self.query_count,
            "steps": [step.to_term() for step in self.steps],
        }

    @property
    def identity(self) -> SemanticId:
        return semantic_id(
            "transcript-construction-plan",
            "fri-ior.transcript-construction-plan.v1",
            self.to_term(),
        )


def _step(
    kind: str,
    occurrence: str,
    namespace: str,
    codec: str,
    sampler: str | None,
    feeds_transcript_state: bool,
    *protected_occurrences: str,
) -> TranscriptPlanStep:
    return TranscriptPlanStep(
        kind,
        occurrence,
        namespace,
        codec,
        sampler,
        feeds_transcript_state,
        protected_occurrences,
    )


CANONICAL_CONSTRUCTION_PLAN = TranscriptConstructionPlan(
    model=MODEL,
    algebra_profile_id=EXACT_ALGEBRA_PROFILE.identity,
    commitment_profile_id=EXACT_COMMITMENT_PROFILE.identity,
    grinding_profile_id=EXACT_GRINDING_PROFILE.identity,
    semantic_law_ids=tuple(law.identity for law in EXACT_TRANSCRIPT_LAWS),
    query_domain_size=QUERY_DOMAIN_SIZE,
    query_count=EXACT_ALGEBRA_PROFILE.ordered_query_count,
    steps=(
        _step(
            ABSORB_PUBLICATION,
            STATEMENT,
            STATEMENT_NAMESPACE,
            CLOSED_TERM_CODEC,
            None,
            True,
            BETA0,
            BETA1,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            ABSORB_PUBLICATION,
            APPLICATION_CONTEXT,
            APPLICATION_CONTEXT_NAMESPACE,
            CLOSED_TERM_CODEC,
            None,
            True,
            BETA0,
            BETA1,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            ABSORB_PUBLICATION,
            CAP0,
            CAP0_NAMESPACE,
            CAP_CODEC,
            None,
            True,
            BETA0,
            BETA1,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            DERIVE_CHALLENGE,
            BETA0,
            BETA0_NAMESPACE,
            FP2_CODEC,
            FP2_SAMPLER,
            True,
            BETA1,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            ABSORB_PUBLICATION,
            CAP1,
            CAP1_NAMESPACE,
            CAP_CODEC,
            None,
            True,
            BETA1,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            DERIVE_CHALLENGE,
            BETA1,
            BETA1_NAMESPACE,
            FP2_CODEC,
            FP2_SAMPLER,
            True,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            ABSORB_PUBLICATION,
            TERMINAL,
            TERMINAL_NAMESPACE,
            TERMINAL_CODEC,
            None,
            True,
            WORK_SEED,
            QUERY_SEED,
        ),
        _step(
            DERIVE_CHALLENGE,
            WORK_SEED,
            WORK_SEED_NAMESPACE,
            SEED_CODEC,
            SEED_SAMPLER,
            True,
            WORK_CHECK,
            QUERY_SEED,
        ),
        _step(
            ABSORB_PUBLICATION,
            GRINDING_NONCE,
            GRINDING_NONCE_NAMESPACE,
            NONCE_CODEC,
            None,
            True,
            WORK_CHECK,
            QUERY_SEED,
        ),
        _step(
            CHECK_WORK,
            WORK_CHECK,
            WORK_CHECK_NAMESPACE,
            SEED_CODEC,
            WORK_RULE,
            False,
            QUERY_SEED,
        ),
        _step(
            DERIVE_CHALLENGE,
            QUERY_SEED,
            QUERY_SEED_NAMESPACE,
            SEED_CODEC,
            SEED_SAMPLER,
            True,
            QUERY_OCCURRENCES,
        ),
        _step(
            SAMPLE_OCCURRENCES,
            QUERY_OCCURRENCES,
            QUERY_OCCURRENCES_NAMESPACE,
            QUERY_INDEX_CODEC,
            QUERY_SAMPLER,
            False,
        ),
    ),
)


def _first_plan_difference(
    candidate: TranscriptConstructionPlan,
) -> CheckResult | None:
    boundary = "transcript:plan-admission"
    expected = CANONICAL_CONSTRUCTION_PLAN
    scalar_fields = (
        "model",
        "algebra_profile_id",
        "commitment_profile_id",
        "grinding_profile_id",
        "semantic_law_ids",
        "query_domain_size",
        "query_count",
    )
    if any(
        getattr(candidate, field) != getattr(expected, field) for field in scalar_fields
    ):
        return unsupported(
            boundary,
            "FRI-IOR-TRANSCRIPT-019",
            "the plan selects different semantic dependencies or query-vector shape",
        )

    expected_by_occurrence = {step.occurrence: step for step in expected.steps}
    candidate_occurrences = tuple(step.occurrence for step in candidate.steps)
    if len(set(candidate_occurrences)) != len(candidate_occurrences) or set(
        candidate_occurrences
    ) != set(expected_by_occurrence):
        return refused(
            boundary,
            "FRI-IOR-TRANSCRIPT-010",
            "the plan omits, duplicates, or adds a required transcript occurrence",
        )

    positions = {
        occurrence: candidate_occurrences.index(occurrence)
        for occurrence in expected_by_occurrence
    }
    if positions[QUERY_SEED] < positions[TERMINAL]:
        return refused(
            boundary,
            "FRI-IOR-TRANSCRIPT-017",
            "query randomness is derived before terminal material",
        )
    if (
        positions[GRINDING_NONCE] > positions[QUERY_SEED]
        or positions[WORK_CHECK] > positions[QUERY_SEED]
    ):
        return refused(
            boundary,
            "FRI-IOR-TRANSCRIPT-018",
            "grinding publication or verification follows query randomness",
        )
    if candidate_occurrences != tuple(step.occurrence for step in expected.steps):
        return refused(
            boundary,
            "FRI-IOR-TRANSCRIPT-011",
            "the transcript occurrences are not in the required order",
        )

    for candidate_step, expected_step in zip(candidate.steps, expected.steps):
        if candidate_step.kind != expected_step.kind:
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-011",
                "a transcript occurrence has the wrong semantic kind",
            )
        if candidate_step.namespace != expected_step.namespace:
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-013",
                "a transcript occurrence has the wrong namespace",
            )
        if candidate_step.codec != expected_step.codec:
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-014",
                "a transcript occurrence has the wrong codec",
            )
        if candidate_step.sampler != expected_step.sampler:
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-015",
                "a challenge, work check, or query draw has the wrong sampler rule",
            )
        if (
            expected_step.kind == ABSORB_PUBLICATION
            and not candidate_step.feeds_transcript_state
        ):
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-016",
                "a published message is excluded from transcript influence",
            )
        if (
            candidate_step.feeds_transcript_state
            != expected_step.feeds_transcript_state
            or candidate_step.protected_occurrences
            != expected_step.protected_occurrences
        ):
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-012",
                "a statement, message, or derived coin lacks its required protection reach",
            )
    return None


def admit_construction_plan(candidate: object) -> CheckResult:
    """Admit the exact transcript profile and plan, not FS eligibility.

    This checker does not inspect a Core, establish public-coin structure, or
    prove that an occurrence map is total.  Those are obligations of the
    separate checked Fiat--Shamir construction that consumes this plan.
    """

    boundary = "transcript:plan-admission"
    if not isinstance(candidate, TranscriptConstructionPlan):
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-TRANSCRIPT-001",
            "construction-plan admission requires a TranscriptConstructionPlan value",
        )
    try:
        difference = _first_plan_difference(candidate)
        if difference is not None:
            return difference
        return affirmative(
            boundary,
            "FRI-IOR-TRANSCRIPT-100",
            "the exact typed transcript profile and plan are admitted",
            subject=candidate.identity,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected construction-plan checker failure: {type(error).__name__}",
        )


@dataclass(frozen=True, slots=True)
class QueryOccurrence:
    """One ordered logical draw; equal positions remain distinct occurrences."""

    ordinal: int
    initial_domain_index: int

    def __post_init__(self) -> None:
        if type(self.ordinal) is not int or self.ordinal < 0:
            raise malformed(
                "transcript:query-formation",
                "FRI-IOR-TRANSCRIPT-020",
                "a query ordinal must be a non-negative integer",
            )
        if type(self.initial_domain_index) is not int or not (
            0 <= self.initial_domain_index < QUERY_DOMAIN_SIZE
        ):
            raise malformed(
                "transcript:query-formation",
                "FRI-IOR-TRANSCRIPT-021",
                "a query index lies outside the exact initial evaluation domain",
            )

    def to_term(self) -> dict[str, int]:
        return {
            "ordinal": self.ordinal,
            "initial_domain_index": self.initial_domain_index,
        }


def _validate_phase_prefix(
    plan: object,
    transcript_state: object,
    *fold_challenges: object,
) -> None:
    if not isinstance(plan, TranscriptConstructionPlan):
        raise malformed(
            "transcript:phase-formation",
            "FRI-IOR-TRANSCRIPT-038",
            "a transcript phase requires a TranscriptConstructionPlan",
        )
    if not isinstance(transcript_state, bytes) or len(transcript_state) != DIGEST_BYTES:
        raise malformed(
            "transcript:phase-formation",
            "FRI-IOR-TRANSCRIPT-039",
            "a transcript phase state must be one SHA-256 digest",
        )
    if not all(isinstance(challenge, Fp2) for challenge in fold_challenges):
        raise malformed(
            "transcript:phase-formation",
            "FRI-IOR-TRANSCRIPT-040",
            "every fold challenge in a transcript phase must be an Fp2 value",
        )


@dataclass(frozen=True, slots=True)
class _FirstRoundTranscript:
    plan: TranscriptConstructionPlan
    transcript_state: bytes
    beta0: Fp2

    def __post_init__(self) -> None:
        _validate_phase_prefix(self.plan, self.transcript_state, self.beta0)


@dataclass(frozen=True, slots=True)
class _SecondRoundTranscript:
    plan: TranscriptConstructionPlan
    transcript_state: bytes
    beta0: Fp2
    beta1: Fp2

    def __post_init__(self) -> None:
        _validate_phase_prefix(
            self.plan,
            self.transcript_state,
            self.beta0,
            self.beta1,
        )


@dataclass(frozen=True, slots=True)
class _WorkSeedTranscript:
    plan: TranscriptConstructionPlan
    transcript_state: bytes
    beta0: Fp2
    beta1: Fp2
    terminal_coefficients: tuple[Fp2, ...]
    work_seed: bytes

    def __post_init__(self) -> None:
        _validate_phase_prefix(
            self.plan,
            self.transcript_state,
            self.beta0,
            self.beta1,
        )
        canonical_polynomial(
            self.terminal_coefficients,
            EXACT_PROFILE.terminal_max_coefficient_count,
        )
        if not isinstance(self.work_seed, bytes) or len(self.work_seed) != DIGEST_BYTES:
            raise malformed(
                "transcript:phase-formation",
                "FRI-IOR-TRANSCRIPT-041",
                "a work-seed phase requires one 32-byte work challenge",
            )
        if self.transcript_state != self.work_seed:
            raise malformed(
                "transcript:phase-formation",
                "FRI-IOR-TRANSCRIPT-042",
                "the post-squeeze transcript state must equal the work challenge digest",
            )


@dataclass(frozen=True, slots=True)
class FiatShamirTranscript:
    plan: TranscriptConstructionPlan
    transcript_state: bytes
    beta0: Fp2
    beta1: Fp2
    terminal_coefficients: tuple[Fp2, ...]
    work_seed: bytes
    grinding_nonce: int
    work_digest: bytes
    query_seed: bytes
    query_occurrences: tuple[QueryOccurrence, ...]

    def __post_init__(self) -> None:
        _validate_phase_prefix(
            self.plan,
            self.transcript_state,
            self.beta0,
            self.beta1,
        )
        canonical_polynomial(
            self.terminal_coefficients,
            EXACT_PROFILE.terminal_max_coefficient_count,
        )
        for value in (self.work_seed, self.work_digest, self.query_seed):
            if not isinstance(value, bytes) or len(value) != DIGEST_BYTES:
                raise malformed(
                    "transcript:phase-formation",
                    "FRI-IOR-TRANSCRIPT-043",
                    "work and query challenge material must contain 32 bytes",
                )
        if self.transcript_state != self.query_seed:
            raise malformed(
                "transcript:phase-formation",
                "FRI-IOR-TRANSCRIPT-044",
                "the final transcript state must equal the query challenge digest",
            )
        if type(self.grinding_nonce) is not int or not (
            0 <= self.grinding_nonce <= MAX_GRINDING_NONCE
        ):
            raise malformed(
                "transcript:phase-formation",
                "FRI-IOR-TRANSCRIPT-045",
                "a completed transcript requires an unsigned 32-bit nonce",
            )
        if self.work_digest[0] >> (8 - EXACT_GRINDING_PROFILE.difficulty_bits) != 0:
            raise malformed(
                "transcript:phase-formation",
                "FRI-IOR-TRANSCRIPT-046",
                "a completed transcript carries a failing work digest",
            )
        if (
            not isinstance(self.query_occurrences, tuple)
            or len(self.query_occurrences) != EXACT_PROFILE.ordered_query_count
            or not all(
                isinstance(occurrence, QueryOccurrence)
                for occurrence in self.query_occurrences
            )
            or tuple(occurrence.ordinal for occurrence in self.query_occurrences)
            != tuple(range(EXACT_PROFILE.ordered_query_count))
        ):
            raise malformed(
                "transcript:phase-formation",
                "FRI-IOR-TRANSCRIPT-047",
                "query occurrences must be the exact ordered four-occurrence sequence",
            )


def _counter_or_default(resources: ResourceCounter | None) -> ResourceCounter:
    if resources is None:
        return ResourceCounter(DEFAULT_VALIDATION_LIMITS)
    if not isinstance(resources, ResourceCounter):
        raise malformed(
            "transcript:resources",
            "FRI-IOR-TRANSCRIPT-022",
            "transcript evaluation requires a ResourceCounter when metered",
        )
    return resources


def _u16(value: int, boundary: str) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 16:
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-023",
            "the finite transcript codec requires an unsigned 16-bit integer",
        )
    return value.to_bytes(2, "big")


def _u32(value: int, boundary: str) -> bytes:
    if type(value) is not int or not 0 <= value <= MAX_GRINDING_NONCE:
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-024",
            "the grinding nonce must fit the selected grinding-profile width",
        )
    return value.to_bytes(EXACT_GRINDING_PROFILE.nonce_bytes, "big")


def _frame(namespace: str, codec: str, payload: bytes) -> bytes:
    boundary = "transcript:framing"
    _require_nonempty_text(namespace, boundary, "namespace")
    _require_nonempty_text(codec, boundary, "codec")
    if not isinstance(payload, bytes):
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-025",
            "a transcript payload must be bytes before framing",
        )
    try:
        namespace_bytes = namespace.encode("ascii")
        codec_bytes = codec.encode("ascii")
    except UnicodeEncodeError as error:
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-025",
            "transcript namespaces and codecs must be ASCII",
        ) from error
    if len(namespace_bytes) >= 1 << 16 or len(codec_bytes) >= 1 << 16:
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-025",
            "a transcript namespace or codec exceeds its framing bound",
        )
    if len(payload) >= 1 << 32:
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-025",
            "a transcript payload exceeds its framing bound",
        )
    return (
        _u16(len(namespace_bytes), boundary)
        + namespace_bytes
        + _u16(len(codec_bytes), boundary)
        + codec_bytes
        + len(payload).to_bytes(4, "big")
        + payload
    )


def _metered_frame(
    namespace: str,
    codec: str,
    payload: bytes,
    resources: ResourceCounter,
) -> bytes:
    framed = _frame(namespace, codec, payload)
    resources.consume_transcript_frames(1)
    return framed


def _sha256(payload: bytes, resources: ResourceCounter) -> bytes:
    resources.consume_hash(len(payload))
    return hashlib.sha256(payload).digest()


def _genesis(plan: TranscriptConstructionPlan, resources: ResourceCounter) -> bytes:
    payload = _GENESIS_DOMAIN + encode_term(
        {
            "model": plan.model,
            "algebra_profile_id": plan.algebra_profile_id.to_term(),
            "commitment_profile_id": plan.commitment_profile_id.to_term(),
            "grinding_profile_id": plan.grinding_profile_id.to_term(),
            "transcript_semantic_law_ids": [
                identity.to_term() for identity in plan.semantic_law_ids
            ],
        }
    )
    return _sha256(payload, resources)


def _absorb(
    state: bytes,
    namespace: str,
    codec: str,
    payload: bytes,
    resources: ResourceCounter,
) -> bytes:
    if not isinstance(state, bytes) or len(state) != DIGEST_BYTES:
        raise malformed(
            "transcript:state",
            "FRI-IOR-TRANSCRIPT-026",
            "a transcript state must be one SHA-256 digest",
        )
    return _sha256(
        _ABSORB_DOMAIN + state + _metered_frame(namespace, codec, payload, resources),
        resources,
    )


def _squeeze_digest(
    state: bytes,
    namespace: str,
    sampler: str,
    attempt: int,
    resources: ResourceCounter,
) -> bytes:
    return _sha256(
        _SQUEEZE_DOMAIN
        + state
        + _metered_frame(
            namespace,
            sampler,
            _u16(attempt, "transcript:sampling"),
            resources,
        ),
        resources,
    )


def _sample_fp2(
    state: bytes,
    namespace: str,
    resources: ResourceCounter,
) -> tuple[Fp2, bytes]:
    cardinality = MODULUS * MODULUS
    acceptance_ceiling = ((1 << 16) // cardinality) * cardinality
    remaining_attempts = resources.limits.sampler_attempts - resources.sampler_attempts
    for attempt in range(remaining_attempts):
        resources.consume_sampler_attempts(1)
        digest = _squeeze_digest(state, namespace, FP2_SAMPLER, attempt, resources)
        candidate = int.from_bytes(digest[:2], "big")
        if candidate < acceptance_ceiling:
            residue = candidate % cardinality
            return Fp2(Fp(residue // MODULUS), Fp(residue % MODULUS)), digest
    raise ModelFailure(
        OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        "transcript:fp2-sampling",
        "FRI-IOR-TRANSCRIPT-027",
        "the selected sampler-attempt resource limit was exhausted",
    )


def _derive_seed(
    state: bytes,
    namespace: str,
    resources: ResourceCounter,
) -> bytes:
    resources.consume_sampler_attempts(1)
    return _squeeze_digest(state, namespace, SEED_SAMPLER, 0, resources)


def _sample_query_occurrences(
    query_seed: bytes,
    resources: ResourceCounter,
) -> tuple[QueryOccurrence, ...]:
    if not isinstance(query_seed, bytes) or len(query_seed) != DIGEST_BYTES:
        raise malformed(
            "transcript:query-sampling",
            "FRI-IOR-TRANSCRIPT-028",
            "query sampling requires one 32-byte query seed",
        )
    if QUERY_DOMAIN_SIZE & (QUERY_DOMAIN_SIZE - 1) != 0:  # pragma: no cover
        raise AssertionError("the exact query domain must have power-of-two order")
    index_mask = QUERY_DOMAIN_SIZE - 1
    occurrences: list[QueryOccurrence] = []
    for ordinal in range(EXACT_PROFILE.ordered_query_count):
        resources.consume_sampler_attempts(1)
        payload = (
            _QUERY_EXPAND_DOMAIN
            + query_seed
            + _metered_frame(
                QUERY_OCCURRENCES_NAMESPACE,
                QUERY_SAMPLER,
                _u16(ordinal, "transcript:query-sampling"),
                resources,
            )
        )
        digest = _sha256(payload, resources)
        candidate = int.from_bytes(digest[:2], "big")
        occurrences.append(QueryOccurrence(ordinal, candidate & index_mask))
    return tuple(occurrences)


def _cap_payload(cap: object, boundary: str) -> bytes:
    if not isinstance(cap, MerkleCap):
        raise malformed(
            boundary,
            "FRI-IOR-TRANSCRIPT-030",
            "a committed FRI transcript requires a MerkleCap publication",
        )
    return encode_term(cap.to_term())


def _terminal_payload(coefficients: object) -> tuple[tuple[Fp2, ...], bytes]:
    if not isinstance(coefficients, tuple):
        raise malformed(
            "transcript:terminal",
            "FRI-IOR-TRANSCRIPT-031",
            "terminal coefficients must be a canonical sequence",
        )
    canonical = canonical_polynomial(
        coefficients,
        EXACT_PROFILE.terminal_max_coefficient_count,
    )
    payload = encode_term(
        {
            "coefficient_order": "ascending",
            "coefficients": [coefficient.to_term() for coefficient in canonical],
        }
    )
    return canonical, payload


def _admitted(plan: object) -> CheckResult | None:
    admission = admit_construction_plan(plan)
    if admission.outcome is not OutcomeClass.AFFIRMATIVE:
        return admission
    return None


def _begin_transcript(
    plan: object,
    statement: Any,
    application_context: Any,
    cap0: object,
    resources: ResourceCounter | None = None,
) -> _FirstRoundTranscript | CheckResult:
    """Bind the public statement, semantic context, and first cap; derive beta0."""

    boundary = "transcript:first-round"
    try:
        failure = _admitted(plan)
        if failure is not None:
            return failure
        assert isinstance(plan, TranscriptConstructionPlan)
        counter = _counter_or_default(resources)
        state = _genesis(plan, counter)
        state = _absorb(
            state,
            STATEMENT_NAMESPACE,
            CLOSED_TERM_CODEC,
            encode_term(statement),
            counter,
        )
        state = _absorb(
            state,
            APPLICATION_CONTEXT_NAMESPACE,
            CLOSED_TERM_CODEC,
            encode_term(application_context),
            counter,
        )
        state = _absorb(
            state,
            CAP0_NAMESPACE,
            CAP_CODEC,
            _cap_payload(cap0, boundary),
            counter,
        )
        beta0, state = _sample_fp2(state, BETA0_NAMESPACE, counter)
        return _FirstRoundTranscript(plan, state, beta0)
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary, f"unexpected first-round failure: {type(error).__name__}"
        )


def _continue_transcript(
    first_round: object,
    cap1: object,
    resources: ResourceCounter | None = None,
) -> _SecondRoundTranscript | CheckResult:
    """Bind the second cap after beta0 and derive beta1."""

    boundary = "transcript:second-round"
    try:
        if not isinstance(first_round, _FirstRoundTranscript):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-032",
                "second-round derivation requires an evaluator-issued first-round state",
            )
        failure = _admitted(first_round.plan)
        if failure is not None:
            return failure
        counter = _counter_or_default(resources)
        state = _absorb(
            first_round.transcript_state,
            CAP1_NAMESPACE,
            CAP_CODEC,
            _cap_payload(cap1, boundary),
            counter,
        )
        beta1, state = _sample_fp2(state, BETA1_NAMESPACE, counter)
        return _SecondRoundTranscript(
            first_round.plan,
            state,
            first_round.beta0,
            beta1,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary, f"unexpected second-round failure: {type(error).__name__}"
        )


def _bind_terminal_and_derive_work_seed(
    second_round: object,
    terminal_coefficients: object,
    resources: ResourceCounter | None = None,
) -> _WorkSeedTranscript | CheckResult:
    """Bind terminal material, then derive the explicit grinding challenge."""

    boundary = "transcript:work-seed"
    try:
        if not isinstance(second_round, _SecondRoundTranscript):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-033",
                "work-seed derivation requires an evaluator-issued second-round state",
            )
        failure = _admitted(second_round.plan)
        if failure is not None:
            return failure
        counter = _counter_or_default(resources)
        canonical, payload = _terminal_payload(terminal_coefficients)
        state = _absorb(
            second_round.transcript_state,
            TERMINAL_NAMESPACE,
            TERMINAL_CODEC,
            payload,
            counter,
        )
        work_seed = _derive_seed(state, WORK_SEED_NAMESPACE, counter)
        return _WorkSeedTranscript(
            second_round.plan,
            work_seed,
            second_round.beta0,
            second_round.beta1,
            canonical,
            work_seed,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary, f"unexpected work-seed failure: {type(error).__name__}"
        )


def _work_digest(
    work_seed: bytes,
    nonce: int,
    resources: ResourceCounter,
) -> bytes:
    if not isinstance(work_seed, bytes) or len(work_seed) != DIGEST_BYTES:
        raise malformed(
            "transcript:work-check",
            "FRI-IOR-TRANSCRIPT-034",
            "the work challenge must contain exactly 32 bytes",
        )
    nonce_bytes = _u32(nonce, "transcript:work-check")
    resources.consume_grinding_trials(1)
    return _sha256(
        _WORK_DOMAIN
        + _metered_frame(
            WORK_CHECK_NAMESPACE,
            WORK_RULE,
            work_seed + nonce_bytes,
            resources,
        ),
        resources,
    )


def _work_succeeds(
    work_seed: bytes, nonce: int, resources: ResourceCounter | None = None
) -> bool:
    """Check the predicate owned by the selected grinding profile."""

    counter = _counter_or_default(resources)
    digest = _work_digest(work_seed, nonce, counter)
    return digest[0] >> (8 - EXACT_GRINDING_PROFILE.difficulty_bits) == 0


def _find_grinding_nonce(
    work_seed: bytes,
    resources: ResourceCounter | None = None,
    *,
    start_nonce: int = 0,
) -> int:
    """Find the first successful nonce under the selected resource budget."""

    _u32(start_nonce, "transcript:grinding-search")
    counter = _counter_or_default(resources)
    remaining_trials = counter.limits.grinding_trials - counter.grinding_trials
    for offset in range(remaining_trials):
        nonce = start_nonce + offset
        if nonce > MAX_GRINDING_NONCE:
            break
        if _work_succeeds(work_seed, nonce, counter):
            return nonce
    raise ModelFailure(
        OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        "transcript:grinding-search",
        "FRI-IOR-TRANSCRIPT-035",
        "the selected grinding-trial resource limit was exhausted",
    )


def _complete_transcript(
    work_state: object,
    grinding_nonce: int,
    resources: ResourceCounter | None = None,
) -> FiatShamirTranscript | CheckResult:
    """Verify work, absorb its nonce, derive a query seed, and draw occurrences."""

    boundary = "transcript:completion"
    try:
        if not isinstance(work_state, _WorkSeedTranscript):
            raise malformed(
                boundary,
                "FRI-IOR-TRANSCRIPT-036",
                "transcript completion requires an evaluator-issued work-seed state",
            )
        failure = _admitted(work_state.plan)
        if failure is not None:
            return failure
        counter = _counter_or_default(resources)
        nonce_bytes = _u32(grinding_nonce, boundary)
        state = _absorb(
            work_state.transcript_state,
            GRINDING_NONCE_NAMESPACE,
            NONCE_CODEC,
            nonce_bytes,
            counter,
        )
        work_digest = _work_digest(work_state.work_seed, grinding_nonce, counter)
        if work_digest[0] >> (8 - EXACT_GRINDING_PROFILE.difficulty_bits) != 0:
            return refused(
                boundary,
                "FRI-IOR-TRANSCRIPT-037",
                "the published nonce does not satisfy the selected grinding profile",
            )
        query_seed = _derive_seed(state, QUERY_SEED_NAMESPACE, counter)
        occurrences = _sample_query_occurrences(query_seed, counter)
        return FiatShamirTranscript(
            work_state.plan,
            query_seed,
            work_state.beta0,
            work_state.beta1,
            work_state.terminal_coefficients,
            work_state.work_seed,
            grinding_nonce,
            work_digest,
            query_seed,
            occurrences,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected transcript-completion failure: {type(error).__name__}",
        )


def _derive_work_state_from_raw(
    plan: object,
    statement: Any,
    application_context: Any,
    cap0: object,
    cap1: object,
    terminal_coefficients: object,
    resources: ResourceCounter,
) -> _WorkSeedTranscript | CheckResult:
    first_round = _begin_transcript(
        plan,
        statement,
        application_context,
        cap0,
        resources,
    )
    if isinstance(first_round, CheckResult):
        return first_round
    second_round = _continue_transcript(first_round, cap1, resources)
    if isinstance(second_round, CheckResult):
        return second_round
    return _bind_terminal_and_derive_work_seed(
        second_round,
        terminal_coefficients,
        resources,
    )


def derive_fiat_shamir_transcript(
    plan: object,
    statement: Any,
    application_context: Any,
    cap0: object,
    cap1: object,
    terminal_coefficients: object,
    grinding_nonce: int,
    resources: ResourceCounter | None = None,
) -> FiatShamirTranscript | CheckResult:
    """Derive and check one transcript solely from raw public/proof material.

    No caller-authored intermediate transcript carrier crosses this boundary.
    The evaluator replays every protected prefix, absorbs the nonce before the
    work check, and derives query randomness only after that check succeeds.
    """

    boundary = "transcript:one-shot-verification"
    try:
        counter = _counter_or_default(resources)
        work_state = _derive_work_state_from_raw(
            plan,
            statement,
            application_context,
            cap0,
            cap1,
            terminal_coefficients,
            counter,
        )
        if isinstance(work_state, CheckResult):
            return work_state
        return _complete_transcript(work_state, grinding_nonce, counter)
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected one-shot transcript failure: {type(error).__name__}",
        )


def construct_fiat_shamir_transcript(
    plan: object,
    statement: Any,
    application_context: Any,
    cap0: object,
    cap1: object,
    terminal_coefficients: object,
    resources: ResourceCounter | None = None,
) -> FiatShamirTranscript | CheckResult:
    """Build the deterministic finite fixture by bounded nonce search.

    This convenience function is reproducibility machinery, not a claim that
    deterministic salt, nonce, or prover generation is suitable in production.
    Like verification, it accepts only raw inputs and never trusts a staged
    transcript carrier supplied by a caller.
    """

    boundary = "transcript:one-shot-construction"
    try:
        counter = _counter_or_default(resources)
        work_state = _derive_work_state_from_raw(
            plan,
            statement,
            application_context,
            cap0,
            cap1,
            terminal_coefficients,
            counter,
        )
        if isinstance(work_state, CheckResult):
            return work_state
        grinding_nonce = _find_grinding_nonce(work_state.work_seed, counter)
        return _complete_transcript(work_state, grinding_nonce, counter)
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected one-shot transcript construction failure: {type(error).__name__}",
        )
