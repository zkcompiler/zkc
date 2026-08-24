"""Finite Analysis procedures for the P01 Schnorr/Sigma witness.

This module owns public-transcript algebra, bounded exhaustive experiments, and
the explicit refusal to promote finite evidence into a general theorem.  It
does not own relation truth.  Whenever fork extraction produces a candidate
witness, the candidate is allocated and checked through the Relations-owned
owner-local satisfaction operation.

The frozen evaluator profile has exactly:

* 968 accepting transcripts (11 statements x 11 nonces x 8 challenges);
* 3,388 unordered distinct-challenge forks (11 x 11 x C(8, 2)); and
* 88 challenge-conditioned SHVZK distribution comparisons (11 x 8).

Those cardinalities are executable coverage facts for one finite profile, not
security theorems for a protocol family.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from enum import Enum
import re
from typing import Any, Mapping

from .relations import (
    CheckedRelationSatisfaction,
    RelationSatisfactionOwner,
    SchnorrRelation,
    SchnorrRelationInstance,
    admit_instance,
    canonical_schnorr_relation,
    check_relation_satisfaction,
)
from .semantic import AlgebraProfile, admit_algebra
from .terms import (
    Outcome,
    Result,
    TermEncodingError,
    affirmative,
    result,
    semantic_id,
)


_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")

FINITE_PROFILE = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
EXPECTED_ACCEPTING_TRANSCRIPT_COUNT = 968
EXPECTED_UNORDERED_DISTINCT_CHALLENGE_FORK_COUNT = 3388
EXPECTED_CONDITIONAL_DISTRIBUTION_COUNT = 88
EXPECTED_TOTAL_SAMPLES_PER_SIDE = 968


def _closed_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def _safe_identity(value: Any) -> str:
    try:
        identity = value.identity
    except (AttributeError, TermEncodingError, TypeError, ValueError):
        return ""
    return identity if _closed_id(identity) else ""


@dataclass(frozen=True)
class SchnorrTranscript:
    """One public finite transcript; not an execution qualification."""

    instance_id: str
    statement: int
    commitment: int
    challenge: int
    response: int

    def term(self) -> dict[str, Any]:
        return {
            "instance_id": self.instance_id,
            "statement": self.statement,
            "commitment": self.commitment,
            "challenge": self.challenge,
            "response": self.response,
        }

    @property
    def identity(self) -> str:
        return semantic_id("p01.schnorr-transcript.v1", self.term())


def honest_transcript(
    instance: SchnorrRelationInstance,
    witness_scalar: int,
    nonce: int,
    challenge: int,
    profile: AlgebraProfile,
) -> SchnorrTranscript:
    """Generate a finite honest transcript for Analysis enumeration only."""

    if not profile.valid_scalar(witness_scalar):
        raise ValueError("witness scalar is outside the declared domain")
    if not profile.valid_scalar(nonce):
        raise ValueError("nonce is outside the declared scalar domain")
    if not profile.valid_challenge(challenge):
        raise ValueError("challenge is outside the declared challenge domain")
    return SchnorrTranscript(
        instance_id=instance.identity,
        statement=instance.public_statement,
        commitment=pow(profile.generator, nonce, profile.p),
        challenge=challenge,
        response=(nonce + challenge * witness_scalar) % profile.q,
    )


def check_accepting_transcript(
    transcript: SchnorrTranscript,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
) -> Result:
    """Check the finite public verifier equation, not Protocol execution."""

    instance_result = admit_instance(instance, relation, profile)
    if instance_result.outcome is not Outcome.AFFIRMATIVE:
        return instance_result
    if not isinstance(transcript, SchnorrTranscript):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-transcript",
            "P01-TRN-001",
            "transcript has the wrong type",
        )
    if (
        not _closed_id(transcript.instance_id)
        or any(
            not isinstance(value, int) or isinstance(value, bool)
            for value in (
                transcript.statement,
                transcript.commitment,
                transcript.challenge,
                transcript.response,
            )
        )
    ):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-transcript:shape",
            "P01-TRN-009",
            "transcript fields are outside the closed typed grammar",
            subject=_safe_identity(transcript),
        )
    if transcript.instance_id != instance.identity:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-transcript:instance",
            "P01-TRN-002",
            "transcript names a different relation instance",
            subject=_safe_identity(transcript),
        )
    if transcript.statement != instance.public_statement:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-transcript:statement",
            "P01-TRN-003",
            "transcript Statement differs from the relation instance",
            subject=transcript.identity,
        )
    if not profile.valid_group_element(transcript.statement):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:statement-domain",
            "P01-TRN-004",
            "transcript Statement is outside the subgroup",
            subject=transcript.identity,
        )
    if not profile.valid_group_element(transcript.commitment):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:commitment-domain",
            "P01-TRN-005",
            "transcript commitment is outside the subgroup",
            subject=transcript.identity,
        )
    if not profile.valid_challenge(transcript.challenge):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:challenge-domain",
            "P01-TRN-006",
            "transcript challenge is outside the challenge set",
            subject=transcript.identity,
        )
    if not profile.valid_scalar(transcript.response):
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:response-domain",
            "P01-TRN-007",
            "transcript response is outside the scalar domain",
            subject=transcript.identity,
        )
    left = pow(profile.generator, transcript.response, profile.p)
    right = (
        transcript.commitment
        * pow(transcript.statement, transcript.challenge, profile.p)
    ) % profile.p
    if left != right:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-transcript:verifier-equation",
            "P01-TRN-008",
            "transcript does not satisfy the finite Schnorr verifier equation",
            subject=transcript.identity,
        )
    return affirmative(
        "analysis:finite-transcript",
        "P01-TRN-OK",
        "finite transcript satisfies the Schnorr verifier equation",
        subject=transcript.identity,
        non_claim="not a replay-qualified Fresh or Fiat-Shamir execution",
    )


@dataclass(frozen=True)
class TranscriptFork:
    left: SchnorrTranscript
    right: SchnorrTranscript

    @property
    def identity(self) -> str:
        return semantic_id(
            "p01.schnorr-transcript-fork.v1",
            {"left": self.left.identity, "right": self.right.identity},
        )


@dataclass(frozen=True)
class FiniteForkExtraction:
    """Finite local extraction; deliberately has no portable identity/term."""

    fork_id: str
    instance_id: str
    extracted_scalar: int
    relation_satisfaction: CheckedRelationSatisfaction


def extract_special_soundness_fork(
    fork: TranscriptFork,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
    *,
    satisfaction_owner: RelationSatisfactionOwner | None = None,
) -> FiniteForkExtraction | Result:
    """Extract, then ask Relations to validate the candidate witness."""

    if not isinstance(fork, TranscriptFork):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-special-soundness:fork",
            "P01-SS-001",
            "fork has the wrong type",
        )
    if not isinstance(fork.left, SchnorrTranscript) or not isinstance(
        fork.right, SchnorrTranscript
    ):
        return result(
            Outcome.MALFORMED,
            "analysis:finite-special-soundness:fork-shape",
            "P01-SS-009",
            "fork operands must be typed Schnorr transcripts",
            subject=_safe_identity(fork),
        )
    left_result = check_accepting_transcript(fork.left, instance, relation, profile)
    if left_result.outcome is not Outcome.AFFIRMATIVE:
        return result(
            left_result.outcome,
            "analysis:finite-special-soundness:left",
            "P01-SS-002",
            "left fork operand is not an accepting transcript",
            subject=_safe_identity(fork),
            operand_result=left_result.term(),
        )
    right_result = check_accepting_transcript(
        fork.right, instance, relation, profile
    )
    if right_result.outcome is not Outcome.AFFIRMATIVE:
        return result(
            right_result.outcome,
            "analysis:finite-special-soundness:right",
            "P01-SS-003",
            "right fork operand is not an accepting transcript",
            subject=_safe_identity(fork),
            operand_result=right_result.term(),
        )
    if fork.left.statement != fork.right.statement:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-special-soundness:common-statement",
            "P01-SS-004",
            "fork transcripts do not share the exact Statement",
            subject=_safe_identity(fork),
        )
    if fork.left.commitment != fork.right.commitment:
        return result(
            Outcome.MISMATCH,
            "analysis:finite-special-soundness:common-first-message",
            "P01-SS-005",
            "fork transcripts do not share the exact first message",
            subject=_safe_identity(fork),
        )
    if fork.left.challenge == fork.right.challenge:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-special-soundness:distinct-challenges",
            "P01-SS-006",
            "special-soundness fork requires distinct challenges",
            subject=_safe_identity(fork),
        )
    denominator = (fork.left.challenge - fork.right.challenge) % profile.q
    if denominator == 0:
        return result(
            Outcome.SEMANTIC_NEGATIVE,
            "analysis:finite-special-soundness:invertibility",
            "P01-SS-007",
            "challenge difference is not invertible modulo q",
            subject=_safe_identity(fork),
        )
    extracted = (
        (fork.left.response - fork.right.response)
        * pow(denominator, -1, profile.q)
    ) % profile.q

    owner = satisfaction_owner or RelationSatisfactionOwner()
    assignment = owner.allocate_witness(instance, extracted)
    satisfaction = check_relation_satisfaction(
        assignment,
        instance,
        relation,
        profile,
        owner=owner,
    )
    if isinstance(satisfaction, Result):
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-special-soundness:relation-validation",
            "P01-SS-008",
            "Relations refused or failed to complete extracted-witness satisfaction",
            subject=_safe_identity(fork),
            relation_failure=satisfaction.term(),
        )
    if satisfaction.outcome is not Outcome.AFFIRMATIVE:
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-special-soundness:relation-validation",
            "P01-SS-008",
            "Relations found that the extracted candidate does not satisfy the relation",
            subject=_safe_identity(fork),
            relation_satisfaction_outcome=satisfaction.outcome.value,
            relation_satisfaction_code=satisfaction.code,
        )
    return FiniteForkExtraction(
        fork.identity,
        instance.identity,
        extracted,
        satisfaction,
    )


def check_special_soundness_fork(
    fork: TranscriptFork,
    instance: SchnorrRelationInstance,
    relation: SchnorrRelation,
    profile: AlgebraProfile,
    *,
    satisfaction_owner: RelationSatisfactionOwner | None = None,
) -> Result:
    extraction = extract_special_soundness_fork(
        fork,
        instance,
        relation,
        profile,
        satisfaction_owner=satisfaction_owner,
    )
    if isinstance(extraction, Result):
        return extraction
    return affirmative(
        "analysis:finite-special-soundness",
        "P01-SS-OK",
        "two accepting finite transcripts with one first message and distinct challenges yield a Relations-validated satisfying scalar",
        subject=extraction.fork_id,
        instance_id=extraction.instance_id,
        extracted_scalar=extraction.extracted_scalar,
        relation_validation="Relations-owned owner-local satisfaction",
        scope="one finite transcript pair; no strategy or theorem quantification",
    )


def _require_finite_profile(profile: AlgebraProfile, boundary: str) -> Result | None:
    algebra_result = admit_algebra(profile)
    if algebra_result.outcome is not Outcome.AFFIRMATIVE:
        return algebra_result
    if profile != FINITE_PROFILE:
        return result(
            Outcome.UNSUPPORTED,
            boundary,
            "P01-FIN-001",
            "exhaustive evaluator is pinned to p=23, q=11, g=2, C={0,...,7}",
            subject=profile.identity,
            supported_profile_id=FINITE_PROFILE.identity,
        )
    return None


def exhaustive_special_soundness(
    profile: AlgebraProfile = FINITE_PROFILE,
) -> Result:
    """Enumerate every accepted fork in the frozen finite profile.

    Every subgroup Statement and commitment has a unique scalar exponent in
    this prime-order cyclic group.  Enumerating every secret exponent, nonce
    exponent, and unordered distinct challenge pair therefore covers every
    accepting public-transcript fork in this profile.  That finite coverage
    fact is still not strategy quantification or a general theorem.
    """

    profile_failure = _require_finite_profile(
        profile, "analysis:finite-special-soundness:exhaustive"
    )
    if profile_failure is not None:
        return profile_failure
    relation = canonical_schnorr_relation(profile)
    satisfaction_owner = RelationSatisfactionOwner()
    fork_count = 0
    accepting_transcript_count = 0
    for secret in range(profile.q):
        instance = SchnorrRelationInstance(
            relation.identity,
            pow(profile.generator, secret, profile.p),
        )
        for nonce in range(profile.q):
            transcripts = tuple(
                honest_transcript(instance, secret, nonce, challenge, profile)
                for challenge in range(profile.challenge_size)
            )
            accepting_transcript_count += len(transcripts)
            for left_index, left in enumerate(transcripts):
                for right in transcripts[left_index + 1 :]:
                    extraction = extract_special_soundness_fork(
                        TranscriptFork(left, right),
                        instance,
                        relation,
                        profile,
                        satisfaction_owner=satisfaction_owner,
                    )
                    if isinstance(extraction, Result):
                        return result(
                            Outcome.CHECKER_FAILURE,
                            "analysis:finite-special-soundness:exhaustive",
                            "P01-SS-ENUM-001",
                            "an exhaustively generated accepting fork failed extraction",
                            subject=profile.identity,
                            secret=secret,
                            nonce=nonce,
                            left_challenge=left.challenge,
                            right_challenge=right.challenge,
                            failure=extraction.term(),
                        )
                    if extraction.extracted_scalar != secret:
                        return result(
                            Outcome.CHECKER_FAILURE,
                            "analysis:finite-special-soundness:exhaustive",
                            "P01-SS-ENUM-002",
                            "finite extractor returned a different scalar",
                            subject=profile.identity,
                            expected_scalar=secret,
                            actual_scalar=extraction.extracted_scalar,
                        )
                    fork_count += 1

    if accepting_transcript_count != EXPECTED_ACCEPTING_TRANSCRIPT_COUNT:
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-special-soundness:exhaustive",
            "P01-SS-ENUM-003",
            "accepting-transcript count differs from the frozen coverage cardinality",
            subject=profile.identity,
            expected_accepting_transcript_count=(
                EXPECTED_ACCEPTING_TRANSCRIPT_COUNT
            ),
            actual_accepting_transcript_count=accepting_transcript_count,
        )
    if fork_count != EXPECTED_UNORDERED_DISTINCT_CHALLENGE_FORK_COUNT:
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-special-soundness:exhaustive",
            "P01-SS-ENUM-004",
            "fork count differs from the frozen coverage cardinality",
            subject=profile.identity,
            expected_unordered_distinct_challenge_fork_count=(
                EXPECTED_UNORDERED_DISTINCT_CHALLENGE_FORK_COUNT
            ),
            actual_unordered_distinct_challenge_fork_count=fork_count,
        )
    return affirmative(
        "analysis:finite-special-soundness:exhaustive",
        "P01-SS-ENUM-OK",
        "every frozen-profile accepting fork extracts the unique enumerated scalar and passes Relations-owned satisfaction",
        subject=profile.identity,
        statement_count=profile.q,
        nonce_count_per_statement=profile.q,
        challenge_count_per_statement_nonce=profile.challenge_size,
        accepting_transcript_count=accepting_transcript_count,
        unordered_distinct_challenge_fork_count=fork_count,
        coverage="all x, all nonces, and all unordered distinct challenge pairs in the frozen profile",
        non_claim="not a general special-soundness theorem or knowledge extractor",
    )


def exhaustive_shvzk_distribution_equality(
    profile: AlgebraProfile = FINITE_PROFILE,
) -> Result:
    """Compare exact real and fixed-challenge simulator distributions."""

    profile_failure = _require_finite_profile(
        profile, "analysis:finite-shvzk:exhaustive"
    )
    if profile_failure is not None:
        return profile_failure
    conditional_distribution_count = 0
    total_samples_per_side = 0
    for secret in range(profile.q):
        statement = pow(profile.generator, secret, profile.p)
        for challenge in range(profile.challenge_size):
            real: Counter[tuple[int, int, int]] = Counter()
            simulated: Counter[tuple[int, int, int]] = Counter()
            for nonce in range(profile.q):
                commitment = pow(profile.generator, nonce, profile.p)
                response = (nonce + challenge * secret) % profile.q
                real[(commitment, challenge, response)] += 1
            for response in range(profile.q):
                statement_power = pow(statement, challenge, profile.p)
                commitment = (
                    pow(profile.generator, response, profile.p)
                    * pow(statement_power, -1, profile.p)
                ) % profile.p
                simulated[(commitment, challenge, response)] += 1
                left = pow(profile.generator, response, profile.p)
                right = commitment * statement_power % profile.p
                if left != right:
                    return result(
                        Outcome.CHECKER_FAILURE,
                        "analysis:finite-shvzk:simulator-acceptance",
                        "P01-SHVZK-001",
                        "fixed-challenge simulator emitted a rejecting transcript",
                        subject=profile.identity,
                        secret=secret,
                        challenge=challenge,
                        response=response,
                    )
            if real != simulated:
                return result(
                    Outcome.SEMANTIC_NEGATIVE,
                    "analysis:finite-shvzk:distribution-equality",
                    "P01-SHVZK-002",
                    "real and fixed-challenge simulator distributions differ",
                    subject=profile.identity,
                    secret=secret,
                    challenge=challenge,
                    real_support=len(real),
                    simulated_support=len(simulated),
                )
            conditional_distribution_count += 1
            total_samples_per_side += profile.q

    if (
        conditional_distribution_count
        != EXPECTED_CONDITIONAL_DISTRIBUTION_COUNT
        or total_samples_per_side != EXPECTED_TOTAL_SAMPLES_PER_SIDE
    ):
        return result(
            Outcome.CHECKER_FAILURE,
            "analysis:finite-shvzk:exhaustive",
            "P01-SHVZK-ENUM-001",
            "SHVZK enumeration differs from the frozen coverage cardinalities",
            subject=profile.identity,
            expected_conditional_distribution_count=(
                EXPECTED_CONDITIONAL_DISTRIBUTION_COUNT
            ),
            actual_conditional_distribution_count=conditional_distribution_count,
            expected_total_samples_per_side=EXPECTED_TOTAL_SAMPLES_PER_SIDE,
            actual_total_samples_per_side=total_samples_per_side,
        )
    return affirmative(
        "analysis:finite-shvzk:exhaustive",
        "P01-SHVZK-OK",
        "real and simulator transcript distributions are exactly equal for every frozen-profile Statement and fixed challenge",
        subject=profile.identity,
        statement_count=profile.q,
        challenge_count_per_statement=profile.challenge_size,
        conditional_distribution_count=conditional_distribution_count,
        support_points_per_distribution_per_side=profile.q,
        total_samples_per_side=total_samples_per_side,
        simulator_inputs=("statement", "fixed challenge", "simulator randomness"),
        simulator_omits="witness",
        non_claim="not malicious-verifier ZK, a general SHVZK theorem, or ROM/QROM simulation",
    )


class ApplicabilityClaim(str, Enum):
    FINITE_SPECIAL_SOUNDNESS_ALGEBRA = "FiniteSpecialSoundnessAlgebra"
    FINITE_SHVZK_DISTRIBUTION = "FiniteSHVZKDistribution"
    GENERAL_SPECIAL_SOUNDNESS = "GeneralSpecialSoundnessTheorem"
    GENERAL_SHVZK = "GeneralSpecialHVZKTheorem"
    GENERAL_HVZK = "GeneralHVZKTheorem"
    KNOWLEDGE_SOUNDNESS = "KnowledgeSoundness"
    FIAT_SHAMIR_ROM = "FiatShamirROM"
    FIAT_SHAMIR_QROM = "FiatShamirQROM"


def probe_analysis_applicability(
    claim: ApplicabilityClaim,
    profile: AlgebraProfile = FINITE_PROFILE,
) -> Result:
    """Answer bounded questions and refuse unsupported theorem promotions."""

    if not isinstance(claim, ApplicabilityClaim):
        return result(
            Outcome.MALFORMED,
            "analysis:applicability",
            "P01-APP-001",
            "analysis applicability claim is outside the closed vocabulary",
        )
    profile_result = admit_algebra(profile)
    if profile_result.outcome is not Outcome.AFFIRMATIVE:
        return profile_result
    if claim is ApplicabilityClaim.FINITE_SPECIAL_SOUNDNESS_ALGEBRA:
        return exhaustive_special_soundness(profile)
    if claim is ApplicabilityClaim.FINITE_SHVZK_DISTRIBUTION:
        return exhaustive_shvzk_distribution_equality(profile)

    requirements: Mapping[ApplicabilityClaim, tuple[str, str, str]] = {
        ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS: (
            "P01-APP-101",
            "finite enumeration cannot mint a general special-soundness theorem",
            "authenticated theorem capability with exact protocol/relation correspondence",
        ),
        ApplicabilityClaim.GENERAL_SHVZK: (
            "P01-APP-102",
            "finite fixed-challenge equality cannot mint a general special-HVZK theorem",
            "fixed-challenge simulator theorem over the declared protocol family",
        ),
        ApplicabilityClaim.GENERAL_HVZK: (
            "P01-APP-103",
            "SHVZK evidence is not silently retyped as an independently scoped HVZK result",
            "honest-verifier view definition and exact joint-distribution theorem",
        ),
        ApplicabilityClaim.KNOWLEDGE_SOUNDNESS: (
            "P01-APP-104",
            "a direct two-transcript extractor is not a strategy-level proof-of-knowledge extractor",
            "adversarial strategy, rewinding rights, threshold, extractor, and quantitative bound",
        ),
        ApplicabilityClaim.FIAT_SHAMIR_ROM: (
            "P01-APP-105",
            "finite transcript algebra does not establish a Fiat-Shamir ROM theorem",
            "exact ROM theorem, oracle interface, adversary map, correspondence, and loss transformer",
        ),
        ApplicabilityClaim.FIAT_SHAMIR_QROM: (
            "P01-APP-106",
            "classical finite transcript algebra does not establish a Fiat-Shamir QROM theorem",
            "exact QROM theorem, quantum query access, reprogram rights, adversary map, and loss transformer",
        ),
    }
    code, detail, missing = requirements[claim]
    return result(
        Outcome.REFUSED,
        f"analysis:applicability:{claim.value}",
        code,
        detail,
        subject=profile.identity,
        available_evidence=(
            ApplicabilityClaim.FINITE_SPECIAL_SOUNDNESS_ALGEBRA.value,
            ApplicabilityClaim.FINITE_SHVZK_DISTRIBUTION.value,
        ),
        missing_capability=missing,
        non_promotion_law="finite evidence cannot author theorem applicability",
    )


def applicability_refusal_matrix(
    profile: AlgebraProfile = FINITE_PROFILE,
) -> dict[str, Result]:
    return {
        claim.value: probe_analysis_applicability(claim, profile)
        for claim in ApplicabilityClaim
    }


def run_self_check() -> dict[str, Result]:
    """Exercise finite positive, negative, exhaustive, and refusal lanes."""

    profile = FINITE_PROFILE
    relation = canonical_schnorr_relation(profile)
    instance = SchnorrRelationInstance(relation.identity, 13)
    owner = RelationSatisfactionOwner()

    left = honest_transcript(instance, 7, 4, 3, profile)
    right = honest_transcript(instance, 7, 4, 4, profile)
    fork = TranscriptFork(left, right)
    equal_challenge = TranscriptFork(left, left)
    different_commitment = TranscriptFork(
        left, honest_transcript(instance, 7, 5, 4, profile)
    )
    rejected_right = SchnorrTranscript(
        instance_id=right.instance_id,
        statement=right.statement,
        commitment=right.commitment,
        challenge=right.challenge,
        response=(right.response + 1) % profile.q,
    )
    rejected = TranscriptFork(left, rejected_right)

    checks = {
        "fork": check_special_soundness_fork(
            fork,
            instance,
            relation,
            profile,
            satisfaction_owner=owner,
        ),
        "equal_challenge_fork": check_special_soundness_fork(
            equal_challenge, instance, relation, profile
        ),
        "different_commitment_fork": check_special_soundness_fork(
            different_commitment, instance, relation, profile
        ),
        "rejected_fork": check_special_soundness_fork(
            rejected, instance, relation, profile
        ),
        "exhaustive_special_soundness": exhaustive_special_soundness(profile),
        "exhaustive_shvzk": exhaustive_shvzk_distribution_equality(profile),
    }
    expected = {
        "fork": Outcome.AFFIRMATIVE,
        "equal_challenge_fork": Outcome.SEMANTIC_NEGATIVE,
        "different_commitment_fork": Outcome.MISMATCH,
        "rejected_fork": Outcome.SEMANTIC_NEGATIVE,
        "exhaustive_special_soundness": Outcome.AFFIRMATIVE,
        "exhaustive_shvzk": Outcome.AFFIRMATIVE,
    }
    for name, expected_outcome in expected.items():
        actual = checks[name]
        if actual.outcome is not expected_outcome:
            raise AssertionError(
                f"{name}: expected {expected_outcome.value}, got "
                f"{actual.outcome.value} ({actual.code})"
            )

    matrix = applicability_refusal_matrix(profile)
    for claim in (
        ApplicabilityClaim.FINITE_SPECIAL_SOUNDNESS_ALGEBRA,
        ApplicabilityClaim.FINITE_SHVZK_DISTRIBUTION,
    ):
        if matrix[claim.value].outcome is not Outcome.AFFIRMATIVE:
            raise AssertionError(f"finite Analysis probe {claim.value} did not affirm")
    for claim in (
        ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS,
        ApplicabilityClaim.GENERAL_SHVZK,
        ApplicabilityClaim.GENERAL_HVZK,
        ApplicabilityClaim.KNOWLEDGE_SOUNDNESS,
        ApplicabilityClaim.FIAT_SHAMIR_ROM,
        ApplicabilityClaim.FIAT_SHAMIR_QROM,
    ):
        if matrix[claim.value].outcome is not Outcome.REFUSED:
            raise AssertionError(f"theorem probe {claim.value} was not refused")
    checks.update({f"applicability:{name}": value for name, value in matrix.items()})
    return checks


if __name__ == "__main__":
    completed = run_self_check()
    affirmative_count = sum(
        value.outcome is Outcome.AFFIRMATIVE for value in completed.values()
    )
    refusal_count = sum(
        value.outcome is Outcome.REFUSED for value in completed.values()
    )
    print(
        "P01 Analysis self-check passed: "
        f"{len(completed)} judgments, {affirmative_count} affirmative, "
        f"{refusal_count} theorem refusals"
    )
