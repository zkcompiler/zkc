"""Public-only verification for the exact committed finite FRI profile.

The verifier accepts one closed public-input carrier, one closed public proof,
and one exact caller-owned resource counter.  That counter is cooperative
instrumentation at this low-level API; an authoritative boundary must create
it privately from already-admitted immutable limits.  The verifier reconstructs Fiat--Shamir from raw
public material and never accepts a staged transcript, native execution trace,
source polynomial, complete oracle, or commitment-construction state.

An affirmative result is deliberately local: the published openings
authenticate and the four ordered query occurrences satisfy this profile's two
fold checks and terminal-degree check.  It does not establish a proximity
theorem or any outer relation.
"""

from __future__ import annotations

from dataclasses import dataclass

from .commitment import PairOpening, verify_pair_opening
from .field import binary_fold, evaluate_polynomial, polynomial_degree
from .profile import D0, D1, D2, EXACT_PROFILE, admit_exact_profile
from .proof import CommittedFriPublicInputs, PublicFriProof
from .terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    affirmative,
    checker_failure,
    malformed,
    refused,
    semantic_id,
)
from .transcript import FiatShamirTranscript, derive_fiat_shamir_transcript


LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW = 2


@dataclass(frozen=True, slots=True)
class _CoveredOccurrence:
    """Internal resolution of one draw to two authenticated table rows."""

    ordinal: int
    initial_domain_index: int
    layer0: PairOpening
    layer1: PairOpening


def _require_formed_inputs(
    public_inputs: object,
    proof: object,
    resources: object,
) -> tuple[CommittedFriPublicInputs, PublicFriProof, ResourceCounter]:
    if not isinstance(public_inputs, CommittedFriPublicInputs):
        raise malformed(
            "committed:formation",
            "FRI-IOR-COMMITTED-001",
            "committed verification requires a formed public-input carrier",
        )
    if not isinstance(proof, PublicFriProof):
        raise malformed(
            "committed:formation",
            "FRI-IOR-COMMITTED-002",
            "committed verification requires a formed public FRI proof",
        )
    if type(resources) is not ResourceCounter:
        raise malformed(
            "committed:formation",
            "FRI-IOR-COMMITTED-003",
            "committed verification requires one caller-owned ResourceCounter",
        )
    return public_inputs, proof, resources


def _expected_opening_keys(
    transcript: FiatShamirTranscript,
) -> tuple[tuple[int, int], ...]:
    keys: set[tuple[int, int]] = set()
    for occurrence in transcript.query_occurrences:
        query_index = occurrence.initial_domain_index
        keys.add((0, query_index % (D0.order // 2)))
        keys.add((1, query_index % (D1.order // 2)))
    return tuple(sorted(keys))


def _cover_occurrences(
    proof: PublicFriProof,
    transcript: FiatShamirTranscript,
    resources: ResourceCounter,
) -> tuple[_CoveredOccurrence, ...] | CheckResult:
    """Check canonical deduplication and resolve all four logical draws."""

    boundary = "committed:occurrence-coverage"
    table = proof.opening_table
    table_keys = tuple(entry.key for entry in table)
    if table_keys != tuple(sorted(table_keys)) or len(set(table_keys)) != len(
        table_keys
    ):
        return refused(
            boundary,
            "FRI-IOR-COMMITTED-010",
            "the opening table is not in strict canonical key order",
        )

    expected_domains = {0: D0.name, 1: D1.name}
    for entry in table:
        expected_domain = expected_domains.get(entry.layer)
        if expected_domain is None or entry.opening.domain_name != expected_domain:
            return refused(
                boundary,
                "FRI-IOR-COMMITTED-011",
                "an opening-table row has an unsupported layer or wrong domain",
            )

    expected_keys = _expected_opening_keys(transcript)
    if table_keys != expected_keys:
        return refused(
            boundary,
            "FRI-IOR-COMMITTED-012",
            "the canonical opening table does not exactly cover the derived draws",
        )

    occurrences = transcript.query_occurrences
    selectors = proof.occurrence_selectors
    if len(selectors) != len(occurrences) or tuple(
        selector.ordinal for selector in selectors
    ) != tuple(occurrence.ordinal for occurrence in occurrences):
        return refused(
            boundary,
            "FRI-IOR-COMMITTED-013",
            "selectors must preserve all four derived occurrence identities in order",
        )

    covered: list[_CoveredOccurrence] = []
    for occurrence, selector in zip(occurrences, selectors, strict=True):
        if (
            selector.layer0_opening_index >= len(table)
            or selector.layer1_opening_index >= len(table)
        ):
            return refused(
                boundary,
                "FRI-IOR-COMMITTED-014",
                "an occurrence selector points outside the canonical opening table",
            )
        layer0_entry = table[selector.layer0_opening_index]
        layer1_entry = table[selector.layer1_opening_index]
        query_index = occurrence.initial_domain_index
        if layer0_entry.key != (0, query_index % (D0.order // 2)) or (
            layer1_entry.key != (1, query_index % (D1.order // 2))
        ):
            return refused(
                boundary,
                "FRI-IOR-COMMITTED-015",
                "an occurrence selector does not name its two derived layer queries",
            )
        covered.append(
            _CoveredOccurrence(
                occurrence.ordinal,
                query_index,
                layer0_entry.opening,
                layer1_entry.opening,
            )
        )

    resources.consume_query_opening_resources(
        logical_query_occurrences=(
            len(covered) * LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW
        ),
        unique_openings=len(table),
        proof_bytes=proof.canonical_byte_length,
    )
    return tuple(covered)


def _authenticate_unique_openings(
    proof: PublicFriProof,
    resources: ResourceCounter,
) -> CheckResult | None:
    """Authenticate each physical table row exactly once."""

    for entry in proof.opening_table:
        domain = D0 if entry.layer == 0 else D1
        cap = proof.cap0 if entry.layer == 0 else proof.cap1
        result = verify_pair_opening(domain, cap, entry.opening, resources)
        if result.outcome is not OutcomeClass.AFFIRMATIVE:
            return result
    return None


def _check_first_fold(
    covered: tuple[_CoveredOccurrence, ...],
    transcript: FiatShamirTranscript,
    resources: ResourceCounter,
) -> CheckResult | None:
    boundary = "committed:fold0"
    for occurrence in covered:
        pair_index = occurrence.initial_domain_index % (D0.order // 2)
        next_index = occurrence.initial_domain_index % D1.order
        expected = binary_fold(
            D0.points()[pair_index],
            occurrence.layer0.positive,
            occurrence.layer0.negative,
            transcript.beta0,
            resources,
        )
        published = (
            occurrence.layer1.positive
            if next_index < D1.order // 2
            else occurrence.layer1.negative
        )
        if expected != published:
            return refused(
                boundary,
                "FRI-IOR-COMMITTED-020",
                "a derived occurrence fails the first authenticated fold equation",
            )
    return None


def _check_second_fold_and_terminal_evaluations(
    covered: tuple[_CoveredOccurrence, ...],
    transcript: FiatShamirTranscript,
    resources: ResourceCounter,
) -> CheckResult | None:
    boundary = "committed:fold1"
    for occurrence in covered:
        pair_index = occurrence.initial_domain_index % (D1.order // 2)
        expected = binary_fold(
            D1.points()[pair_index],
            occurrence.layer1.positive,
            occurrence.layer1.negative,
            transcript.beta1,
            resources,
        )
        published = evaluate_polynomial(
            transcript.terminal_coefficients,
            D2.points()[pair_index],
            resources,
        )
        if expected != published:
            return refused(
                boundary,
                "FRI-IOR-COMMITTED-021",
                "a derived occurrence fails the second fold-to-terminal equation",
            )
    return None


def verify_committed_fri(
    public_inputs: object,
    proof: object,
    resources: object,
) -> CheckResult:
    """Verify one proof from raw public material in fixed fail-closed order."""

    boundary = "committed:verification"
    try:
        inputs, public_proof, counter = _require_formed_inputs(
            public_inputs,
            proof,
            resources,
        )

        profile_result = admit_exact_profile(inputs.profile)
        if profile_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return profile_result

        derived = derive_fiat_shamir_transcript(
            inputs.transcript_plan,
            inputs.statement,
            inputs.application_context,
            public_proof.cap0,
            public_proof.cap1,
            public_proof.terminal_coefficients,
            public_proof.grinding_nonce,
            counter,
        )
        if isinstance(derived, CheckResult):
            return derived
        if not isinstance(derived, FiatShamirTranscript):
            raise RuntimeError("the one-shot transcript API returned a wrong-kind value")

        covered = _cover_occurrences(public_proof, derived, counter)
        if isinstance(covered, CheckResult):
            return covered

        authentication_failure = _authenticate_unique_openings(
            public_proof,
            counter,
        )
        if authentication_failure is not None:
            return authentication_failure

        first_fold_failure = _check_first_fold(covered, derived, counter)
        if first_fold_failure is not None:
            return first_fold_failure

        second_fold_failure = _check_second_fold_and_terminal_evaluations(
            covered,
            derived,
            counter,
        )
        if second_fold_failure is not None:
            return second_fold_failure

        if (
            polynomial_degree(derived.terminal_coefficients)
            >= EXACT_PROFILE.terminal_degree_bound_exclusive
        ):
            return refused(
                "committed:terminal-degree",
                "FRI-IOR-COMMITTED-022",
                "the authenticated terminal polynomial exceeds the exact degree bound",
            )

        subject = semantic_id(
            "committed-fri-verification",
            "fri-ior.committed-verification.v1",
            {
                "public_inputs": inputs.identity.to_term(),
                "proof": public_proof.identity.to_term(),
            },
        )
        return affirmative(
            boundary,
            "FRI-IOR-COMMITTED-100",
            "the exact public committed FRI checks accept",
            subject=subject,
            verdict="Accept",
            beta0=derived.beta0.to_term(),
            beta1=derived.beta1.to_term(),
            ordered_initial_domain_indices=[
                occurrence.initial_domain_index
                for occurrence in derived.query_occurrences
            ],
            random_draw_count=len(derived.query_occurrences),
            logical_layer_query_occurrences=(
                len(covered) * LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW
            ),
            unique_authenticated_openings=len(public_proof.opening_table),
            first_fold_checks=len(covered),
            second_fold_checks=len(covered),
            proof_bytes=public_proof.canonical_byte_length,
            establishes_outer_relation=False,
            establishes_proximity_theorem=False,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - exercised by fault injection
        return checker_failure(
            boundary,
            f"unexpected committed-verifier failure: {type(error).__name__}",
        )


__all__ = [
    "LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW",
    "verify_committed_fri",
]
