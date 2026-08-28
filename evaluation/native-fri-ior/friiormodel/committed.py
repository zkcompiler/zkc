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
from typing import Any

from .commitment import (
    EXACT_COMMITMENT_PROFILE,
    MerkleCap,
    PairOpening,
    verify_pair_opening,
)
from .field import (
    Fp2,
    binary_fold,
    canonical_polynomial,
    evaluate_polynomial,
    polynomial_degree,
)
from .native import RandomQueryDraw
from .profile import D0, D1, D2, EXACT_ALGEBRA_PROFILE, EXACT_PROFILE, admit_exact_profile
from .proof import (
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
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
from .transcript import FiatShamirTranscript, derive_fiat_shamir_transcript


LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW = 2


@dataclass(frozen=True, slots=True)
class ExplicitCommittedFriExecution:
    """Committed-Core inputs with challenge origin left outside the carrier.

    A Fresh verifier may supply the values directly.  The Fiat--Shamir wrapper
    derives the same values from raw public inputs and then delegates to the
    same Core checker.  No work nonce, statement, application context, or
    transcript construction plan appears in this carrier.
    """

    algebra_profile_id: SemanticId
    commitment_profile_id: SemanticId
    cap0: MerkleCap
    beta0: Fp2
    cap1: MerkleCap
    beta1: Fp2
    terminal_coefficients: tuple[Fp2, ...]
    query_draws: tuple[RandomQueryDraw, ...]
    opening_table: tuple[OpeningTableEntry, ...]
    occurrence_selectors: tuple[OccurrenceSelector, ...]

    def __post_init__(self) -> None:
        if type(self) is not ExplicitCommittedFriExecution:
            raise malformed(
                "committed:explicit-execution-formation",
                "FRI-IOR-COMMITTED-004",
                "explicit committed execution requires the exact closed carrier",
            )
        if (
            not isinstance(self.algebra_profile_id, SemanticId)
            or self.algebra_profile_id.subject_kind != "fri-algebra-profile"
            or not isinstance(self.commitment_profile_id, SemanticId)
            or self.commitment_profile_id.subject_kind != "fri-commitment-profile"
            or not isinstance(self.cap0, MerkleCap)
            or not isinstance(self.beta0, Fp2)
            or not isinstance(self.cap1, MerkleCap)
            or not isinstance(self.beta1, Fp2)
        ):
            raise malformed(
                "committed:explicit-execution-formation",
                "FRI-IOR-COMMITTED-004",
                "explicit committed execution contains a wrong-kind scalar value",
            )
        canonical_polynomial(
            self.terminal_coefficients,
            EXACT_PROFILE.terminal_max_coefficient_count,
        )
        if (
            type(self.query_draws) is not tuple
            or not all(type(item) is RandomQueryDraw for item in self.query_draws)
            or type(self.opening_table) is not tuple
            or not all(type(item) is OpeningTableEntry for item in self.opening_table)
            or type(self.occurrence_selectors) is not tuple
            or not all(
                type(item) is OccurrenceSelector for item in self.occurrence_selectors
            )
        ):
            raise malformed(
                "committed:explicit-execution-formation",
                "FRI-IOR-COMMITTED-004",
                "explicit committed execution requires exact immutable sequences",
            )

    def to_term(self) -> dict[str, Any]:
        return {
            "schema": "zkc.fri-ior.explicit-committed-core-execution.v1",
            "algebra_profile_id": self.algebra_profile_id.to_term(),
            "commitment_profile_id": self.commitment_profile_id.to_term(),
            "cap0": self.cap0.to_term(),
            "beta0": self.beta0.to_term(),
            "cap1": self.cap1.to_term(),
            "beta1": self.beta1.to_term(),
            "terminal_coefficients": [
                coefficient.to_term() for coefficient in self.terminal_coefficients
            ],
            "ordered_query_draws": [
                {
                    "ordinal": draw.ordinal,
                    "initial_domain_index": draw.initial_domain_index,
                }
                for draw in self.query_draws
            ],
            "opening_table": [entry.to_term() for entry in self.opening_table],
            "occurrence_selectors": [
                selector.to_term() for selector in self.occurrence_selectors
            ],
        }

    @property
    def identity(self):
        return semantic_id(
            "explicit-committed-fri-execution",
            "fri-ior.explicit-committed-fri-execution.v1",
            self.to_term(),
        )


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
    query_draws: tuple[RandomQueryDraw, ...],
) -> tuple[tuple[int, int], ...]:
    keys: set[tuple[int, int]] = set()
    for draw in query_draws:
        query_index = draw.initial_domain_index
        keys.add((0, query_index % (D0.order // 2)))
        keys.add((1, query_index % (D1.order // 2)))
    return tuple(sorted(keys))


def _cover_occurrences(
    execution: ExplicitCommittedFriExecution,
    resources: ResourceCounter,
    public_message_byte_length: int,
) -> tuple[_CoveredOccurrence, ...] | CheckResult:
    """Check canonical deduplication and resolve all four logical draws."""

    boundary = "committed:occurrence-coverage"
    table = execution.opening_table
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

    expected_keys = _expected_opening_keys(execution.query_draws)
    if table_keys != expected_keys:
        return refused(
            boundary,
            "FRI-IOR-COMMITTED-012",
            "the canonical opening table does not exactly cover the derived draws",
        )

    occurrences = execution.query_draws
    selectors = execution.occurrence_selectors
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
        if selector.layer0_opening_index >= len(
            table
        ) or selector.layer1_opening_index >= len(table):
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
        proof_bytes=public_message_byte_length,
    )
    return tuple(covered)


def _authenticate_unique_openings(
    execution: ExplicitCommittedFriExecution,
    resources: ResourceCounter,
) -> CheckResult | None:
    """Authenticate each physical table row exactly once."""

    for entry in execution.opening_table:
        domain = D0 if entry.layer == 0 else D1
        cap = execution.cap0 if entry.layer == 0 else execution.cap1
        result = verify_pair_opening(domain, cap, entry.opening, resources)
        if result.outcome is not OutcomeClass.AFFIRMATIVE:
            return result
    return None


def _check_first_fold(
    covered: tuple[_CoveredOccurrence, ...],
    execution: ExplicitCommittedFriExecution,
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
            execution.beta0,
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
    execution: ExplicitCommittedFriExecution,
    resources: ResourceCounter,
) -> CheckResult | None:
    boundary = "committed:fold1"
    for occurrence in covered:
        pair_index = occurrence.initial_domain_index % (D1.order // 2)
        expected = binary_fold(
            D1.points()[pair_index],
            occurrence.layer1.positive,
            occurrence.layer1.negative,
            execution.beta1,
            resources,
        )
        published = evaluate_polynomial(
            execution.terminal_coefficients,
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


def _check_explicit_committed_execution(
    execution: ExplicitCommittedFriExecution,
    resources: ResourceCounter,
    public_message_byte_length: int,
) -> CheckResult:
    """Run the challenge-origin-independent committed Core checks."""

    if (
        execution.algebra_profile_id != EXACT_ALGEBRA_PROFILE.identity
        or execution.commitment_profile_id != EXACT_COMMITMENT_PROFILE.identity
    ):
        return unsupported(
            "committed:explicit-core-verification",
            "FRI-IOR-COMMITTED-009",
            "the committed execution selects unsupported algebra or commitment semantics",
        )
    if (
        len(execution.query_draws) != EXACT_PROFILE.ordered_query_count
        or tuple(draw.ordinal for draw in execution.query_draws)
        != tuple(range(EXACT_PROFILE.ordered_query_count))
        or any(
            not 0 <= draw.initial_domain_index < D0.order
            for draw in execution.query_draws
        )
    ):
        return refused(
            "committed:occurrence-coverage",
            "FRI-IOR-COMMITTED-013",
            "query draws must be the exact four ordered in-domain occurrences",
        )

    covered = _cover_occurrences(
        execution,
        resources,
        public_message_byte_length,
    )
    if isinstance(covered, CheckResult):
        return covered
    authentication_failure = _authenticate_unique_openings(
        execution,
        resources,
    )
    if authentication_failure is not None:
        return authentication_failure
    first_fold_failure = _check_first_fold(covered, execution, resources)
    if first_fold_failure is not None:
        return first_fold_failure
    second_fold_failure = _check_second_fold_and_terminal_evaluations(
        covered,
        execution,
        resources,
    )
    if second_fold_failure is not None:
        return second_fold_failure
    if (
        polynomial_degree(execution.terminal_coefficients)
        >= EXACT_PROFILE.terminal_degree_bound_exclusive
    ):
        return refused(
            "committed:terminal-degree",
            "FRI-IOR-COMMITTED-022",
            "the authenticated terminal polynomial exceeds the exact degree bound",
        )
    return affirmative(
        "committed:explicit-core-verification",
        "FRI-IOR-COMMITTED-101",
        "the explicit-coin committed Core checks accept",
        subject=execution.identity,
        verdict="Accept",
        beta0=execution.beta0.to_term(),
        beta1=execution.beta1.to_term(),
        ordered_initial_domain_indices=[
            draw.initial_domain_index for draw in execution.query_draws
        ],
        random_draw_count=len(execution.query_draws),
        logical_layer_query_occurrences=(
            len(covered) * LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW
        ),
        unique_authenticated_openings=len(execution.opening_table),
        first_fold_checks=len(covered),
        second_fold_checks=len(covered),
        proof_bytes=public_message_byte_length,
        establishes_outer_relation=False,
        establishes_proximity_theorem=False,
    )


def verify_explicit_committed_fri(
    candidate: object,
    resources: object,
) -> CheckResult:
    """Verify the committed Core under caller-supplied challenge values."""

    boundary = "committed:explicit-core-verification"
    if type(candidate) is not ExplicitCommittedFriExecution:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-COMMITTED-005",
            "explicit committed verification requires its exact execution carrier",
        )
    if type(resources) is not ResourceCounter:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-COMMITTED-006",
            "explicit committed verification requires one caller-owned ResourceCounter",
        )
    try:
        public_message_byte_length = len(
            encode_term(
                {
                    "schema": "zkc.fri-ior.committed-fresh-public-messages.v1",
                    "cap0": candidate.cap0.to_term(),
                    "cap1": candidate.cap1.to_term(),
                    "terminal_coefficients": [
                        coefficient.to_term()
                        for coefficient in candidate.terminal_coefficients
                    ],
                    "opening_table": [
                        entry.to_term() for entry in candidate.opening_table
                    ],
                    "occurrence_selectors": [
                        selector.to_term()
                        for selector in candidate.occurrence_selectors
                    ],
                }
            )
        )
        return _check_explicit_committed_execution(
            candidate,
            resources,
            public_message_byte_length,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected explicit committed-verifier failure: {type(error).__name__}",
        )


def verify_explicit_committed_prefix(
    candidate: object,
    resources: object,
) -> CheckResult:
    """Admit the publication/challenge/terminal prefix without query work."""

    boundary = "committed:explicit-prefix-verification"
    if type(candidate) is not ExplicitCommittedFriExecution:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-COMMITTED-007",
            "explicit prefix verification requires its exact execution carrier",
        )
    if type(resources) is not ResourceCounter:
        return CheckResult(
            OutcomeClass.MALFORMED,
            boundary,
            "FRI-IOR-COMMITTED-008",
            "explicit prefix verification requires one caller-owned ResourceCounter",
        )
    try:
        if (
            candidate.algebra_profile_id != EXACT_ALGEBRA_PROFILE.identity
            or candidate.commitment_profile_id != EXACT_COMMITMENT_PROFILE.identity
        ):
            return unsupported(
                boundary,
                "FRI-IOR-COMMITTED-009",
                "the committed prefix selects unsupported algebra or commitment semantics",
            )
        return affirmative(
            boundary,
            "FRI-IOR-COMMITTED-102",
            "the committed publication and terminal-material prefix is formed",
            subject=candidate.identity,
            performs_query_sampling=False,
            performs_opening_authentication=False,
            decides_protocol_verdict=False,
        )
    except ModelFailure as error:
        return error.to_result()
    except Exception as error:  # pragma: no cover - fault-injection boundary
        return checker_failure(
            boundary,
            f"unexpected explicit prefix-verifier failure: {type(error).__name__}",
        )


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
            raise RuntimeError(
                "the one-shot transcript API returned a wrong-kind value"
            )

        execution = ExplicitCommittedFriExecution(
            inputs.profile.identity,
            EXACT_COMMITMENT_PROFILE.identity,
            public_proof.cap0,
            derived.beta0,
            public_proof.cap1,
            derived.beta1,
            derived.terminal_coefficients,
            tuple(
                RandomQueryDraw(
                    occurrence.ordinal,
                    occurrence.initial_domain_index,
                )
                for occurrence in derived.query_occurrences
            ),
            public_proof.opening_table,
            public_proof.occurrence_selectors,
        )
        core_result = _check_explicit_committed_execution(
            execution,
            counter,
            public_proof.canonical_byte_length,
        )
        if core_result.outcome is not OutcomeClass.AFFIRMATIVE:
            return core_result

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
                len(derived.query_occurrences)
                * LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW
            ),
            unique_authenticated_openings=len(public_proof.opening_table),
            first_fold_checks=len(derived.query_occurrences),
            second_fold_checks=len(derived.query_occurrences),
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
    "ExplicitCommittedFriExecution",
    "LOGICAL_LAYER_QUERY_OCCURRENCES_PER_DRAW",
    "verify_committed_fri",
    "verify_explicit_committed_fri",
    "verify_explicit_committed_prefix",
]
