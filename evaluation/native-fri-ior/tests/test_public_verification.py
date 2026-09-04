"""Tests for public-only committed verification of the finite FRI profile."""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
import inspect
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import friiormodel.committed as committed_model  # noqa: E402
from friiormodel.commitment import (  # noqa: E402
    CommitmentTree,
    PairOpening,
    build_commitment,
)
from friiormodel.field import Fp, Fp2, evaluate_polynomial  # noqa: E402
from friiormodel.profile import (  # noqa: E402
    D0,
    D1,
    DEFAULT_VALIDATION_LIMITS,
    EXACT_PROFILE,
)
from friiormodel.proof import (  # noqa: E402
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
)
from friiormodel.terms import (  # noqa: E402
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
)
from friiormodel.transcript import (  # noqa: E402
    CANONICAL_CONSTRUCTION_PLAN,
    FiatShamirTranscript,
    construct_fiat_shamir_transcript,
    derive_fiat_shamir_transcript,
)


STATEMENT = {
    "schema": "zkc.fri-ior.statement.v1",
    "profile": "f97-binary-two-round",
    "initial_oracle_role": "relation-supplied",
}
APPLICATION_CONTEXT = {
    "application": "native-fri-ior-validation",
    "case": "primary",
    "suffix": 71394,
}
PRIMARY_COEFFICIENTS = (3, 5, 7, 11, 13, 17, 19, 23)


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _fold_coefficients(
    coefficients: tuple[Fp2, ...],
    challenge: Fp2,
) -> tuple[Fp2, ...]:
    if len(coefficients) % 2 != 0:
        raise AssertionError("test fixture coefficient count must be even")
    return tuple(
        coefficients[index] + challenge * coefficients[index + 1]
        for index in range(0, len(coefficients), 2)
    )


def _salts(prefix: int, pair_count: int) -> tuple[bytes, ...]:
    return tuple(bytes((prefix + index,)) * 16 for index in range(pair_count))


@dataclass(frozen=True, slots=True)
class _PublicCase:
    public_inputs: CommittedFriPublicInputs
    proof: PublicFriProof
    transcript: FiatShamirTranscript
    tree0: CommitmentTree
    tree1: CommitmentTree


def _assemble_proof(
    public_inputs: CommittedFriPublicInputs,
    tree0: CommitmentTree,
    tree1: CommitmentTree,
    terminal: tuple[Fp2, ...],
    expected_beta0: Fp2,
    expected_beta1: Fp2,
) -> tuple[PublicFriProof, FiatShamirTranscript]:
    transcript = construct_fiat_shamir_transcript(
        public_inputs.transcript_plan,
        public_inputs.statement,
        public_inputs.application_context,
        tree0.cap,
        tree1.cap,
        terminal,
        ResourceCounter(),
    )
    if isinstance(transcript, CheckResult):
        raise AssertionError(transcript.to_term())
    if transcript.beta0 != expected_beta0 or transcript.beta1 != expected_beta1:
        raise AssertionError(
            f"fixture challenge drift: {transcript.beta0!r}, {transcript.beta1!r}"
        )

    keys = tuple(
        sorted(
            {
                key
                for occurrence in transcript.query_occurrences
                for key in (
                    (0, occurrence.initial_domain_index % (D0.order // 2)),
                    (1, occurrence.initial_domain_index % (D1.order // 2)),
                )
            }
        )
    )
    opening_table = tuple(
        OpeningTableEntry(
            layer,
            (tree0 if layer == 0 else tree1).open_pair(pair_index),
        )
        for layer, pair_index in keys
    )
    table_index = {entry.key: index for index, entry in enumerate(opening_table)}
    selectors = tuple(
        OccurrenceSelector(
            occurrence.ordinal,
            table_index[(0, occurrence.initial_domain_index % (D0.order // 2))],
            table_index[(1, occurrence.initial_domain_index % (D1.order // 2))],
        )
        for occurrence in transcript.query_occurrences
    )
    proof = PublicFriProof(
        tree0.cap,
        tree1.cap,
        terminal,
        transcript.grinding_nonce,
        opening_table,
        selectors,
    )
    return proof, transcript


def _build_case(
    coefficient_values: tuple[int, ...] = PRIMARY_COEFFICIENTS,
    *,
    expected_beta0: tuple[int, int] = (1, 59),
    expected_beta1: tuple[int, int] = (0, 54),
    corrupt_first_fold_index: int | None = None,
    terminal_transform=None,
) -> _PublicCase:
    public_inputs = CommittedFriPublicInputs(
        EXACT_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        STATEMENT,
        APPLICATION_CONTEXT,
    )
    source_coefficients = tuple(_fp2(value) for value in coefficient_values)
    beta0 = _fp2(*expected_beta0)
    beta1 = _fp2(*expected_beta1)

    initial_evaluations = tuple(
        evaluate_polynomial(source_coefficients, point) for point in D0.points()
    )
    tree0 = build_commitment(
        D0,
        initial_evaluations,
        _salts(0x10, D0.order // 2),
    )

    first_fold_coefficients = _fold_coefficients(source_coefficients, beta0)
    first_fold_evaluations = list(
        evaluate_polynomial(first_fold_coefficients, point) for point in D1.points()
    )
    if corrupt_first_fold_index is not None:
        first_fold_evaluations[corrupt_first_fold_index] = first_fold_evaluations[
            corrupt_first_fold_index
        ] + _fp2(1)
    tree1 = build_commitment(
        D1,
        tuple(first_fold_evaluations),
        _salts(0x40, D1.order // 2),
    )

    terminal = _fold_coefficients(first_fold_coefficients, beta1)
    if terminal_transform is not None:
        terminal = terminal_transform(terminal)
    proof, transcript = _assemble_proof(
        public_inputs,
        tree0,
        tree1,
        terminal,
        beta0,
        beta1,
    )
    return _PublicCase(public_inputs, proof, transcript, tree0, tree1)


def _replace_opening(
    proof: PublicFriProof,
    table_index: int,
    opening: PairOpening,
) -> PublicFriProof:
    table = list(proof.opening_table)
    table[table_index] = replace(table[table_index], opening=opening)
    return replace(proof, opening_table=tuple(table))


def _failing_nonce(case: _PublicCase) -> int:
    for nonce in range(32):
        result = derive_fiat_shamir_transcript(
            case.public_inputs.transcript_plan,
            case.public_inputs.statement,
            case.public_inputs.application_context,
            case.proof.cap0,
            case.proof.cap1,
            case.proof.terminal_coefficients,
            nonce,
            ResourceCounter(),
        )
        if isinstance(result, CheckResult) and result.code == "FRI-IOR-TRANSCRIPT-037":
            return nonce
    raise AssertionError("the small deterministic nonce search found no failing nonce")


class PublicCarrierTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()

    def test_verifier_surface_accepts_only_public_carriers_and_one_counter(
        self,
    ) -> None:
        self.assertEqual(
            tuple(inspect.signature(committed_model.verify_committed_fri).parameters),
            ("public_inputs", "proof", "resources"),
        )
        self.assertEqual(
            {field.name for field in fields(CommittedFriPublicInputs)},
            {"profile", "transcript_plan", "statement", "application_context"},
        )
        self.assertEqual(
            {field.name for field in fields(PublicFriProof)},
            {
                "cap0",
                "cap1",
                "terminal_coefficients",
                "grinding_nonce",
                "opening_table",
                "occurrence_selectors",
            },
        )
        serialized = repr(
            {
                "inputs": self.case.public_inputs.to_term(),
                "proof": self.case.proof.to_term(),
            }
        ).lower()
        for forbidden in (
            "native_trace",
            "source_polynomial",
            "complete_oracle",
            "private_generation",
            "commitment_tree",
        ):
            self.assertNotIn(forbidden, serialized)

    def test_staged_transcript_is_not_verifier_authority(self) -> None:
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            self.case.transcript,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-002")

    def test_public_terms_are_copied_and_deeply_immutable(self) -> None:
        statement = {"nested": {"value": 3}}
        inputs = CommittedFriPublicInputs(
            EXACT_PROFILE,
            CANONICAL_CONSTRUCTION_PLAN,
            statement,
            APPLICATION_CONTEXT,
        )
        identity = inputs.identity
        statement["nested"]["value"] = 9
        self.assertEqual(inputs.statement["nested"]["value"], 3)
        self.assertEqual(inputs.identity, identity)
        with self.assertRaises(TypeError):
            inputs.statement["nested"]["value"] = 7

    def test_non_closed_public_map_is_malformed_at_formation(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            CommittedFriPublicInputs(
                EXACT_PROFILE,
                CANONICAL_CONSTRUCTION_PLAN,
                {1: "not-a-text-key"},
                APPLICATION_CONTEXT,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-PROOF-001")

    def test_host_container_subclasses_are_not_closed_term_authority(self) -> None:
        class DictSubclass(dict):
            pass

        with self.assertRaises(ModelFailure) as raised:
            CommittedFriPublicInputs(
                EXACT_PROFILE,
                CANONICAL_CONSTRUCTION_PLAN,
                DictSubclass({"formed": True}),
                APPLICATION_CONTEXT,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-PROOF-002")

    def test_resource_counter_subclass_cannot_override_low_level_metering(self) -> None:
        class CounterSubclass(ResourceCounter):
            pass

        with self.assertRaises(ModelFailure) as raised:
            CounterSubclass()
        self.assertEqual(raised.exception.code, "FRI-IOR-RESOURCE-010")

        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            self.case.proof,
            object(),
        )
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-003")


class PublicVerificationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()

    def test_primary_public_proof_accepts_with_separate_logical_and_physical_counts(
        self,
    ) -> None:
        counter = ResourceCounter()
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            self.case.proof,
            counter,
        )
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-100")
        self.assertEqual(result.evidence["verdict"], "Accept")
        self.assertEqual(result.evidence["random_draw_count"], 4)
        self.assertEqual(result.evidence["logical_layer_query_occurrences"], 8)
        self.assertEqual(result.evidence["unique_authenticated_openings"], 5)
        self.assertEqual(result.evidence["first_fold_checks"], 4)
        self.assertEqual(result.evidence["second_fold_checks"], 4)
        self.assertFalse(result.evidence["establishes_outer_relation"])
        self.assertFalse(result.evidence["establishes_proximity_theorem"])
        self.assertEqual(counter.logical_query_occurrences, 8)
        self.assertEqual(counter.unique_openings, 5)
        self.assertEqual(counter.proof_bytes, self.case.proof.canonical_byte_length)

    def test_known_transcript_retains_antipodal_query_occurrences(
        self,
    ) -> None:
        queries = tuple(
            occurrence.initial_domain_index
            for occurrence in self.case.transcript.query_occurrences
        )
        self.assertEqual(queries, (3, 15, 11, 10))
        selectors = self.case.proof.occurrence_selectors
        self.assertEqual(
            tuple(selector.ordinal for selector in selectors), (0, 1, 2, 3)
        )
        self.assertEqual(selectors[0], replace(selectors[2], ordinal=0))
        self.assertEqual(len(self.case.proof.opening_table), 5)

    def test_reordered_and_duplicate_opening_tables_are_refused(self) -> None:
        reordered = replace(
            self.case.proof,
            opening_table=tuple(reversed(self.case.proof.opening_table)),
        )
        duplicated = replace(
            self.case.proof,
            opening_table=(
                self.case.proof.opening_table[0],
                *self.case.proof.opening_table,
            ),
        )
        for proof in (reordered, duplicated):
            with self.subTest(keys=tuple(entry.key for entry in proof.opening_table)):
                result = committed_model.verify_committed_fri(
                    self.case.public_inputs,
                    proof,
                    ResourceCounter(),
                )
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, "FRI-IOR-COMMITTED-010")

    def test_missing_opening_is_refused_as_inexact_coverage(self) -> None:
        proof = replace(
            self.case.proof,
            opening_table=self.case.proof.opening_table[:-1],
        )
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-012")

    def test_selector_count_bounds_and_mapping_are_checked(self) -> None:
        missing = replace(self.case.proof, occurrence_selectors=())
        out_of_bounds_selectors = list(self.case.proof.occurrence_selectors)
        out_of_bounds_selectors[0] = replace(
            out_of_bounds_selectors[0],
            layer0_opening_index=len(self.case.proof.opening_table),
        )
        out_of_bounds = replace(
            self.case.proof,
            occurrence_selectors=tuple(out_of_bounds_selectors),
        )
        wrong_selectors = list(self.case.proof.occurrence_selectors)
        wrong_selectors[0] = replace(wrong_selectors[0], layer0_opening_index=0)
        wrong_mapping = replace(
            self.case.proof,
            occurrence_selectors=tuple(wrong_selectors),
        )
        expected = (
            (missing, "FRI-IOR-COMMITTED-013"),
            (out_of_bounds, "FRI-IOR-COMMITTED-014"),
            (wrong_mapping, "FRI-IOR-COMMITTED-015"),
        )
        for proof, code in expected:
            with self.subTest(code=code):
                result = committed_model.verify_committed_fri(
                    self.case.public_inputs,
                    proof,
                    ResourceCounter(),
                )
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, code)

    def test_invalid_work_precedes_occurrence_coverage(self) -> None:
        proof = replace(
            self.case.proof,
            grinding_nonce=_failing_nonce(self.case),
            occurrence_selectors=(),
        )
        counter = ResourceCounter()
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            proof,
            counter,
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-037")
        self.assertEqual(counter.logical_query_occurrences, 0)

    def test_occurrence_coverage_precedes_opening_authentication(self) -> None:
        opening = self.case.proof.opening_table[0].opening
        bad_salt = bytes((opening.salt[0] ^ 1,)) + opening.salt[1:]
        unauthenticated = _replace_opening(
            self.case.proof,
            0,
            replace(opening, salt=bad_salt),
        )
        proof = replace(unauthenticated, occurrence_selectors=())
        counter = ResourceCounter()
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            proof,
            counter,
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-013")
        self.assertEqual(counter.merkle_nodes, 0)

    def test_altered_opening_is_refused_by_authentication(self) -> None:
        opening = self.case.proof.opening_table[0].opening
        bad_salt = bytes((opening.salt[0] ^ 1,)) + opening.salt[1:]
        proof = _replace_opening(
            self.case.proof,
            0,
            replace(opening, salt=bad_salt),
        )
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-025")

    def test_authenticated_inconsistent_first_fold_is_refused(self) -> None:
        case = _build_case(
            expected_beta1=(31, 57),
            corrupt_first_fold_index=0,
        )
        self.assertEqual(
            tuple(
                occurrence.initial_domain_index
                for occurrence in case.transcript.query_occurrences
            ),
            (6, 5, 8, 7),
        )
        result = committed_model.verify_committed_fri(
            case.public_inputs,
            case.proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-020")

    def test_wrong_terminal_value_is_refused_at_second_fold(self) -> None:
        case = _build_case(
            terminal_transform=lambda terminal: (
                terminal[0] + _fp2(1),
                terminal[1],
            )
        )
        result = committed_model.verify_committed_fri(
            case.public_inputs,
            case.proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-021")

    def test_terminal_degree_is_checked_after_matching_domain_evaluations(self) -> None:
        def add_vanishing_polynomial(
            terminal: tuple[Fp2, ...],
        ) -> tuple[Fp2, ...]:
            coefficient = _fp2(1)
            return (
                terminal[0] - coefficient,
                terminal[1],
                _fp2(0),
                _fp2(0),
                coefficient,
            )

        case = _build_case(terminal_transform=add_vanishing_polynomial)
        result = committed_model.verify_committed_fri(
            case.public_inputs,
            case.proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-022")

    def test_coherent_alternate_commitments_verify_without_source_comparison(
        self,
    ) -> None:
        alternate = _build_case(
            (4, 5, 7, 11, 13, 17, 19, 23),
            expected_beta0=(55, 38),
            expected_beta1=(11, 64),
        )
        self.assertEqual(alternate.public_inputs, self.case.public_inputs)
        self.assertNotEqual(alternate.proof.cap0, self.case.proof.cap0)
        self.assertNotEqual(alternate.proof.cap1, self.case.proof.cap1)
        result = committed_model.verify_committed_fri(
            alternate.public_inputs,
            alternate.proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-100")
        self.assertFalse(result.evidence["establishes_outer_relation"])

    def test_exact_profile_admission_precedes_transcript_work(self) -> None:
        unsupported_profile = replace(EXACT_PROFILE, name="unsupported-fri-profile")
        inputs = replace(self.case.public_inputs, profile=unsupported_profile)
        proof = replace(
            self.case.proof,
            grinding_nonce=_failing_nonce(self.case),
            occurrence_selectors=(),
        )
        counter = ResourceCounter()
        result = committed_model.verify_committed_fri(inputs, proof, counter)
        self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(result.code, "FRI-IOR-PROFILE-018")
        self.assertEqual(counter.transcript_frames, 0)

    def test_query_opening_resource_charge_is_atomic_and_distinct(self) -> None:
        limits = replace(
            DEFAULT_VALIDATION_LIMITS,
            logical_query_occurrences=7,
        )
        counter = ResourceCounter(limits)
        result = committed_model.verify_committed_fri(
            self.case.public_inputs,
            self.case.proof,
            counter,
        )
        self.assertIs(
            result.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(result.code, "FRI-IOR-RESOURCE-008")
        self.assertEqual(counter.logical_query_occurrences, 0)
        self.assertEqual(counter.unique_openings, 0)
        self.assertEqual(counter.proof_bytes, 0)

    def test_unexpected_checker_fault_is_not_a_refusal(self) -> None:
        with patch.object(
            committed_model,
            "binary_fold",
            side_effect=RuntimeError("injected"),
        ):
            result = committed_model.verify_committed_fri(
                self.case.public_inputs,
                self.case.proof,
                ResourceCounter(),
            )
        self.assertIs(result.outcome, OutcomeClass.CHECKER_FAILURE)
        self.assertEqual(result.code, "FRI-IOR-CHECKER-001")


if __name__ == "__main__":
    unittest.main()
