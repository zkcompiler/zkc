"""Tests for private FRI generation and concrete construction checking."""

from __future__ import annotations

from dataclasses import fields, replace
import inspect
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.commitment import PairOpening  # noqa: E402
from friiormodel.committed import verify_committed_fri  # noqa: E402
from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.generation import (  # noqa: E402
    CheckedNativeToCommittedExecution,
    PrivateFriGenerationMaterial,
    PublicFriArtifacts,
    check_native_to_committed_execution,
    generate_honest_native_to_committed_execution,
    primary_private_generation_material,
    primary_public_inputs,
)
from friiormodel.profile import (  # noqa: E402
    DEFAULT_VALIDATION_LIMITS,
    EXACT_PROFILE,
)
from friiormodel.proof import PublicFriProof  # noqa: E402
from friiormodel.subjects import (  # noqa: E402
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    COMMITMENT_COMPILATION_DECLARATION,
    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
    GRINDING_AUGMENTATION_DECLARATION,
)
from friiormodel.terms import (  # noqa: E402
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
)
from friiormodel.transcript import (  # noqa: E402
    FiatShamirTranscript,
    derive_fiat_shamir_transcript,
)


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _require_primary() -> CheckedNativeToCommittedExecution:
    admission = generate_honest_native_to_committed_execution(
        primary_private_generation_material(),
        primary_public_inputs(),
    )
    if admission.checked_execution is None:
        raise AssertionError(admission.result.to_term())
    return admission.checked_execution


def _replace_proof_opening(
    proof: PublicFriProof,
    table_index: int,
    opening: PairOpening,
) -> PublicFriProof:
    table = list(proof.opening_table)
    table[table_index] = replace(table[table_index], opening=opening)
    return replace(proof, opening_table=tuple(table))


class PrivateAndPublicLaneTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checked = _require_primary()

    def test_private_material_has_no_portable_term_or_identity(self) -> None:
        private = primary_private_generation_material()
        self.assertFalse(hasattr(private, "to_term"))
        self.assertFalse(hasattr(private, "identity"))
        rendered = repr(private)
        self.assertNotIn("3", rendered)
        self.assertNotIn("salt", rendered.lower())

    def test_public_projection_has_only_public_inputs_and_proof(self) -> None:
        projection = self.checked.public_artifacts
        self.assertEqual(
            {item.name for item in fields(PublicFriArtifacts)},
            {"public_inputs", "proof"},
        )
        rendered = repr(projection.to_term()).lower()
        for forbidden in (
            "private_material",
            "source_trace",
            "source_polynomial",
            "complete_logical_oracle",
            "commitment_tree",
        ):
            self.assertNotIn(forbidden, rendered)

    def test_public_projection_verifies_without_owner_local_material(self) -> None:
        projection = self.checked.public_artifacts
        result = verify_committed_fri(
            projection.public_inputs,
            projection.proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-100")

    def test_generation_surface_accepts_limits_not_a_mutable_counter(self) -> None:
        self.assertEqual(
            tuple(
                inspect.signature(
                    generate_honest_native_to_committed_execution
                ).parameters
            ),
            ("private_material", "public_inputs", "limits"),
        )
        admission = generate_honest_native_to_committed_execution(
            primary_private_generation_material(),
            primary_public_inputs(),
            ResourceCounter(),
        )
        self.assertIs(admission.result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-037")

    def test_private_salt_shape_is_checked_at_formation(self) -> None:
        private = primary_private_generation_material()
        with self.assertRaises(ModelFailure) as raised:
            PrivateFriGenerationMaterial(
                private.coefficients,
                private.initial_layer_salts[:-1],
                private.first_fold_layer_salts,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-GENERATION-002")


class HonestGenerationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checked = _require_primary()
        cls.candidate = cls.checked.candidate
        cls.projection = cls.checked.public_artifacts
        transcript = derive_fiat_shamir_transcript(
            cls.projection.public_inputs.transcript_plan,
            cls.projection.public_inputs.statement,
            cls.projection.public_inputs.application_context,
            cls.projection.proof.cap0,
            cls.projection.proof.cap1,
            cls.projection.proof.terminal_coefficients,
            cls.projection.proof.grinding_nonce,
            ResourceCounter(),
        )
        if not isinstance(transcript, FiatShamirTranscript):
            raise AssertionError(transcript.to_term())
        cls.transcript = transcript

    def test_primary_polynomial_generates_the_exact_public_vector(self) -> None:
        private = self.candidate.private_material
        self.assertEqual(
            tuple(coefficient.real.value for coefficient in private.coefficients),
            (3, 5, 7, 11, 13, 17, 19, 23),
        )
        self.assertTrue(
            all(coefficient.imag == Fp(0) for coefficient in private.coefficients)
        )
        self.assertEqual(self.transcript.beta0, _fp2(10, 34))
        self.assertEqual(self.transcript.beta1, _fp2(23, 31))
        self.assertEqual(
            tuple(
                occurrence.initial_domain_index
                for occurrence in self.transcript.query_occurrences
            ),
            (6, 6, 1, 9),
        )

    def test_checked_receipt_binds_every_construction_subject(self) -> None:
        candidate = self.candidate
        self.assertEqual(
            candidate.commitment_compilation_declaration_id,
            COMMITMENT_COMPILATION_DECLARATION.identity,
        )
        self.assertEqual(
            candidate.grinding_augmentation_declaration_id,
            GRINDING_AUGMENTATION_DECLARATION.identity,
        )
        self.assertEqual(
            candidate.fiat_shamir_construction_declaration_id,
            FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity,
        )
        self.assertEqual(
            candidate.checked_fiat_shamir_construction_id,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity,
        )

    def test_occurrence_map_preserves_duplicate_and_opposite_draws(self) -> None:
        occurrence_map = self.candidate.occurrence_map
        self.assertEqual(tuple(entry.ordinal for entry in occurrence_map), (0, 1, 2, 3))
        self.assertEqual(
            tuple(entry.initial_domain_index for entry in occurrence_map),
            (6, 6, 1, 9),
        )
        self.assertNotEqual(
            occurrence_map[0].source_initial_query_id,
            occurrence_map[1].source_initial_query_id,
        )
        self.assertEqual(
            occurrence_map[0].target_initial_opening_id,
            occurrence_map[1].target_initial_opening_id,
        )
        self.assertEqual(
            occurrence_map[0].target_first_fold_opening_id,
            occurrence_map[1].target_first_fold_opening_id,
        )
        self.assertEqual(
            occurrence_map[2].initial_layer_table_index,
            occurrence_map[3].initial_layer_table_index,
        )
        self.assertEqual(
            occurrence_map[2].first_fold_layer_table_index,
            occurrence_map[3].first_fold_layer_table_index,
        )

    def test_receipt_records_decision_and_commutation_without_security_claims(
        self,
    ) -> None:
        admission = check_native_to_committed_execution(self.candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-100")
        evidence = admission.result.evidence
        self.assertTrue(evidence["decisions_equal"])
        self.assertTrue(evidence["complete_commitment_caps_equal"])
        self.assertTrue(evidence["sampled_answer_pairs_equal"])
        self.assertTrue(evidence["challenge_and_query_trace_equal"])
        self.assertFalse(evidence["establishes_general_compiler_correctness"])
        self.assertFalse(evidence["establishes_commitment_security"])
        self.assertFalse(evidence["establishes_proximity_theorem"])
        self.assertFalse(evidence["establishes_protocol_security"])

    def test_validation_basis_changes_without_changing_execution_semantics(
        self,
    ) -> None:
        alternate_limits = replace(
            DEFAULT_VALIDATION_LIMITS,
            field_operations=1000,
        )
        admission = check_native_to_committed_execution(
            self.candidate,
            alternate_limits,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        alternate = admission.checked_execution
        assert alternate is not None
        self.assertEqual(
            alternate.semantic_execution_id,
            self.checked.semantic_execution_id,
        )
        self.assertNotEqual(
            alternate.validation_basis_id,
            self.checked.validation_basis_id,
        )
        self.assertNotEqual(alternate.identity, self.checked.identity)

    def test_resource_snapshot_is_complete_and_frozen(self) -> None:
        snapshot = self.checked.resource_snapshot
        self.assertEqual(
            set(snapshot.to_term()), set(DEFAULT_VALIDATION_LIMITS.to_term())
        )
        self.assertGreater(snapshot.field_operations, 0)
        self.assertEqual(snapshot.logical_query_occurrences, 24)
        self.assertEqual(snapshot.unique_openings, 4)
        with self.assertRaises(AttributeError):
            snapshot.field_operations = 0


class CorrespondenceRefusalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checked = _require_primary()
        cls.candidate = cls.checked.candidate

    def test_mismatched_source_trace_is_not_revalidated(self) -> None:
        trace = self.candidate.source_trace
        entries = list(trace.initial_oracle.entries)
        entries[0] = replace(
            entries[0],
            value=entries[0].value + _fp2(1),
        )
        altered_oracle = replace(trace.initial_oracle, entries=tuple(entries))
        altered_trace = replace(trace, initial_oracle=altered_oracle)
        candidate = replace(
            self.candidate,
            source_trace=altered_trace,
            claimed_source_trace_id=altered_trace.identity,
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-026")

    def test_mismatched_private_commitment_advice_is_refused(self) -> None:
        private = self.candidate.private_material
        salts = list(private.initial_layer_salts)
        salts[0] = bytes((salts[0][0] ^ 1,)) + salts[0][1:]
        candidate = replace(
            self.candidate,
            private_material=PrivateFriGenerationMaterial(
                private.coefficients,
                tuple(salts),
                private.first_fold_layer_salts,
            ),
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-027")

    def test_mismatched_target_proof_is_checked_not_silently_rebound(self) -> None:
        proof = self.candidate.public_artifacts.proof
        opening = proof.opening_table[0].opening
        bad_salt = bytes((opening.salt[0] ^ 1,)) + opening.salt[1:]
        altered_proof = _replace_proof_opening(
            proof,
            0,
            replace(opening, salt=bad_salt),
        )
        artifacts = replace(self.candidate.public_artifacts, proof=altered_proof)
        candidate = replace(
            self.candidate,
            public_artifacts=artifacts,
            claimed_proof_id=altered_proof.identity,
            claimed_target_decision="Reject",
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-COMMITMENT-025")

    def test_profile_mismatch_precedes_transcript_or_proof_work(self) -> None:
        unsupported_profile = replace(EXACT_PROFILE, name="alternate-fri-profile")
        inputs = replace(
            self.candidate.public_artifacts.public_inputs,
            profile=unsupported_profile,
        )
        artifacts = replace(self.candidate.public_artifacts, public_inputs=inputs)
        candidate = replace(self.candidate, public_artifacts=artifacts)
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-019")

    def test_occurrence_map_mismatch_is_refused(self) -> None:
        occurrence_map = list(self.candidate.occurrence_map)
        occurrence_map[0] = replace(
            occurrence_map[0],
            initial_domain_index=(occurrence_map[0].initial_domain_index + 1) % 16,
        )
        candidate = replace(self.candidate, occurrence_map=tuple(occurrence_map))
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-034")

    def test_stale_source_target_and_trace_bindings_are_distinct(self) -> None:
        stale_candidates = (
            (
                replace(
                    self.candidate,
                    claimed_source_trace_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-021",
            ),
            (
                replace(
                    self.candidate,
                    claimed_public_inputs_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-022",
            ),
            (
                replace(
                    self.candidate,
                    claimed_proof_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-023",
            ),
            (
                replace(
                    self.candidate,
                    claimed_target_trace_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-025",
            ),
        )
        for candidate, code in stale_candidates:
            with self.subTest(code=code):
                admission = check_native_to_committed_execution(candidate)
                self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(admission.result.code, code)

    def test_wrong_construction_subject_is_a_kind_mismatch(self) -> None:
        candidate = replace(
            self.candidate,
            commitment_compilation_declaration_id=EXACT_PROFILE.identity,
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-024")

    def test_stale_decision_claim_is_refused(self) -> None:
        candidate = replace(
            self.candidate,
            claimed_source_decision="Reject",
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-029")

    def test_generation_resource_exhaustion_is_typed_and_atomic(self) -> None:
        limits = replace(DEFAULT_VALIDATION_LIMITS, field_operations=0)
        admission = generate_honest_native_to_committed_execution(
            primary_private_generation_material(),
            primary_public_inputs(),
            limits,
        )
        self.assertIs(
            admission.result.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-RESOURCE-008")
        self.assertIsNone(admission.checked_execution)

    def test_wrong_candidate_and_mutable_counter_are_malformed(self) -> None:
        wrong_candidate = check_native_to_committed_execution(object())
        self.assertIs(wrong_candidate.result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(wrong_candidate.result.code, "FRI-IOR-GENERATION-017")
        wrong_limits = check_native_to_committed_execution(
            self.candidate,
            ResourceCounter(),
        )
        self.assertIs(wrong_limits.result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(wrong_limits.result.code, "FRI-IOR-GENERATION-018")


if __name__ == "__main__":
    unittest.main()
