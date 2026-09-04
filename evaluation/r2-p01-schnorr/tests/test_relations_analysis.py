from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import pickle
import sys
import unittest
from unittest.mock import patch


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = MODEL_ROOT.parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from p01model.analysis import (  # noqa: E402
    EXPECTED_ACCEPTING_TRANSCRIPT_COUNT,
    EXPECTED_CONDITIONAL_DISTRIBUTION_COUNT,
    EXPECTED_TOTAL_SAMPLES_PER_SIDE,
    EXPECTED_UNORDERED_DISTINCT_CHALLENGE_FORK_COUNT,
    ApplicabilityClaim,
    FiniteForkExtraction,
    SchnorrTranscript,
    TranscriptFork,
    check_accepting_transcript,
    exhaustive_shvzk_distribution_equality,
    exhaustive_special_soundness,
    extract_special_soundness_fork,
    honest_transcript,
    probe_analysis_applicability,
)
from p01model.execution import (  # noqa: E402
    CheckedPublicExecution,
    Disposition,
    FreshChallengeBinding,
    PortableExecutionRecord,
    PublicInvocation,
    PublicReplayRequest,
    build_evaluator_basis,
    build_portable_execution,
    export_checked_public_statement,
    issue_relations_checked_statement,
    public_trace_value,
    qualify_public_execution,
)
from p01model.provenance import (  # noqa: E402
    ArtifactContentId,
    EvidenceRecordId,
    artifact_content_id,
)
from p01model.relations import (  # noqa: E402
    CheckedPublicExecutionStatement,
    CheckedRelationSatisfaction,
    PrivateWitnessOccurrenceRef,
    RelationSatisfactionOwner,
    SchnorrRelationInstance,
    admit_witness_assignment,
    canonical_schnorr_relation,
    check_relation_execution_grounding,
    check_relation_honest_prover_correspondence,
    check_relation_satisfaction,
    relation_execution_grounding_candidate,
    relation_honest_prover_candidate,
)
from p01model.semantic import (  # noqa: E402
    CHALLENGE,
    COMMITMENT,
    RESPONSE,
    AlgebraProfile,
    canonical_core,
    canonical_honest_prover_contract,
    canonical_transcript_construction,
    honest_witness_precondition_contract_id,
    make_fresh_protocol,
    make_fs_protocol,
)
from p01model.terms import Outcome, Result  # noqa: E402


class ResultAssertions(unittest.TestCase):
    def assert_result(
        self,
        checked: object,
        outcome: Outcome,
        *,
        code: str | None = None,
    ) -> Result:
        self.assertIsInstance(checked, Result)
        assert isinstance(checked, Result)
        self.assertIs(checked.outcome, outcome)
        if code is not None:
            self.assertEqual(checked.code, code)
        return checked


class P01Fixture(ResultAssertions):
    @classmethod
    def setUpClass(cls) -> None:
        cls.profile = AlgebraProfile(p=23, q=11, generator=2, challenge_size=8)
        cls.core = canonical_core(cls.profile)
        cls.construction = canonical_transcript_construction(
            cls.core,
            cls.profile,
        )
        cls.fresh_protocol, cls.fresh = make_fresh_protocol(
            cls.core,
            cls.profile,
        )
        cls.fs_protocol = make_fs_protocol(
            cls.core,
            cls.construction,
            cls.profile,
        )
        cls.relation = canonical_schnorr_relation(cls.profile)
        cls.instance = SchnorrRelationInstance(cls.relation.identity, 13)

        cls.public_fixture_id = artifact_content_id(
            (
                REPO_ROOT
                / "evaluation/r2-p01-schnorr/cases/public-inputs.json"
            ).read_bytes()
        )
        cls.evaluator_basis = build_evaluator_basis(
            REPO_ROOT,
            (cls.fresh_protocol.identity, cls.fs_protocol.identity),
        )

        fresh_source = artifact_content_id(b"p01-test-fresh-support-point\n")
        fresh_binding = FreshChallengeBinding(
            cls.core.identity,
            cls.fresh_protocol.identity,
            CHALLENGE,
            3,
            fresh_source,
        )
        fresh_invocation = PublicInvocation(
            cls.profile.identity,
            cls.core.identity,
            cls.fresh_protocol.identity,
            13,
            None,
            fresh_binding,
        )
        fresh_record = build_portable_execution(
            fresh_invocation,
            16,
            3,
            cls.fresh_protocol,
            cls.profile,
            cls.core,
            fresh=cls.fresh,
        )
        if isinstance(fresh_record, Result):
            raise AssertionError(f"Fresh fixture did not execute: {fresh_record.term()}")
        fresh_request = PublicReplayRequest(
            fresh_invocation,
            fresh_record,
            cls.evaluator_basis.identity,
            cls.public_fixture_id,
        )
        fresh_checked = qualify_public_execution(
            fresh_request,
            cls.evaluator_basis,
            cls.fresh_protocol,
            cls.profile,
            cls.core,
            fresh=cls.fresh,
        )
        if isinstance(fresh_checked, Result):
            raise AssertionError(
                f"Fresh fixture did not qualify: {fresh_checked.term()}"
            )

        fs_invocation = PublicInvocation(
            cls.profile.identity,
            cls.core.identity,
            cls.fs_protocol.identity,
            13,
            "zkc/p01/test-session/alpha",
            None,
        )
        fs_record = build_portable_execution(
            fs_invocation,
            16,
            2,
            cls.fs_protocol,
            cls.profile,
            cls.core,
            construction=cls.construction,
        )
        if isinstance(fs_record, Result):
            raise AssertionError(f"FS fixture did not execute: {fs_record.term()}")
        fs_request = PublicReplayRequest(
            fs_invocation,
            fs_record,
            cls.evaluator_basis.identity,
            cls.public_fixture_id,
        )
        fs_checked = qualify_public_execution(
            fs_request,
            cls.evaluator_basis,
            cls.fs_protocol,
            cls.profile,
            cls.core,
            construction=cls.construction,
        )
        if isinstance(fs_checked, Result):
            raise AssertionError(f"FS fixture did not qualify: {fs_checked.term()}")

        cls.fresh_checked: CheckedPublicExecution = fresh_checked
        cls.fs_checked: CheckedPublicExecution = fs_checked

    def transcript_from_execution(
        self,
        checked: CheckedPublicExecution,
    ) -> SchnorrTranscript:
        commitment = public_trace_value(checked.record, COMMITMENT)
        response = public_trace_value(checked.record, RESPONSE)
        self.assertNotIsInstance(commitment, Result)
        self.assertNotIsInstance(response, Result)
        assert isinstance(commitment, int)
        assert isinstance(response, int)
        return SchnorrTranscript(
            instance_id=self.instance.identity,
            statement=checked.invocation.statement,
            commitment=commitment,
            challenge=checked.record.challenge_receipt.challenge,
            response=response,
        )


class RelationAuthorityTest(P01Fixture):
    def test_owner_local_assignments_and_results_are_nonportable(self) -> None:
        owner = RelationSatisfactionOwner()
        assignment = owner.allocate_witness(self.instance, 7)
        reference = assignment.local_occurrence
        satisfaction = check_relation_satisfaction(
            assignment,
            self.instance,
            self.relation,
            self.profile,
            owner=owner,
        )

        self.assertIsInstance(reference, PrivateWitnessOccurrenceRef)
        self.assertIsInstance(satisfaction, CheckedRelationSatisfaction)
        for local_value in (owner, reference, assignment, satisfaction):
            with self.subTest(local_type=type(local_value).__name__):
                self.assertFalse(hasattr(local_value, "term"))
                self.assertFalse(hasattr(local_value, "identity"))
                with self.assertRaises(TypeError):
                    pickle.dumps(local_value)
        self.assertNotIn("secret_scalar=7", repr(assignment))

    def test_satisfaction_authorizes_only_the_exact_occurrence_and_owner(self) -> None:
        owner = RelationSatisfactionOwner()
        foreign_owner = RelationSatisfactionOwner()
        assignment = owner.allocate_witness(self.instance, 7)
        same_scalar_other_occurrence = owner.allocate_witness(self.instance, 7)
        foreign_assignment = foreign_owner.allocate_witness(self.instance, 7)

        satisfaction = check_relation_satisfaction(
            assignment,
            self.instance,
            self.relation,
            self.profile,
            owner=owner,
        )
        self.assertIsInstance(satisfaction, CheckedRelationSatisfaction)
        assert isinstance(satisfaction, CheckedRelationSatisfaction)
        self.assertIs(satisfaction.outcome, Outcome.AFFIRMATIVE)
        authorization = {
            "precondition_contract_id": honest_witness_precondition_contract_id(
                self.profile
            ),
            "public_statement": self.instance.public_statement,
        }
        self.assertTrue(
            satisfaction.authorizes_assignment(
                witness_assignment=assignment,
                owner=owner,
                **authorization,
            )
        )
        self.assertIsNot(
            assignment.local_occurrence,
            same_scalar_other_occurrence.local_occurrence,
        )
        self.assertFalse(
            satisfaction.authorizes_assignment(
                witness_assignment=same_scalar_other_occurrence,
                owner=owner,
                **authorization,
            )
        )
        self.assertFalse(
            satisfaction.authorizes_assignment(
                witness_assignment=foreign_assignment,
                owner=foreign_owner,
                **authorization,
            )
        )

    def test_missing_and_cross_owner_authority_are_refused(self) -> None:
        owner = RelationSatisfactionOwner()
        foreign_owner = RelationSatisfactionOwner()
        assignment = owner.allocate_witness(self.instance, 7)

        missing = admit_witness_assignment(
            assignment,
            self.instance,
            self.relation,
            self.profile,
        )
        foreign = check_relation_satisfaction(
            assignment,
            self.instance,
            self.relation,
            self.profile,
            owner=foreign_owner,
        )
        self.assert_result(missing, Outcome.REFUSED, code="P01-WIT-006")
        self.assert_result(foreign, Outcome.REFUSED, code="P01-WIT-006")

    def test_authorized_correct_and_wrong_witnesses_remain_distinct_judgments(
        self,
    ) -> None:
        owner = RelationSatisfactionOwner()
        correct = owner.allocate_witness(self.instance, 7)
        wrong = owner.allocate_witness(self.instance, 8)

        satisfying = check_relation_satisfaction(
            correct,
            self.instance,
            self.relation,
            self.profile,
            owner=owner,
        )
        nonsatisfying = check_relation_satisfaction(
            wrong,
            self.instance,
            self.relation,
            self.profile,
            owner=owner,
        )
        self.assertIsInstance(satisfying, CheckedRelationSatisfaction)
        self.assertIsInstance(nonsatisfying, CheckedRelationSatisfaction)
        assert isinstance(satisfying, CheckedRelationSatisfaction)
        assert isinstance(nonsatisfying, CheckedRelationSatisfaction)
        self.assertIs(satisfying.outcome, Outcome.AFFIRMATIVE)
        self.assertEqual(satisfying.code, "P01-SAT-OK")
        self.assertIs(nonsatisfying.outcome, Outcome.SEMANTIC_NEGATIVE)
        self.assertEqual(nonsatisfying.code, "P01-SAT-001")
        self.assertFalse(
            nonsatisfying.authorizes_assignment(
                witness_assignment=wrong,
                owner=owner,
                precondition_contract_id=honest_witness_precondition_contract_id(
                    self.profile
                ),
                public_statement=self.instance.public_statement,
            )
        )


class RelationPublicGroundingTest(P01Fixture):
    def test_fresh_and_fs_grounding_uses_execution_issued_statement_views(self) -> None:
        for checked in (self.fresh_checked, self.fs_checked):
            with self.subTest(realization=checked.protocol.realization_kind.value):
                statement = issue_relations_checked_statement(checked)
                self.assertIsInstance(statement, CheckedPublicExecutionStatement)
                assert isinstance(statement, CheckedPublicExecutionStatement)
                self.assertIsInstance(
                    statement.public_execution_qualification_id,
                    EvidenceRecordId,
                )
                self.assertIsInstance(
                    statement.public_execution_record_id,
                    ArtifactContentId,
                )
                self.assertIsInstance(statement.source_event_id, ArtifactContentId)
                self.assertEqual(statement.protocol_id, checked.protocol.identity)
                self.assertEqual(statement.core_id, self.core.identity)
                self.assertEqual(statement.evaluation_profile_id, self.profile.identity)

                grounding = relation_execution_grounding_candidate(
                    self.instance,
                    self.relation,
                    statement,
                )
                grounded = check_relation_execution_grounding(
                    grounding,
                    self.instance,
                    self.relation,
                    statement,
                    self.profile,
                )
                self.assert_result(
                    grounded,
                    Outcome.AFFIRMATIVE,
                    code="P01-GRD-SHAPE-OK",
                )

    def test_public_export_or_caller_construction_cannot_mint_grounding_authority(
        self,
    ) -> None:
        checked = self.fresh_checked
        issued = issue_relations_checked_statement(checked)
        exported = export_checked_public_statement(checked)
        self.assertIsInstance(issued, CheckedPublicExecutionStatement)
        self.assertNotIsInstance(exported, Result)
        assert isinstance(issued, CheckedPublicExecutionStatement)

        grounding = relation_execution_grounding_candidate(
            self.instance,
            self.relation,
            issued,
        )
        rejected_export = check_relation_execution_grounding(
            grounding,
            self.instance,
            self.relation,
            exported,  # type: ignore[arg-type]
            self.profile,
        )
        self.assert_result(rejected_export, Outcome.MALFORMED, code="P01-GRD-001")

        with self.assertRaises(TypeError):
            CheckedPublicExecutionStatement(
                public_execution_qualification_id=checked.identity,
                public_execution_record_id=checked.record.identity,
                protocol_id=checked.protocol.identity,
                core_id=checked.core.identity,
                evaluation_profile_id=checked.profile.identity,
                occurrence=issued.occurrence,
                value=issued.value,
                source_event_id=issued.source_event_id,
                _seal=object(),
            )

    def test_checked_statement_rejects_cross_lane_identity_substitution(self) -> None:
        substitutions = (
            ("public_execution_qualification_id", self.fresh_checked.record.identity),
            ("public_execution_record_id", self.fresh_checked.identity),
            ("source_event_id", self.fresh_checked.identity),
        )
        for attribute, wrong_lane_id in substitutions:
            with self.subTest(attribute=attribute):
                statement = issue_relations_checked_statement(self.fresh_checked)
                self.assertIsInstance(statement, CheckedPublicExecutionStatement)
                assert isinstance(statement, CheckedPublicExecutionStatement)
                object.__setattr__(statement, attribute, wrong_lane_id)
                grounding = relation_execution_grounding_candidate(
                    self.instance,
                    self.relation,
                    statement,
                )
                rejected = check_relation_execution_grounding(
                    grounding,
                    self.instance,
                    self.relation,
                    statement,
                    self.profile,
                )
                self.assert_result(
                    rejected,
                    Outcome.MALFORMED,
                    code="P01-GRD-002",
                )

    def test_relation_honest_prover_correspondence_is_exact(self) -> None:
        honest_contract = canonical_honest_prover_contract(self.core, self.profile)
        correspondence = relation_honest_prover_candidate(
            self.relation,
            self.core,
            honest_contract,
            self.profile,
        )
        checked = check_relation_honest_prover_correspondence(
            correspondence,
            self.relation,
            self.core,
            honest_contract,
            self.profile,
        )
        self.assert_result(checked, Outcome.AFFIRMATIVE, code="P01-RHC-OK")

        wrong = replace(correspondence, witness_source="different-local-source")
        rejected = check_relation_honest_prover_correspondence(
            wrong,
            self.relation,
            self.core,
            honest_contract,
            self.profile,
        )
        self.assert_result(rejected, Outcome.MISMATCH, code="P01-RHC-004")


class FiniteAnalysisTest(P01Fixture):
    def test_actual_fresh_and_fs_public_transcripts_are_accepting(self) -> None:
        expected_challenges = (3, 6)
        expected_responses = (3, 2)
        for checked, challenge, response in zip(
            (self.fresh_checked, self.fs_checked),
            expected_challenges,
            expected_responses,
            strict=True,
        ):
            with self.subTest(realization=checked.protocol.realization_kind.value):
                self.assertIsInstance(checked.record, PortableExecutionRecord)
                self.assertIs(
                    checked.record.verifier_decision.disposition,
                    Disposition.ACCEPT,
                )
                transcript = self.transcript_from_execution(checked)
                self.assertEqual(transcript.challenge, challenge)
                self.assertEqual(transcript.response, response)
                accepted = check_accepting_transcript(
                    transcript,
                    self.instance,
                    self.relation,
                    self.profile,
                )
                self.assert_result(
                    accepted,
                    Outcome.AFFIRMATIVE,
                    code="P01-TRN-OK",
                )

    def test_fork_extraction_delegates_candidate_validation_to_relations(self) -> None:
        left = self.transcript_from_execution(self.fresh_checked)
        right = honest_transcript(self.instance, 7, 4, 4, self.profile)
        owner = RelationSatisfactionOwner()

        with patch(
            "p01model.analysis.check_relation_satisfaction",
            wraps=check_relation_satisfaction,
        ) as relations_check:
            extraction = extract_special_soundness_fork(
                TranscriptFork(left, right),
                self.instance,
                self.relation,
                self.profile,
                satisfaction_owner=owner,
            )

        self.assertIsInstance(extraction, FiniteForkExtraction)
        assert isinstance(extraction, FiniteForkExtraction)
        self.assertEqual(extraction.extracted_scalar, 7)
        self.assertIsInstance(
            extraction.relation_satisfaction,
            CheckedRelationSatisfaction,
        )
        self.assertIs(
            extraction.relation_satisfaction.outcome,
            Outcome.AFFIRMATIVE,
        )
        relations_check.assert_called_once()
        self.assertIs(relations_check.call_args.kwargs["owner"], owner)
        self.assertFalse(hasattr(extraction, "term"))
        self.assertFalse(hasattr(extraction, "identity"))

    def test_equal_challenge_fork_is_rejected_before_extraction(self) -> None:
        left = self.transcript_from_execution(self.fresh_checked)
        rejected = extract_special_soundness_fork(
            TranscriptFork(left, left),
            self.instance,
            self.relation,
            self.profile,
        )

        checked = self.assert_result(
            rejected,
            Outcome.SEMANTIC_NEGATIVE,
            code="P01-SS-006",
        )
        self.assertEqual(
            checked.boundary,
            "analysis:finite-special-soundness:distinct-challenges",
        )

    def test_exhaustive_coverage_has_the_frozen_exact_cardinalities(self) -> None:
        special_soundness = exhaustive_special_soundness(self.profile)
        shvzk = exhaustive_shvzk_distribution_equality(self.profile)
        self.assert_result(
            special_soundness,
            Outcome.AFFIRMATIVE,
            code="P01-SS-ENUM-OK",
        )
        self.assert_result(shvzk, Outcome.AFFIRMATIVE, code="P01-SHVZK-OK")
        self.assertEqual(
            special_soundness.evidence["accepting_transcript_count"],
            EXPECTED_ACCEPTING_TRANSCRIPT_COUNT,
        )
        self.assertEqual(EXPECTED_ACCEPTING_TRANSCRIPT_COUNT, 968)
        self.assertEqual(
            special_soundness.evidence[
                "unordered_distinct_challenge_fork_count"
            ],
            EXPECTED_UNORDERED_DISTINCT_CHALLENGE_FORK_COUNT,
        )
        self.assertEqual(EXPECTED_UNORDERED_DISTINCT_CHALLENGE_FORK_COUNT, 3388)
        self.assertEqual(
            shvzk.evidence["conditional_distribution_count"],
            EXPECTED_CONDITIONAL_DISTRIBUTION_COUNT,
        )
        self.assertEqual(EXPECTED_CONDITIONAL_DISTRIBUTION_COUNT, 88)
        self.assertEqual(
            shvzk.evidence["total_samples_per_side"],
            EXPECTED_TOTAL_SAMPLES_PER_SIDE,
        )
        self.assertEqual(EXPECTED_TOTAL_SAMPLES_PER_SIDE, 968)

    def test_all_six_theorem_promotions_are_refused(self) -> None:
        expected_codes = {
            ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS: "P01-APP-101",
            ApplicabilityClaim.GENERAL_SHVZK: "P01-APP-102",
            ApplicabilityClaim.GENERAL_HVZK: "P01-APP-103",
            ApplicabilityClaim.KNOWLEDGE_SOUNDNESS: "P01-APP-104",
            ApplicabilityClaim.FIAT_SHAMIR_ROM: "P01-APP-105",
            ApplicabilityClaim.FIAT_SHAMIR_QROM: "P01-APP-106",
        }
        self.assertEqual(len(expected_codes), 6)
        for claim, code in expected_codes.items():
            with self.subTest(claim=claim.value):
                refused = probe_analysis_applicability(claim, self.profile)
                checked = self.assert_result(
                    refused,
                    Outcome.REFUSED,
                    code=code,
                )
                self.assertTrue(checked.evidence["missing_capability"])
                self.assertEqual(
                    checked.evidence["non_promotion_law"],
                    "finite evidence cannot author theorem applicability",
                )


if __name__ == "__main__":
    unittest.main()
