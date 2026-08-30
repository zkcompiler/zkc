"""Focused Relations and Analysis tests for the exact classical FRI control."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.classical import (  # noqa: E402
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_NATIVE_CORE,
    build_honest_classical_case,
    form_classical_public_environment,
    verify_native_trace,
)
from friiormodel.classical_analysis import (  # noqa: E402
    AnalysisEvaluationStatus,
    BcsShortcutRequest,
    CanonicalRational,
    ClassicalPropertyFamily,
    DIRECT_FRI_SOURCE_VALIDATION,
    DIRECT_FRI_THEOREM_SCHEMA,
    QuantitativeBoundClassification,
    TheoremApplicabilityStatus,
    TheoremSourceValidation,
    TheoremTruthStatus,
    check_algorithm_one_structural_correspondence,
    evaluate_selected_goldilocks_direct_fri_bound,
    form_direct_fri_quantitative_question,
    form_restricted_state_restoration_question,
    form_round_by_round_soundness_question,
    refuse_bcs_commitment_shortcut,
    refuse_question_as_property_transport,
)
from friiormodel.classical_relations import (  # noqa: E402
    EXACT_RS_PROXIMITY_RELATION,
    ClassicalRelationStatementOccurrence,
    OuterRelationInferenceRequest,
    OuterRelationPremise,
    ProximityEvaluationStatus,
    check_classical_relation_grounding,
    check_construction_relation_view,
    check_initial_oracle_grounding,
    form_exact_rs_relation_instance_and_binding,
    infer_outer_computation_relation,
)
from friiormodel.oracle_construction import (  # noqa: E402
    EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION,
    admit_oracle_commitment_construction,
    check_oracle_commitment_run,
    form_oracle_commitment_advice,
)
from friiormodel.terms import OutcomeClass, semantic_id  # noqa: E402


class ExactClassicalRelationsAnalysisTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = build_honest_classical_case()
        cls.statement = ClassicalRelationStatementOccurrence(
            cls.case.native_trace.public_environment,
        )
        cls.instance, cls.binding = form_exact_rs_relation_instance_and_binding(
            cls.statement,
            cls.case.native_trace.oracles[0],
        )
        cls.initial_grounding_admission = check_initial_oracle_grounding(
            cls.instance,
            cls.binding,
            cls.case.native_trace,
        )
        construction_admission = admit_oracle_commitment_construction(
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION
        )
        if construction_admission.capability is None:
            raise AssertionError(construction_admission.result.to_term())
        cls.construction_admission = construction_admission
        cls.capability = construction_admission.capability
        advice = form_oracle_commitment_advice(
            cls.capability,
            cls.case,
            cls.case.owner_salts,
        )
        run_admission = check_oracle_commitment_run(
            cls.capability,
            cls.case,
            advice,
        )
        if run_admission.receipt is None:
            raise AssertionError(run_admission.result.to_term())
        cls.run_admission = run_admission
        cls.run_receipt = run_admission.receipt

    def test_exact_rs_relation_and_public_statement_are_closed(self) -> None:
        relation = EXACT_RS_PROXIMITY_RELATION
        self.assertEqual(relation.field_size, 18446744069414584321)
        self.assertEqual(relation.initial_domain_order, 64)
        self.assertEqual(relation.degree_bound_exclusive, 8)
        self.assertEqual(
            (
                relation.distance_threshold_numerator,
                relation.distance_threshold_denominator,
            ),
            (1, 2),
        )
        self.assertEqual(
            self.statement.canonical_statement,
            self.case.fresh_run.public_inputs.statement,
        )
        self.assertEqual(
            self.statement.public_environment_id,
            self.case.native_trace.public_environment.identity,
        )
        self.assertEqual(
            self.statement.statement_coordinate_id,
            self.case.native_trace.public_environment.statement_coordinate_id,
        )
        self.assertEqual(
            self.instance.to_term()["satisfaction_status"],
            ProximityEvaluationStatus.NOT_EVALUATED.value,
        )

    def test_initial_oracle_grounding_is_exact_but_not_proximity(self) -> None:
        admission = self.initial_grounding_admission
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIsNotNone(admission.checked)
        self.assertFalse(admission.result.evidence["establishes_proximity"])
        self.assertEqual(
            admission.result.evidence["durable_required_view"],
            "PirOwnedPurposeSpecificConfidentialOracleView",
        )
        self.assertFalse(admission.result.evidence["durable_promotion_ready"])
        assert admission.checked is not None
        self.assertEqual(
            admission.checked.initial_oracle_material_id,
            self.case.native_trace.oracles[0].identity,
        )
        self.assertEqual(
            admission.checked.public_environment_id,
            self.case.native_trace.public_environment.identity,
        )

        wrong_trace = replace(
            self.case.native_trace,
            oracles=(
                replace(
                    self.case.native_trace.oracles[0],
                    values=tuple(
                        reversed(self.case.native_trace.oracles[0].values)
                    ),
                ),
            )
            + self.case.native_trace.oracles[1:],
        )
        wrong = check_initial_oracle_grounding(
            self.instance,
            self.binding,
            wrong_trace,
        )
        self.assertIs(wrong.result.outcome, OutcomeClass.REFUSED)
        self.assertIsNone(wrong.checked)

    def test_grounding_refuses_authored_statement_or_context_substitution(self) -> None:
        original = self.case.native_trace.public_environment
        substituted_environments = (
            form_classical_public_environment(
                {"claim": "different-statement"},
                {"application": "zkc-exact-classical-fri-control", "version": 1},
            ),
            form_classical_public_environment(
                {"claim": "degree-below-eight-on-goldilocks-l0", "public_instance": 7},
                {"application": "different-context", "version": 1},
            ),
        )
        for environment in substituted_environments:
            with self.subTest(environment_id=str(environment.identity)):
                self.assertNotEqual(environment.identity, original.identity)
                statement = ClassicalRelationStatementOccurrence(environment)
                instance, binding = form_exact_rs_relation_instance_and_binding(
                    statement,
                    self.case.native_trace.oracles[0],
                )
                admission = check_initial_oracle_grounding(
                    instance,
                    binding,
                    self.case.native_trace,
                )
                self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(
                    admission.result.code,
                    "FRI-IOR-CLASSICAL-RELATION-013",
                )
                self.assertIsNone(admission.checked)

    def test_live_capability_attenuates_to_three_root_twelve_occurrence_view(
        self,
    ) -> None:
        admission = check_construction_relation_view(self.capability)
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIsNotNone(admission.view)
        assert admission.view is not None
        self.assertEqual(admission.view.public_environment_coordinates, 2)
        self.assertEqual(admission.view.root_publications, 3)
        self.assertEqual(admission.view.query_draws, 4)
        self.assertEqual(admission.view.logical_query_occurrences, 12)
        self.assertEqual(
            admission.view.construction_id,
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION.identity,
        )
        self.assertNotIn("capability", admission.view.to_term())
        self.assertNotIn("result_ref", admission.view.to_term())

    def test_declaration_and_semantic_id_are_not_live_construction_authority(
        self,
    ) -> None:
        for wrong_kind in (
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION,
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION.identity,
        ):
            admission = check_construction_relation_view(wrong_kind)
            self.assertIs(admission.result.outcome, OutcomeClass.KIND_MISMATCH)
            self.assertIsNone(admission.view)

    def test_one_run_receipt_is_inert_and_refused_in_stable_slot(self) -> None:
        self.assertIs(
            self.run_admission.result.outcome,
            OutcomeClass.AFFIRMATIVE,
        )
        self.assertEqual(
            self.run_receipt.construction_id,
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION.identity,
        )
        receipt_term = self.run_receipt.to_term()
        self.assertEqual(
            receipt_term["semantic_receipt"]["conclusion"],
            "ThisExecutionForwardMapped",
        )
        self.assertNotIn("authority", receipt_term)
        self.assertNotIn("capability", receipt_term)
        view = check_construction_relation_view(self.run_receipt)
        self.assertIs(view.result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertIsNone(view.view)

    def test_acceptance_leaves_proximity_and_outer_relation_unevaluated(self) -> None:
        native = verify_native_trace(self.case.native_trace)
        self.assertIs(native.outcome, OutcomeClass.AFFIRMATIVE)
        initial = self.initial_grounding_admission.checked
        assert initial is not None
        grounding = check_classical_relation_grounding(
            self.instance,
            self.binding,
            self.case.native_trace,
            initial,
            self.capability,
        )
        self.assertIs(grounding.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertFalse(grounding.result.evidence["establishes_proximity"])
        self.assertFalse(
            grounding.result.evidence["establishes_outer_computation_relation"]
        )
        assert grounding.checked is not None
        residual = grounding.checked.terminal_residual
        self.assertIs(
            residual.proximity_status,
            ProximityEvaluationStatus.NOT_EVALUATED,
        )
        outer_id = semantic_id(
            "outer-computation-relation",
            "fri-ior.test.outer-relation.v1",
            {"name": "not-established-by-fri-acceptance"},
        )
        for premise in OuterRelationPremise:
            result = infer_outer_computation_relation(
                OuterRelationInferenceRequest(residual, outer_id, premise)
            )
            self.assertIs(result.outcome, OutcomeClass.REFUSED)

    def test_algorithm_one_shape_is_not_theorem_truth_or_applicability(self) -> None:
        admission = check_algorithm_one_structural_correspondence(
            EXACT_CLASSICAL_FRI_PROFILE,
            EXACT_CLASSICAL_NATIVE_CORE,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIsNotNone(admission.checked)
        self.assertIsNone(admission.result.evidence["theorem_true"])
        self.assertIsNone(admission.result.evidence["theorem_applicable"])
        self.assertIsNone(admission.result.evidence["property_established"])
        assert admission.checked is not None
        self.assertEqual(admission.checked.fold_count, 3)
        self.assertEqual(admission.checked.committed_oracle_layers, 3)
        self.assertEqual(admission.checked.logical_layer_query_occurrences, 12)

    def _form_analysis_questions(self):
        correspondence = check_algorithm_one_structural_correspondence(
            EXACT_CLASSICAL_FRI_PROFILE,
            EXACT_CLASSICAL_NATIVE_CORE,
        ).checked
        assert correspondence is not None
        round_by_round = form_round_by_round_soundness_question(
            EXACT_CLASSICAL_FRI_PROFILE,
            EXACT_CLASSICAL_NATIVE_CORE.identity,
            self.instance,
            self.binding,
            correspondence,
        )
        restoration = form_restricted_state_restoration_question(
            round_by_round,
            branch_extension_budget=8,
        )
        return correspondence, round_by_round, restoration

    def test_soundness_families_are_separate_unevaluated_questions(self) -> None:
        _, round_by_round, restoration = self._form_analysis_questions()
        self.assertIs(
            round_by_round.family,
            ClassicalPropertyFamily.ROUND_BY_ROUND_SOUNDNESS,
        )
        self.assertIs(
            restoration.family,
            ClassicalPropertyFamily.RESTRICTED_STATE_RESTORATION_SOUNDNESS,
        )
        self.assertIs(
            round_by_round.evaluation_status,
            AnalysisEvaluationStatus.NOT_EVALUATED,
        )
        self.assertIs(
            restoration.evaluation_status,
            AnalysisEvaluationStatus.NOT_EVALUATED,
        )
        self.assertNotEqual(round_by_round.identity, restoration.identity)
        for candidate in (round_by_round, restoration):
            self.assertEqual(candidate.to_term()["catalog_status"], "CandidateQuestion")
            self.assertFalse(candidate.to_term()["durable_promotion_ready"])
        self.assertIs(
            refuse_question_as_property_transport(round_by_round, restoration).outcome,
            OutcomeClass.REFUSED,
        )

    def test_direct_fri_substitution_is_nonvacuous_without_theorem_claims(
        self,
    ) -> None:
        correspondence, round_by_round, _ = self._form_analysis_questions()
        question = form_direct_fri_quantitative_question(
            round_by_round,
            correspondence,
        )
        evaluation, result = evaluate_selected_goldilocks_direct_fri_bound(question)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIs(
            evaluation.classification,
            QuantitativeBoundClassification.NONVACUOUS,
        )
        self.assertEqual(evaluation.rate, CanonicalRational(1, 8))
        self.assertEqual(evaluation.johnson_slack_eta, CanonicalRational(1, 20))
        self.assertEqual(evaluation.distance, CanonicalRational(1, 2))
        self.assertEqual(evaluation.theorem_m, 3)
        self.assertEqual(evaluation.query_repetitions, 4)
        self.assertEqual(evaluation.second_term, CanonicalRational(1, 16))
        self.assertEqual(
            evaluation.selected_upper_bound,
            CanonicalRational(1, 16),
        )
        self.assertEqual(evaluation.dominant_term, "repetition-term")
        self.assertEqual(
            evaluation.first_term_squared,
            CanonicalRational(
                355584218417856512,
                3062541300862339246411675480114971279369,
            ),
        )
        self.assertTrue(evaluation.eta_range_condition_holds)
        self.assertTrue(evaluation.delta_range_condition_holds)
        self.assertTrue(evaluation.standing_k_at_most_n_over_two)
        self.assertIs(
            evaluation.theorem_truth_status,
            TheoremTruthStatus.NOT_ESTABLISHED,
        )
        self.assertIs(
            evaluation.theorem_applicability_status,
            TheoremApplicabilityStatus.NOT_EVALUATED,
        )
        self.assertIsNone(result.evidence["theorem_true"])
        self.assertIsNone(result.evidence["theorem_applicable"])
        self.assertIsNone(result.evidence["property_established"])

    def test_source_validation_is_distinct_from_theorem_schema_and_truth(self) -> None:
        schema_id = DIRECT_FRI_THEOREM_SCHEMA.identity
        self.assertEqual(
            DIRECT_FRI_SOURCE_VALIDATION.theorem_schema_id,
            schema_id,
        )
        self.assertNotIn("artifact_digest", DIRECT_FRI_THEOREM_SCHEMA.to_term())
        rotated = replace(
            DIRECT_FRI_SOURCE_VALIDATION,
            artifact_digest="0" * 64,
        )
        self.assertEqual(rotated.theorem_schema_id, schema_id)
        self.assertNotEqual(rotated.identity, DIRECT_FRI_SOURCE_VALIDATION.identity)
        self.assertIsInstance(rotated, TheoremSourceValidation)

    def test_old_proximity_to_committed_soundness_shortcut_is_refused(self) -> None:
        request = BcsShortcutRequest(
            "NativeProximitySoundness",
            "CommittedInteractiveSoundness",
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION.identity,
        )
        result = refuse_bcs_commitment_shortcut(request)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertIn("restricted state-restoration", result.detail)


if __name__ == "__main__":
    unittest.main()
