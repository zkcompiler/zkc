"""Focused Relations and Analysis tests for the exact classical FRI control."""

from __future__ import annotations

import copy
from dataclasses import replace
import pickle
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.classical import (  # noqa: E402
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_NATIVE_CORE,
    EXACT_CLASSICAL_ORACLE_DECLARATIONS,
    GoldilocksElement,
    check_classical_strong_fiat_shamir_core,
    form_classical_public_environment,
    verify_committed_fiat_shamir,
    verify_native_trace,
)
from friiormodel.confidential_oracle import (  # noqa: E402
    admit_confidential_initial_oracle_disclosure_policy,
    build_causal_honest_classical_case,
    issue_confidential_initial_oracle_view,
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
    OracleMaterialAgreementOutcome,
    OuterRelationInferenceRequest,
    OuterRelationPremise,
    ProximityEvaluationStatus,
    check_classical_relation_grounding,
    check_construction_relation_view,
    check_initial_oracle_grounding,
    form_exact_initial_oracle_disclosure_policy,
    form_exact_rs_relation_instance_and_binding,
    infer_outer_computation_relation,
    issue_relation_initial_oracle_secret_assignment,
    oracle_material_question_id,
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
        cls.causal_case = build_causal_honest_classical_case()
        cls.case = cls.causal_case.case
        cls.statement = ClassicalRelationStatementOccurrence(
            cls.case.native_trace.public_environment,
        )
        cls.instance, cls.binding = form_exact_rs_relation_instance_and_binding(
            cls.statement,
        )
        cls.policy = form_exact_initial_oracle_disclosure_policy(
            cls.instance,
            cls.binding,
            cls.statement,
        )
        policy_admission = admit_confidential_initial_oracle_disclosure_policy(
            cls.policy
        )
        if policy_admission.capability is None:
            raise AssertionError(policy_admission.result.to_term())
        cls.policy_admission = policy_admission
        cls.policy_capability = policy_admission.capability
        view_admission = issue_confidential_initial_oracle_view(
            cls.causal_case.execution_authority,
            cls.policy_capability,
        )
        if view_admission.capability is None:
            raise AssertionError(view_admission.result.to_term())
        cls.view_admission = view_admission
        cls.view_capability = view_admission.capability
        cls.secret_capability = issue_relation_initial_oracle_secret_assignment(
            cls.instance,
            cls.binding,
            cls.statement,
            cls.causal_case.execution_authority,
            cls.case.native_trace.oracles[0].values,
        )
        cls.initial_grounding_admission = check_initial_oracle_grounding(
            cls.instance,
            cls.binding,
            cls.statement,
            cls.secret_capability,
            cls.view_capability,
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
        self.assertNotIn("satisfaction_status", self.instance.to_term())
        self.assertEqual(
            self.instance.public_statement,
            self.statement.canonical_statement,
        )
        for term in (self.instance.to_term(), self.binding.to_term()):
            rendered = repr(term)
            self.assertNotIn("initial_oracle_material_id", rendered)
            self.assertNotIn("initial_oracle_occurrence_id", rendered)
            self.assertNotIn(
                self.case.native_trace.oracles[0].identity.digest.hex(),
                rendered,
            )

    def test_instance_binding_and_question_identities_are_factorized(self) -> None:
        original_question = oracle_material_question_id(
            self.instance,
            self.binding,
            self.statement,
        )
        changed_statement_occurrence = ClassicalRelationStatementOccurrence(
            form_classical_public_environment(
                {"claim": "different-statement"},
                {
                    "application": "zkc-exact-classical-fri-control",
                    "version": 1,
                },
            )
        )
        changed_instance, changed_binding = (
            form_exact_rs_relation_instance_and_binding(
                changed_statement_occurrence,
            )
        )
        self.assertNotEqual(changed_instance.identity, self.instance.identity)
        self.assertEqual(changed_binding.identity, self.binding.identity)
        self.assertNotEqual(
            oracle_material_question_id(
                changed_instance,
                changed_binding,
                changed_statement_occurrence,
            ),
            original_question,
        )

        changed_context_occurrence = ClassicalRelationStatementOccurrence(
            form_classical_public_environment(
                {
                    "claim": "degree-below-eight-on-goldilocks-l0",
                    "public_instance": 7,
                },
                {"application": "different-context", "version": 1},
            )
        )
        changed_context_instance, changed_context_binding = (
            form_exact_rs_relation_instance_and_binding(
                changed_context_occurrence,
            )
        )
        self.assertEqual(changed_context_instance.identity, self.instance.identity)
        self.assertEqual(changed_context_binding.identity, self.binding.identity)
        self.assertNotEqual(
            oracle_material_question_id(
                changed_context_instance,
                changed_context_binding,
                changed_context_occurrence,
            ),
            original_question,
        )

        instance_term = self.instance.to_term()
        self.assertEqual(
            set(instance_term),
            {
                "interface_id",
                "public_values",
                "oracle_public_bindings",
                "phase_values",
            },
        )
        self.assertEqual(
            instance_term["public_values"]["statement"],
            self.statement.canonical_statement.hex(),
        )
        binding_rendered = repr(self.binding.to_term())
        for forbidden in (
            "relation_instance_id",
            "statement_occurrence_id",
            "public_environment_id",
            "statement_coordinate_id",
            "canonical_value",
        ):
            self.assertNotIn(forbidden, binding_rendered)

    def test_initial_oracle_grounding_is_causal_exact_but_not_proximity(self) -> None:
        admission = self.initial_grounding_admission
        self.assertIs(
            admission.result.outcome,
            OracleMaterialAgreementOutcome.AFFIRMATIVE,
        )
        self.assertIsNotNone(admission.checked)
        self.assertFalse(admission.result.evidence["establishes_proximity"])
        assert admission.checked is not None
        self.assertEqual(
            admission.checked.initial_oracle_coordinate_id,
            EXACT_CLASSICAL_ORACLE_DECLARATIONS[0].identity,
        )
        self.assertEqual(
            admission.checked.public_environment_id,
            self.case.native_trace.public_environment.identity,
        )
        portable = admission.checked.to_term()
        rendered = repr(portable)
        for forbidden in (
            "native_trace_id",
            "initial_oracle_material_id",
            "values",
            "terminal_scalar",
            self.case.native_trace.oracles[0].identity.digest.hex(),
        ):
            self.assertNotIn(forbidden, rendered)
        self.assertFalse(portable["material_serialized"])
        self.assertFalse(portable["material_digest_serialized"])

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
                )
                admission = check_initial_oracle_grounding(
                    instance,
                    binding,
                    statement,
                    self.secret_capability,
                    self.view_capability,
                )
                self.assertIs(
                    admission.result.outcome,
                    OracleMaterialAgreementOutcome.REFUSED,
                )
                self.assertEqual(
                    admission.result.code,
                    "FRI-IOR-CLASSICAL-RELATION-013",
                )
                self.assertIsNone(admission.checked)

    def test_native_core_declares_causal_oracle_roles_and_rejects_same_core_fs(
        self,
    ) -> None:
        declarations = EXACT_CLASSICAL_NATIVE_CORE.to_term()[
            "oracle_declarations"
        ]
        self.assertEqual(
            tuple(item["origin"] for item in declarations),
            ("InitialOracle", "ProverOracle", "ProverOracle"),
        )
        self.assertEqual(
            tuple(item["publication_mode"] for item in declarations),
            ("LogicalAccess",) * 3,
        )
        self.assertTrue(all(item["publication_outputs"] == [] for item in declarations))
        native = check_classical_strong_fiat_shamir_core(
            EXACT_CLASSICAL_NATIVE_CORE
        )
        self.assertIs(native.outcome, OutcomeClass.REFUSED)
        self.assertEqual(native.code, "FRI-IOR-CLASSICAL-FS-015")
        committed = check_classical_strong_fiat_shamir_core(
            EXACT_CLASSICAL_COMMITTED_CORE
        )
        self.assertIs(committed.outcome, OutcomeClass.AFFIRMATIVE)
        replay = verify_committed_fiat_shamir(
            self.case.fiat_shamir_run.public_inputs,
            self.case.fiat_shamir_run.proof,
        )
        self.assertIs(replay.outcome, OutcomeClass.AFFIRMATIVE)

    def test_confidential_authorities_are_causal_nonportable_and_not_replayable(
        self,
    ) -> None:
        raw_trace_attempt = issue_confidential_initial_oracle_view(
            self.case.native_trace,
            self.policy_capability,
        )
        self.assertIs(raw_trace_attempt.result.outcome, OutcomeClass.REFUSED)
        verification_attempt = issue_confidential_initial_oracle_view(
            verify_native_trace(self.case.native_trace),
            self.policy_capability,
        )
        self.assertIs(verification_attempt.result.outcome, OutcomeClass.REFUSED)
        receipt_attempt = issue_confidential_initial_oracle_view(
            self.run_receipt,
            self.policy_capability,
        )
        self.assertIs(receipt_attempt.result.outcome, OutcomeClass.REFUSED)
        authored_policy_attempt = issue_confidential_initial_oracle_view(
            self.causal_case.execution_authority,
            self.policy,
        )
        self.assertIs(authored_policy_attempt.result.outcome, OutcomeClass.REFUSED)

        authorities = (
            self.causal_case.supply_capability,
            self.causal_case.execution_authority,
            self.policy_capability,
            self.view_admission.checked_authority,
            self.view_capability,
            self.secret_capability,
            self.initial_grounding_admission.checked,
            self.initial_grounding_admission.checked.result_ref,
        )
        for authority in authorities:
            with self.subTest(authority=type(authority).__name__):
                with self.assertRaises(TypeError):
                    copy.copy(authority)
                with self.assertRaises(TypeError):
                    pickle.dumps(authority)

    def test_missing_or_reconstructed_live_sources_do_not_become_inequality(
        self,
    ) -> None:
        missing = check_initial_oracle_grounding(
            self.instance,
            self.binding,
            self.statement,
            None,
            self.view_capability,
        )
        self.assertIs(
            missing.result.outcome,
            OracleMaterialAgreementOutcome.CANNOT_ANSWER,
        )
        reconstructed = check_initial_oracle_grounding(
            self.instance,
            self.binding,
            self.statement,
            object(),
            self.view_capability,
        )
        self.assertIs(
            reconstructed.result.outcome,
            OracleMaterialAgreementOutcome.REFUSED,
        )
        self.assertIsNone(missing.checked)
        self.assertIsNone(reconstructed.checked)

    def test_unqueried_initial_entry_mutation_is_semantic_negative(self) -> None:
        queried = {
            index
            for occurrence in self.case.native_trace.query_occurrences
            if occurrence.layer == 0
            for index in (occurrence.sampled_index, occurrence.mate_index)
        }
        unqueried = next(
            index for index in range(64) if index not in queried
        )
        values = list(self.case.native_trace.oracles[0].values)
        values[unqueried] = GoldilocksElement.reduce(values[unqueried].value + 1)
        changed_secret = issue_relation_initial_oracle_secret_assignment(
            self.instance,
            self.binding,
            self.statement,
            self.causal_case.execution_authority,
            tuple(values),
        )
        admission = check_initial_oracle_grounding(
            self.instance,
            self.binding,
            self.statement,
            changed_secret,
            self.view_capability,
        )
        self.assertIs(
            admission.result.outcome,
            OracleMaterialAgreementOutcome.NEGATIVE,
        )
        self.assertIsNotNone(admission.checked)
        assert admission.checked is not None
        self.assertIs(
            admission.checked.outcome,
            OracleMaterialAgreementOutcome.NEGATIVE,
        )
        self.assertNotIn("values", repr(admission.checked.to_term()))

        issued_view = self.view_capability._checked._view
        self.assertFalse(hasattr(issued_view, "_trace"))
        self.assertFalse(hasattr(issued_view, "_terminal_scalar"))
        self.assertFalse(hasattr(issued_view, "_owner_salts"))

    def test_policy_consumer_purpose_and_role_substitution_are_refused(self) -> None:
        wrong_role = semantic_id(
            "relations-wrong-confidential-role",
            "fri-ior.test.wrong-confidential-role.v1",
            {"role": "wrong"},
        )
        candidates = (
            replace(self.policy, downstream_consumer_id=wrong_role),
            replace(self.policy, purpose_id=wrong_role),
            replace(
                self.policy,
                downstream_consumer_id=self.policy.purpose_id,
                purpose_id=self.policy.downstream_consumer_id,
            ),
        )
        self.assertNotEqual(
            self.policy.downstream_consumer_id.subject_kind,
            self.policy.purpose_id.subject_kind,
        )
        for candidate in candidates:
            with self.subTest(policy_id=str(candidate.identity)):
                policy = admit_confidential_initial_oracle_disclosure_policy(
                    candidate
                )
                self.assertIsNotNone(policy.capability)
                view = issue_confidential_initial_oracle_view(
                    self.causal_case.execution_authority,
                    policy.capability,
                )
                self.assertIsNotNone(view.capability)
                admission = check_initial_oracle_grounding(
                    self.instance,
                    self.binding,
                    self.statement,
                    self.secret_capability,
                    view.capability,
                )
                self.assertIs(
                    admission.result.outcome,
                    OracleMaterialAgreementOutcome.REFUSED,
                )

    def test_wrong_protocol_and_different_invocation_or_supply_are_refused(self) -> None:
        wrong_protocol = semantic_id(
            "classical-fri-native-protocol",
            "fri-ior.test.wrong-native-protocol.v1",
            {"challenge_interpretation": "Fresh", "variant": "wrong"},
        )
        policy = admit_confidential_initial_oracle_disclosure_policy(
            replace(self.policy, protocol_id=wrong_protocol)
        )
        self.assertIs(policy.result.outcome, OutcomeClass.REFUSED)
        self.assertIsNone(policy.capability)

        other = build_causal_honest_classical_case()
        other_view = issue_confidential_initial_oracle_view(
            other.execution_authority,
            self.policy_capability,
        )
        self.assertIsNotNone(other_view.capability)
        admission = check_initial_oracle_grounding(
            self.instance,
            self.binding,
            self.statement,
            self.secret_capability,
            other_view.capability,
        )
        self.assertIs(
            admission.result.outcome,
            OracleMaterialAgreementOutcome.REFUSED,
        )

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
        residual_term = residual.to_term()
        rendered = repr(residual_term)
        for forbidden in (
            "native_trace_id",
            "terminal_scalar",
            "initial_oracle_material_id",
            "values",
            self.case.native_trace.identity.digest.hex(),
            self.case.native_trace.oracles[0].identity.digest.hex(),
        ):
            self.assertNotIn(forbidden, rendered)
        self.assertFalse(residual_term["trace_identity_serialized"])
        self.assertFalse(residual_term["terminal_value_serialized"])
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
