"""Tests for typed Analysis question formation and exact local arithmetic."""

from __future__ import annotations

import ast
from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel import analysis as analysis_module  # noqa: E402
from friiormodel.analysis import (  # noqa: E402
    BoundClassification,
    BoundLaw,
    BoundShape,
    Capability,
    EvaluationStatus,
    ExperimentKind,
    ModelFailure,
    ObligationKind,
    ObligationStatus,
    PropertyKind,
    QuantitativeBoundExpression,
    Rational,
    ResourceCoordinate,
    SourceAnchor,
    canonical_experiments,
    canonical_property_questions,
    canonical_source_anchors,
    canonical_theorem_questions,
    check_property_coercion,
    check_question_formation,
    evaluate_tiny_f97_round_by_round_bound,
    local_original_fri_obligations,
    retained_assumptions,
)
from friiormodel.profile import EXACT_PROFILE  # noqa: E402
from friiormodel.provenance import ArtifactContentId  # noqa: E402
from friiormodel.terms import OutcomeClass, SemanticId  # noqa: E402


class ExperimentProfileTest(unittest.TestCase):
    def setUp(self) -> None:
        self.experiments = canonical_experiments()

    def test_catalog_forms_distinct_native_committed_and_oracle_games(self) -> None:
        self.assertEqual(len(self.experiments), 12)
        native = self.experiments[ExperimentKind.NATIVE_IOPP]
        committed = self.experiments[ExperimentKind.COMMITTED_INTERACTIVE]
        rom = self.experiments[ExperimentKind.CLASSICAL_ROM]
        qrom = self.experiments[ExperimentKind.QROM]

        self.assertIn(Capability.LOGICAL_ORACLE, native.capabilities)
        self.assertNotIn(Capability.PROOF_SUPPLIED_OPENING, native.capabilities)
        self.assertIn(Capability.PROOF_SUPPLIED_OPENING, committed.capabilities)
        self.assertNotIn(Capability.LOGICAL_ORACLE, committed.capabilities)
        self.assertIn(Capability.CLASSICAL_RANDOM_ORACLE, rom.capabilities)
        self.assertNotIn(Capability.QUANTUM_RANDOM_ORACLE, rom.capabilities)
        self.assertIn(Capability.QUANTUM_RANDOM_ORACLE, qrom.capabilities)
        self.assertNotIn(Capability.CLASSICAL_RANDOM_ORACLE, qrom.capabilities)

        identities = {profile.identity for profile in self.experiments.values()}
        self.assertEqual(len(identities), len(self.experiments))
        self.assertTrue(
            all(isinstance(identity, SemanticId) for identity in identities)
        )

    def test_restricted_and_unrestricted_restoration_are_different_games(self) -> None:
        restricted = self.experiments[ExperimentKind.RESTRICTED_RESTORATION]
        unrestricted = self.experiments[ExperimentKind.UNRESTRICTED_RESTORATION]

        self.assertNotEqual(restricted.identity, unrestricted.identity)
        self.assertIn("no-empty-return", restricted.scheduler_law)
        self.assertIn("empty-state-return-permitted", unrestricted.scheduler_law)
        self.assertIn(
            ResourceCoordinate.RESTORATION_BRANCH_EXTENSIONS,
            restricted.resources,
        )

    def test_resource_coordinates_do_not_alias_equal_numeric_counts(self) -> None:
        native = self.experiments[ExperimentKind.NATIVE_IOPP]
        committed = self.experiments[ExperimentKind.COMMITTED_INTERACTIVE]
        rom = self.experiments[ExperimentKind.CLASSICAL_ROM]
        qrom = self.experiments[ExperimentKind.QROM]

        self.assertIn(ResourceCoordinate.LOGICAL_QUERY_OCCURRENCES, native.resources)
        self.assertIn(ResourceCoordinate.UNIQUE_OPENED_POSITIONS, committed.resources)
        self.assertIn(ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES, rom.resources)
        self.assertIn(ResourceCoordinate.QUANTUM_RANDOM_ORACLE_QUERIES, qrom.resources)
        self.assertEqual(
            len(
                {
                    ResourceCoordinate.LOGICAL_QUERY_OCCURRENCES,
                    ResourceCoordinate.UNIQUE_OPENED_POSITIONS,
                    ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
                    ResourceCoordinate.QUANTUM_RANDOM_ORACLE_QUERIES,
                }
            ),
            4,
        )

    def test_duplicate_finite_carrier_entries_are_malformed(self) -> None:
        native = self.experiments[ExperimentKind.NATIVE_IOPP]
        with self.assertRaises(ModelFailure) as caught:
            replace(
                native,
                capabilities=(Capability.PUBLIC_COIN, Capability.PUBLIC_COIN),
            )
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-020")


class PropertySeparationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.properties = canonical_property_questions()

    def test_required_property_questions_are_present_and_not_established(self) -> None:
        required = {
            PropertyKind.NATIVE_COMPLETENESS,
            PropertyKind.NATIVE_PROXIMITY_SOUNDNESS,
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            PropertyKind.RESTRICTED_RESTORATION_SOUNDNESS,
            PropertyKind.UNRESTRICTED_RESTORATION_SOUNDNESS,
            PropertyKind.COMMITTED_INTERACTIVE_SOUNDNESS,
            PropertyKind.GRINDING_ADJUSTED_SOUNDNESS,
            PropertyKind.CLASSICAL_ROM_SOUNDNESS,
            PropertyKind.QROM_SOUNDNESS,
            PropertyKind.CLASSICAL_ROM_KNOWLEDGE,
            PropertyKind.GENERALIZED_SPECIAL_SOUNDNESS,
        }
        self.assertTrue(required.issubset(self.properties))
        for question in self.properties.values():
            term = question.to_term()
            self.assertIsNone(term["established_property"])
            self.assertIsNone(term["outer_relation_conclusion"])

        self.assertIs(
            self.properties[PropertyKind.QROM_SOUNDNESS].evaluation_status,
            EvaluationStatus.UNSUPPORTED,
        )
        self.assertIs(
            self.properties[PropertyKind.CLASSICAL_ROM_KNOWLEDGE].evaluation_status,
            EvaluationStatus.UNSUPPORTED,
        )

    def test_property_signature_mismatch_is_rejected_at_formation(self) -> None:
        native_soundness = self.properties[PropertyKind.NATIVE_PROXIMITY_SOUNDNESS]
        with self.assertRaises(ModelFailure) as caught:
            replace(
                native_soundness,
                kind=PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
            )
        self.assertIs(caught.exception.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-007")

    def test_soundness_does_not_coerce_to_round_by_round(self) -> None:
        result = check_property_coercion(
            self.properties[PropertyKind.NATIVE_PROXIMITY_SOUNDNESS],
            PropertyKind.ROUND_BY_ROUND_VECTOR_SOUNDNESS,
        )
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(result.code, "FRI-IOR-ANALYSIS-023")

    def test_classical_rom_does_not_coerce_to_qrom(self) -> None:
        result = check_property_coercion(
            self.properties[PropertyKind.CLASSICAL_ROM_SOUNDNESS],
            PropertyKind.QROM_SOUNDNESS,
        )
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)

    def test_honest_verifier_does_not_coerce_to_malicious_verifier(self) -> None:
        result = check_property_coercion(
            self.properties[PropertyKind.HONEST_VERIFIER_ZERO_KNOWLEDGE],
            PropertyKind.MALICIOUS_VERIFIER_ZERO_KNOWLEDGE,
        )
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)

    def test_exact_kind_check_is_formation_evidence_not_property_evidence(self) -> None:
        question = self.properties[PropertyKind.NATIVE_COMPLETENESS]
        result = check_property_coercion(question, question.kind)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-ANALYSIS-100")
        self.assertIsNone(result.evidence["property_established"])


class SourceAndTheoremQuestionTest(unittest.TestCase):
    def setUp(self) -> None:
        self.sources = canonical_source_anchors()
        self.questions = canonical_theorem_questions()

    def test_source_anchors_bind_exact_bytes_but_not_theorem_truth(self) -> None:
        self.assertEqual(len(self.sources), 5)
        expected = {
            "icalp-fri-2018-14": "e244896fb6e7fcab7fe4de00e31a36003b941b6550e062fdb5ee66d78641498d",
            "bcs-iop-2016-116-r2": "a2dc9bd042665081664287281b9bcf64735be2c818ce9207cce57cc43939fa2f",
            "fri-fs-2023-1071-r7": "bb7a7e87b9000c98106de99c9af9d289def2a1b91919a3507ee78bf9bfd16947",
            "afk-multi-round-fs-2021-1377-v2": "93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c",
            "ethstark-2021-582-r3": "23b1bd72be468c3b1781bfd76c075a843bb529e8dedc763629c67a080b4f0099",
        }
        for name, digest in expected.items():
            source = self.sources[name]
            self.assertEqual(source.artifact_content_id, ArtifactContentId(digest))
            self.assertIsNone(source.to_term()["truth_discharge"])

    def test_source_anchor_does_not_accept_a_semantic_identity_as_artifact(
        self,
    ) -> None:
        with self.assertRaises(ModelFailure) as caught:
            SourceAnchor(
                "wrong-kind",
                "Wrong kind",
                "version 1",
                EXACT_PROFILE.identity,  # type: ignore[arg-type]
                ("Theorem 1",),
            )
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-010")

    def test_theorem_catalog_keeps_every_edge_conditional(self) -> None:
        self.assertEqual(len(self.questions), 10)
        for question in self.questions.values():
            term = question.to_term()
            self.assertIsNone(term["theorem_true"])
            self.assertIsNone(term["applicable"])
            self.assertIsNone(term["property_established"])
            self.assertTrue(question.obligations)
            self.assertIn(
                ObligationKind.THEOREM_TRUTH,
                {obligation.kind for obligation in question.obligations},
            )

    def test_commitment_compilation_and_rom_are_separate_theorem_questions(
        self,
    ) -> None:
        compilation = self.questions["commitment-compilation-preservation"]
        rom = self.questions["bcs-restricted-restoration-to-classical-rom"]

        self.assertIs(compilation.bound.law, BoundLaw.COMMITMENT_COMPILATION)
        self.assertIs(rom.bound.law, BoundLaw.BCS_CLASSICAL_ROM)
        self.assertIs(
            compilation.target_property.kind,
            PropertyKind.COMMITTED_INTERACTIVE_SOUNDNESS,
        )
        self.assertIs(rom.target_property.kind, PropertyKind.CLASSICAL_ROM_SOUNDNESS)
        self.assertNotEqual(compilation.identity, rom.identity)

    def test_qrom_and_knowledge_questions_are_distinct_and_unsupported(self) -> None:
        qrom = self.questions["fri-qrom-asymptotic"]
        knowledge = self.questions["multi-round-fs-knowledge"]

        self.assertIs(qrom.evaluation_status, EvaluationStatus.UNSUPPORTED)
        self.assertIs(knowledge.evaluation_status, EvaluationStatus.UNSUPPORTED)
        self.assertIs(qrom.target_property.kind, PropertyKind.QROM_SOUNDNESS)
        self.assertIs(
            qrom.source_property.kind,
            PropertyKind.GENERALIZED_SPECIAL_SOUNDNESS,
        )
        self.assertIs(
            knowledge.target_property.kind,
            PropertyKind.CLASSICAL_ROM_KNOWLEDGE,
        )
        self.assertIs(
            knowledge.source_property.kind,
            PropertyKind.GENERALIZED_SPECIAL_SOUNDNESS,
        )
        self.assertIn(
            ObligationKind.HIDDEN_CONSTANTS,
            {obligation.kind for obligation in qrom.obligations},
        )
        self.assertIn(
            ObligationKind.EXTRACTOR_RELATION,
            {obligation.kind for obligation in knowledge.obligations},
        )

    def test_grinding_is_an_open_placement_specific_theorem_edge(self) -> None:
        grinding = self.questions["grinding-over-vector-errors"]
        self.assertIs(grinding.bound.law, BoundLaw.GRINDING_VECTOR)
        self.assertIn(
            ObligationKind.GRINDING_PLACEMENT,
            {obligation.kind for obligation in grinding.obligations},
        )
        self.assertTrue(
            all(
                obligation.status is ObligationStatus.OPEN
                for obligation in grinding.obligations
            )
        )

    def test_retained_assumptions_are_not_truth_discharge_artifacts(self) -> None:
        assumptions = retained_assumptions()
        self.assertEqual(len(assumptions), len(self.questions))
        self.assertEqual(len({item.identity for item in assumptions}), len(assumptions))
        self.assertTrue(
            all(
                item.to_term()["discharges_theorem_truth"] is False
                for item in assumptions
            )
        )

    def test_question_formation_returns_no_security_or_applicability_claim(
        self,
    ) -> None:
        for candidate in (
            canonical_property_questions()[PropertyKind.NATIVE_COMPLETENESS],
            self.questions["direct-fri-round-by-round"],
        ):
            result = check_question_formation(candidate)
            self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
            self.assertEqual(result.code, "FRI-IOR-ANALYSIS-101")
            self.assertIsNone(result.evidence["theorem_true"])
            self.assertIsNone(result.evidence["applicable"])
            self.assertIsNone(result.evidence["security_established"])
            self.assertIsNone(result.evidence["outer_relation_established"])


class QuantitativeExpressionTest(unittest.TestCase):
    def test_registered_expressions_bind_resource_kinds(self) -> None:
        rbr = QuantitativeBoundExpression.for_law(BoundLaw.DIRECT_FRI_ROUND_BY_ROUND)
        restoration = QuantitativeBoundExpression.for_law(
            BoundLaw.ROUND_BY_ROUND_TO_RESTORATION
        )
        classical = QuantitativeBoundExpression.for_law(
            BoundLaw.DIRECT_FRI_CLASSICAL_ROM
        )
        qrom = QuantitativeBoundExpression.for_law(BoundLaw.SPECIAL_SOUNDNESS_QROM)

        rbr_binders = {item.name: item for item in rbr.binders}
        restoration_binders = {item.name: item for item in restoration.binders}
        classical_binders = {item.name: item for item in classical.binders}
        qrom_binders = {item.name: item for item in qrom.binders}
        self.assertIs(
            rbr_binders["ell"].resource,
            ResourceCoordinate.LOGICAL_QUERY_OCCURRENCES,
        )
        self.assertIs(
            restoration_binders["b"].resource,
            ResourceCoordinate.RESTORATION_BRANCH_EXTENSIONS,
        )
        self.assertIs(
            classical_binders["Q"].resource,
            ResourceCoordinate.CLASSICAL_RANDOM_ORACLE_QUERIES,
        )
        self.assertIs(
            qrom_binders["t"].resource,
            ResourceCoordinate.QUANTUM_RANDOM_ORACLE_QUERIES,
        )
        self.assertIs(qrom.shape, BoundShape.ASYMPTOTIC)

    def test_registered_expression_cannot_be_relabelled(self) -> None:
        expression = QuantitativeBoundExpression.for_law(
            BoundLaw.DIRECT_FRI_ROUND_BY_ROUND
        )
        with self.assertRaises(ModelFailure) as caught:
            replace(expression, formula="epsilon=0")
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-012")

    def test_rationals_are_exact_and_canonical(self) -> None:
        self.assertEqual(Rational(1, 2).to_term(), {"numerator": 1, "denominator": 2})
        with self.assertRaises(ModelFailure):
            Rational(2, 4)
        with self.assertRaises(ModelFailure):
            Rational(1, 0)

    def test_f97_substitution_is_classified_vacuous_without_theorem_claim(self) -> None:
        expression = QuantitativeBoundExpression.for_law(
            BoundLaw.DIRECT_FRI_ROUND_BY_ROUND
        )
        evaluation, result = evaluate_tiny_f97_round_by_round_bound(expression)

        self.assertIs(evaluation.classification, BoundClassification.VACUOUS_BOUND)
        self.assertEqual(evaluation.profile_id, EXACT_PROFILE.identity)
        self.assertIn(
            "first-term-is-greater-than-16009-by-exact-integer-squaring",
            evaluation.derived_facts,
        )
        self.assertIn("second-term-equals-6561/10000", evaluation.derived_facts)
        self.assertIsNone(evaluation.theorem_applicability)
        self.assertIsNone(evaluation.property_established)

        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.evidence["classification"], "VacuousBound")
        self.assertIsNone(result.evidence["theorem_true"])
        self.assertIsNone(result.evidence["theorem_applicable"])
        self.assertIsNone(result.evidence["property_established"])
        self.assertIsNone(result.evidence["non_vacuity_established"])

    def test_original_fri_side_conditions_are_locally_refuted_not_security_evidence(
        self,
    ) -> None:
        obligations = local_original_fri_obligations()
        self.assertEqual(len(obligations), 4)
        self.assertEqual(
            sum(
                item.status is ObligationStatus.LOCALLY_REFUTED for item in obligations
            ),
            3,
        )
        self.assertEqual(
            sum(item.status is ObligationStatus.OPEN for item in obligations),
            1,
        )
        self.assertTrue(
            all(item.kind is ObligationKind.SIDE_CONDITION for item in obligations)
        )


class DependencyBoundaryTest(unittest.TestCase):
    def test_analysis_imports_no_execution_commitment_or_private_generation_module(
        self,
    ) -> None:
        source_path = Path(analysis_module.__file__).resolve()
        tree = ast.parse(source_path.read_text(encoding="utf-8"))
        relative_imports = {
            alias.name
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom) and node.level == 1
            for alias in node.names
        }
        # Imported symbol names are checked in addition to source modules so a
        # future re-export cannot silently add an operational dependency.
        self.assertTrue(
            relative_imports.issubset(
                {
                    "EXACT_PROFILE",
                    "ArtifactContentId",
                    "CheckResult",
                    "ModelFailure",
                    "OutcomeClass",
                    "SemanticId",
                    "affirmative",
                    "kind_mismatch",
                    "malformed",
                    "semantic_id",
                }
            )
        )

        imported_modules = {
            node.module
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom) and node.level == 1
        }
        self.assertEqual(imported_modules, {"profile", "provenance", "terms"})


if __name__ == "__main__":
    unittest.main()
