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
    ApplicabilityObligation,
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
    SemanticBindingKind,
    SourceAnchor,
    TheoremSemanticBinding,
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
from friiormodel.profile import (  # noqa: E402
    BINARY_FOLD_EVALUATOR_LAW,
    EXACT_ALGEBRA_PROFILE,
    QUERY_ANSWER_PROJECTION_LAW,
)
from friiormodel.provenance import ArtifactContentId  # noqa: E402
from friiormodel.subjects import (  # noqa: E402
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    COMMITTED_FRI_CORE,
    COMMITMENT_COMPILATION_DECLARATION,
    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
    FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL,
    FRESH_WORK_AUGMENTED_PROTOCOL,
    GRINDING_AUGMENTATION_DECLARATION,
    NATIVE_FRI_CORE,
)
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
                EXACT_ALGEBRA_PROFILE.identity,  # type: ignore[arg-type]
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
            relation_bindings = tuple(
                binding
                for binding in question.semantic_bindings
                if binding.kind is SemanticBindingKind.RELATION_SCHEMA
            )
            self.assertEqual(len(relation_bindings), 1)
            self.assertIsNone(relation_bindings[0].subject_id)
            self.assertEqual(
                relation_bindings[0].open_obligation_name,
                "relation-correspondence",
            )

    def test_questions_bind_exact_local_source_and_target_subjects(self) -> None:
        expected = {
            "original-fri-native-proximity": (
                NATIVE_FRI_CORE.identity,
                NATIVE_FRI_CORE.identity,
            ),
            "direct-fri-round-by-round": (
                NATIVE_FRI_CORE.identity,
                NATIVE_FRI_CORE.identity,
            ),
            "round-by-round-to-restricted-restoration": (
                NATIVE_FRI_CORE.identity,
                NATIVE_FRI_CORE.identity,
            ),
            "round-by-round-to-unrestricted-restoration": (
                NATIVE_FRI_CORE.identity,
                NATIVE_FRI_CORE.identity,
            ),
            "commitment-compilation-preservation": (
                NATIVE_FRI_CORE.identity,
                COMMITTED_FRI_CORE.identity,
            ),
            "bcs-restricted-restoration-to-classical-rom": (
                NATIVE_FRI_CORE.identity,
                FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity,
            ),
            "grinding-over-vector-errors": (
                NATIVE_FRI_CORE.identity,
                FRESH_WORK_AUGMENTED_PROTOCOL.identity,
            ),
            "direct-fri-classical-rom": (
                NATIVE_FRI_CORE.identity,
                FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity,
            ),
            "fri-qrom-asymptotic": (
                FRESH_WORK_AUGMENTED_PROTOCOL.identity,
                FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity,
            ),
            "multi-round-fs-knowledge": (
                FRESH_WORK_AUGMENTED_PROTOCOL.identity,
                FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL.identity,
            ),
        }
        for name, (source_id, target_id) in expected.items():
            with self.subTest(question=name):
                endpoints = tuple(
                    binding
                    for binding in self.questions[name].semantic_bindings
                    if binding.kind
                    in {
                        SemanticBindingKind.SOURCE_CORE,
                        SemanticBindingKind.SOURCE_PROTOCOL,
                        SemanticBindingKind.TARGET_CORE,
                        SemanticBindingKind.TARGET_PROTOCOL,
                    }
                )
                self.assertEqual(len(endpoints), 2)
                self.assertEqual(endpoints[0].subject_id, source_id)
                self.assertEqual(endpoints[1].subject_id, target_id)

    def test_construction_bindings_distinguish_declarations_checks_and_open_slots(
        self,
    ) -> None:
        commitment = self.questions["commitment-compilation-preservation"]
        bcs = self.questions["bcs-restricted-restoration-to-classical-rom"]
        qrom = self.questions["fri-qrom-asymptotic"]

        def ids(question: object, kind: SemanticBindingKind) -> set[SemanticId]:
            return {
                binding.subject_id
                for binding in question.semantic_bindings  # type: ignore[attr-defined]
                if binding.kind is kind and binding.subject_id is not None
            }

        self.assertEqual(
            ids(commitment, SemanticBindingKind.CONSTRUCTION_DECLARATION),
            {COMMITMENT_COMPILATION_DECLARATION.identity},
        )
        self.assertEqual(ids(commitment, SemanticBindingKind.CHECKED_CONSTRUCTION), set())
        self.assertIn(
            "checked-commitment-compilation",
            {
                binding.name
                for binding in commitment.semantic_bindings
                if binding.kind is SemanticBindingKind.CHECKED_CONSTRUCTION
                and binding.subject_id is None
            },
        )

        self.assertEqual(
            ids(bcs, SemanticBindingKind.CONSTRUCTION_DECLARATION),
            {
                COMMITMENT_COMPILATION_DECLARATION.identity,
                GRINDING_AUGMENTATION_DECLARATION.identity,
                FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity,
            },
        )
        self.assertEqual(
            ids(bcs, SemanticBindingKind.CHECKED_CONSTRUCTION),
            {CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity},
        )
        self.assertEqual(
            ids(qrom, SemanticBindingKind.CONSTRUCTION_DECLARATION),
            {FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity},
        )
        self.assertEqual(
            ids(qrom, SemanticBindingKind.CHECKED_CONSTRUCTION),
            {CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity},
        )

    def test_only_the_native_query_projection_has_a_bound_occurrence_map(self) -> None:
        direct = self.questions["direct-fri-round-by-round"]
        bound = tuple(
            binding
            for binding in direct.semantic_bindings
            if binding.kind is SemanticBindingKind.OCCURRENCE_MAP
        )
        self.assertEqual(len(bound), 1)
        self.assertEqual(bound[0].name, "logical-query-occurrence-map")
        self.assertEqual(bound[0].subject_id, QUERY_ANSWER_PROJECTION_LAW.identity)

        commitment = self.questions["commitment-compilation-preservation"]
        opening = tuple(
            binding
            for binding in commitment.semantic_bindings
            if binding.kind is SemanticBindingKind.OCCURRENCE_MAP
        )
        self.assertEqual(len(opening), 1)
        self.assertIsNone(opening[0].subject_id)
        self.assertEqual(opening[0].open_obligation_name, "occurrence-to-opening")

    def test_local_bindings_rotate_question_but_not_source_theorem_schema(self) -> None:
        question = self.questions["commitment-compilation-preservation"]
        changed_bindings = tuple(
            TheoremSemanticBinding.bound(
                "grinding-augmentation-declaration",
                SemanticBindingKind.CONSTRUCTION_DECLARATION,
                GRINDING_AUGMENTATION_DECLARATION.identity,
            )
            if binding.name == "commitment-compilation-declaration"
            else binding
            for binding in question.semantic_bindings
        )
        changed = replace(question, semantic_bindings=changed_bindings)
        self.assertEqual(changed.schema_identity, question.schema_identity)
        self.assertNotEqual(changed.identity, question.identity)

    def test_semantic_binding_formation_rejects_ambiguous_or_mistyped_slots(
        self,
    ) -> None:
        question = self.questions["direct-fri-round-by-round"]
        relation_index = next(
            index
            for index, binding in enumerate(question.semantic_bindings)
            if binding.kind is SemanticBindingKind.RELATION_SCHEMA
        )
        wrong_obligation = list(question.semantic_bindings)
        wrong_obligation[relation_index] = replace(
            wrong_obligation[relation_index],
            open_obligation_name="theorem-truth",
        )
        with self.assertRaises(ModelFailure) as caught:
            replace(question, semantic_bindings=tuple(wrong_obligation))
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-032")

        with self.assertRaises(ModelFailure) as caught:
            TheoremSemanticBinding.bound(
                "logical-query-occurrence-map",
                SemanticBindingKind.OCCURRENCE_MAP,
                BINARY_FOLD_EVALUATOR_LAW.identity,
            )
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-028")

        occurrence_index = next(
            index
            for index, binding in enumerate(question.semantic_bindings)
            if binding.kind is SemanticBindingKind.OCCURRENCE_MAP
        )
        wrong_map = list(question.semantic_bindings)
        wrong_map[occurrence_index] = replace(
            wrong_map[occurrence_index],
            name="not-a-required-map",
        )
        with self.assertRaises(ModelFailure) as caught:
            replace(question, semantic_bindings=tuple(wrong_map))
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-034")

        without_relation = tuple(
            binding
            for binding in question.semantic_bindings
            if binding.kind is not SemanticBindingKind.RELATION_SCHEMA
        )
        with self.assertRaises(ModelFailure) as caught:
            replace(question, semantic_bindings=without_relation)
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-035")

        duplicate_name = ApplicabilityObligation(
            "theorem-truth",
            ObligationKind.SIDE_CONDITION,
            ObligationStatus.OPEN,
            "a distinct obligation must not reuse this name",
        )
        with self.assertRaises(ModelFailure) as caught:
            replace(question, obligations=question.obligations + (duplicate_name,))
        self.assertEqual(caught.exception.code, "FRI-IOR-ANALYSIS-033")

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
        self.assertEqual(
            evaluation.algebra_profile_id,
            EXACT_ALGEBRA_PROFILE.identity,
        )
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
    def test_analysis_imports_only_semantic_subjects_not_execution_modules(
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
                    "EXACT_ALGEBRA_PROFILE",
                    "QUERY_ANSWER_PROJECTION_LAW",
                    "ArtifactContentId",
                    "CHECKED_FIAT_SHAMIR_CONSTRUCTION",
                    "COMMITTED_FRI_CORE",
                    "COMMITMENT_COMPILATION_DECLARATION",
                    "FIAT_SHAMIR_CONSTRUCTION_DECLARATION",
                    "FIAT_SHAMIR_WORK_AUGMENTED_PROTOCOL",
                    "FRESH_WORK_AUGMENTED_PROTOCOL",
                    "GRINDING_AUGMENTATION_DECLARATION",
                    "NATIVE_FRI_CORE",
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
        self.assertEqual(
            imported_modules,
            {"profile", "provenance", "subjects", "terms"},
        )


if __name__ == "__main__":
    unittest.main()
