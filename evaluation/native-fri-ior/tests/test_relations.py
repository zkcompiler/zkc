"""Tests for exact finite FRI relation and occurrence grounding."""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
import inspect
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.commitment import build_commitment  # noqa: E402
from friiormodel.field import Fp, Fp2, evaluate_polynomial  # noqa: E402
from friiormodel.native import (  # noqa: E402
    NativeFriTrace,
    OracleEntry,
    RandomQueryDraw,
    derive_honest_native_trace,
)
from friiormodel.profile import D0, D1, EXACT_PROFILE  # noqa: E402
from friiormodel.proof import (  # noqa: E402
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
)
from friiormodel.relations import (  # noqa: E402
    FriOracleLayer,
    FriRelationGroundingRequest,
    FriTerminalResidualBoundary,
    OpeningOccurrenceGrounding,
    OuterInferencePremise,
    OuterRelationInferenceRequest,
    RelationStatementOccurrence,
    RepresentationBoundary,
    RepresentationBoundaryDeclaration,
    RepresentationClass,
    canonical_relation_grounding_request,
    check_fri_relation_grounding,
    check_logical_publication_loss,
    check_representation_boundary,
    infer_outer_computation_relation,
    logical_oracle_material_id,
)
from friiormodel.terms import (  # noqa: E402
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    SemanticId,
    semantic_id,
)
from friiormodel.transcript import (  # noqa: E402
    CANONICAL_CONSTRUCTION_PLAN,
    FiatShamirTranscript,
    construct_fiat_shamir_transcript,
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
COEFFICIENT_VALUES = (3, 5, 7, 11, 13, 17, 19, 23)
EXPECTED_BETA0 = (10, 34)
EXPECTED_BETA1 = (23, 31)


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _fold_coefficients(
    coefficients: tuple[Fp2, ...],
    challenge: Fp2,
) -> tuple[Fp2, ...]:
    return tuple(
        coefficients[index] + challenge * coefficients[index + 1]
        for index in range(0, len(coefficients), 2)
    )


def _salts(prefix: int, pair_count: int) -> tuple[bytes, ...]:
    return tuple(bytes((prefix + index,)) * 16 for index in range(pair_count))


@dataclass(frozen=True, slots=True)
class _Case:
    public_inputs: CommittedFriPublicInputs
    proof: PublicFriProof
    transcript: FiatShamirTranscript
    trace: NativeFriTrace
    statement: RelationStatementOccurrence
    request: FriRelationGroundingRequest
    source_coefficients: tuple[Fp2, ...]


def _build_case() -> _Case:
    public_inputs = CommittedFriPublicInputs(
        EXACT_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        STATEMENT,
        APPLICATION_CONTEXT,
    )
    source_coefficients = tuple(_fp2(value) for value in COEFFICIENT_VALUES)
    beta0 = _fp2(*EXPECTED_BETA0)
    beta1 = _fp2(*EXPECTED_BETA1)

    initial_evaluations = tuple(
        evaluate_polynomial(source_coefficients, point) for point in D0.points()
    )
    tree0 = build_commitment(
        D0,
        initial_evaluations,
        _salts(0x10, D0.order // 2),
    )
    first_coefficients = _fold_coefficients(source_coefficients, beta0)
    first_evaluations = tuple(
        evaluate_polynomial(first_coefficients, point) for point in D1.points()
    )
    tree1 = build_commitment(
        D1,
        first_evaluations,
        _salts(0x40, D1.order // 2),
    )
    terminal = _fold_coefficients(first_coefficients, beta1)

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
    if transcript.beta0 != beta0 or transcript.beta1 != beta1:
        raise AssertionError(
            "relations test transcript constants drifted: "
            f"{transcript.beta0!r}, {transcript.beta1!r}"
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
    query_indices = tuple(
        occurrence.initial_domain_index for occurrence in transcript.query_occurrences
    )
    trace = derive_honest_native_trace(
        source_coefficients,
        beta0,
        beta1,
        query_indices,
        ResourceCounter(),
    )
    statement = RelationStatementOccurrence(EXACT_PROFILE.identity, 0, STATEMENT)
    request = canonical_relation_grounding_request(
        statement,
        trace,
        public_inputs,
        proof,
    )
    return _Case(
        public_inputs,
        proof,
        transcript,
        trace,
        statement,
        request,
        source_coefficients,
    )


class RelationGroundingPositiveTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()
        cls.result = check_fri_relation_grounding(
            cls.case.request,
            cls.case.trace,
            cls.case.public_inputs,
            cls.case.proof,
        )

    def test_exact_statement_oracle_cap_and_run_grounding_accepts(self) -> None:
        self.assertIs(self.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(self.result.code, "FRI-IOR-RELATION-102")
        self.assertIsInstance(self.result.subject, SemanticId)
        self.assertEqual(
            self.result.subject.subject_kind,
            "checked-fri-relation-grounding",
        )
        self.assertEqual(
            self.result.evidence["statement_grounding_id"],
            self.case.statement.identity,
        )
        self.assertEqual(
            self.result.evidence["initial_oracle_binding_id"],
            self.case.request.initial_oracle_binding.identity,
        )

    def test_run_grounding_preserves_eight_occurrences_and_physical_dedup(self) -> None:
        evidence = self.result.evidence
        self.assertEqual(evidence["opening_occurrence_grounding_count"], 8)
        self.assertEqual(evidence["unique_physical_opening_count"], 4)
        self.assertEqual(
            tuple(evidence["ordered_grounding_coordinates"]),
            (
                (0, "initial"),
                (0, "first-fold"),
                (1, "initial"),
                (1, "first-fold"),
                (2, "initial"),
                (2, "first-fold"),
                (3, "initial"),
                (3, "first-fold"),
            ),
        )
        self.assertEqual(
            len(evidence["opening_occurrence_grounding_ids"]),
            8,
        )
        self.assertEqual(
            len(set(evidence["opening_occurrence_grounding_ids"])),
            8,
        )

    def test_terminal_and_scientific_residual_are_not_collapsed(self) -> None:
        evidence = self.result.evidence
        self.assertEqual(evidence["execution_terminal"], "Accept")
        self.assertEqual(evidence["proximity_residual_status"], "NotEvaluated")
        self.assertIs(evidence["establishes_proximity"], False)
        self.assertIs(evidence["establishes_proximity_preservation"], False)
        self.assertIs(evidence["infers_outer_computation_relation"], False)
        self.assertIs(evidence["establishes_commitment_binding"], False)
        self.assertIs(evidence["establishes_commitment_hiding"], False)

    def test_full_commitment_compilation_remains_an_open_boundary(self) -> None:
        self.assertEqual(
            self.result.evidence["construction_relation_class"],
            "NonIsomorphicConstructionRelation",
        )
        self.assertIs(
            self.result.evidence["establishes_full_commitment_compilation"],
            False,
        )

    def test_association_and_material_identity_do_not_overclaim(self) -> None:
        evidence = self.result.evidence
        self.assertIs(
            evidence["establishes_statement_to_oracle_predicate"],
            False,
        )
        self.assertIs(evidence["oracle_material_identity_is_confidential"], False)
        self.assertIs(evidence["oracle_material_identity_leaks_equality"], True)
        binding_term = self.case.request.initial_oracle_binding.to_term()
        self.assertEqual(
            binding_term["material_identity_privacy"],
            "deterministic-linkable-not-confidential",
        )

    def test_complete_operation_publishes_one_frozen_resource_snapshot(self) -> None:
        evidence = self.result.evidence
        self.assertEqual(
            evidence["resource_scope"],
            "one-private-counter-for-the-complete-operation",
        )
        self.assertGreater(evidence["resource_snapshot"]["hash_calls"], 0)
        self.assertGreater(
            evidence["resource_snapshot"]["logical_query_occurrences"],
            0,
        )

    def test_portable_request_contains_no_oracle_carrier_or_generation_data(
        self,
    ) -> None:
        rendered = repr(self.case.request.to_term())
        for forbidden in (
            "entries",
            "source_coefficients",
            "private_generation",
            "unopened_salts",
            "authentication_path",
        ):
            self.assertNotIn(forbidden, rendered)
        self.assertEqual(
            tuple(inspect.signature(check_fri_relation_grounding).parameters),
            ("request", "trace", "public_inputs", "proof"),
        )
        self.assertEqual(
            {item.name for item in fields(FriRelationGroundingRequest)},
            {
                "statement",
                "initial_oracle_binding",
                "commitment_compilation_id",
                "construction_inputs",
                "cap_occurrences",
            },
        )


class ExactGroundingNegativeTest(unittest.TestCase):
    def setUp(self) -> None:
        self.case = _build_case()

    def _check(
        self,
        request: FriRelationGroundingRequest | None = None,
        trace: NativeFriTrace | None = None,
    ) -> CheckResult:
        return check_fri_relation_grounding(
            self.case.request if request is None else request,
            self.case.trace if trace is None else trace,
            self.case.public_inputs,
            self.case.proof,
        )

    def test_statement_substitution_refuses_before_execution(self) -> None:
        statement = RelationStatementOccurrence(
            EXACT_PROFILE.identity,
            0,
            {**STATEMENT, "initial_oracle_role": "substituted"},
        )
        request = canonical_relation_grounding_request(
            statement,
            self.case.trace,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(request=request)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-021")

    def test_wrong_statement_profile_is_unsupported(self) -> None:
        other_profile_id = semantic_id(
            "fri-ior-profile",
            "fri-ior.profile.v1",
            {"name": "other-coherent-profile"},
        )
        statement = RelationStatementOccurrence(other_profile_id, 0, STATEMENT)
        request = canonical_relation_grounding_request(
            statement,
            self.case.trace,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(request=request)
        self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-020")

    def test_wrong_initial_material_occurrence_refuses(self) -> None:
        wrong_material = semantic_id(
            "logical-oracle-material",
            "fri-ior.relations.logical-oracle-material.v1",
            {"different": True},
        )
        binding = replace(
            self.case.request.initial_oracle_binding,
            oracle_material_id=wrong_material,
        )
        result = self._check(
            request=replace(self.case.request, initial_oracle_binding=binding)
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-023")

    def test_wrong_statement_owner_in_oracle_binding_refuses(self) -> None:
        other_statement_id = semantic_id(
            "relation-statement-occurrence",
            "fri-ior.relations.statement.v1",
            {"different": True},
        )
        binding = replace(
            self.case.request.initial_oracle_binding,
            relation_statement_id=other_statement_id,
        )
        result = self._check(
            request=replace(self.case.request, initial_oracle_binding=binding)
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-022")

    def test_wrong_construction_declaration_is_kind_mismatch(self) -> None:
        wrong = semantic_id(
            "commitment-compilation-declaration",
            "fri-ior.construction.commitment-compilation.v1",
            {"different": True},
        )
        result = self._check(
            request=replace(self.case.request, commitment_compilation_id=wrong)
        )
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(result.code, "FRI-IOR-RELATION-024")

    def test_swapped_construction_inputs_and_caps_refuse_independently(self) -> None:
        candidates = (
            (
                replace(
                    self.case.request,
                    construction_inputs=tuple(
                        reversed(self.case.request.construction_inputs)
                    ),
                ),
                "FRI-IOR-RELATION-025",
            ),
            (
                replace(
                    self.case.request,
                    cap_occurrences=tuple(reversed(self.case.request.cap_occurrences)),
                ),
                "FRI-IOR-RELATION-026",
            ),
        )
        for request, code in candidates:
            with self.subTest(code=code):
                result = self._check(request=request)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, code)

    def test_native_query_occurrence_substitution_refuses(self) -> None:
        draws = list(self.case.trace.query_draws)
        changed_index = (draws[0].initial_domain_index + 1) % D0.order
        draws[0] = RandomQueryDraw(draws[0].ordinal, changed_index)
        changed_trace = replace(self.case.trace, query_draws=tuple(draws))
        changed_request = canonical_relation_grounding_request(
            self.case.statement,
            changed_trace,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(request=changed_request, trace=changed_trace)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-029")

    def test_distinct_valid_fold_challenges_refuse_cross_run_grounding(self) -> None:
        changed_trace = derive_honest_native_trace(
            self.case.source_coefficients,
            self.case.transcript.beta0 + _fp2(1),
            self.case.transcript.beta1,
            tuple(
                occurrence.initial_domain_index
                for occurrence in self.case.transcript.query_occurrences
            ),
            ResourceCounter(),
        )
        changed_request = canonical_relation_grounding_request(
            self.case.statement,
            changed_trace,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(request=changed_request, trace=changed_trace)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-027")

    def test_distinct_valid_terminal_material_refuses_cross_run_grounding(self) -> None:
        coefficients = list(self.case.source_coefficients)
        coefficients[0] = coefficients[0] + _fp2(1)
        changed_trace = derive_honest_native_trace(
            tuple(coefficients),
            self.case.transcript.beta0,
            self.case.transcript.beta1,
            tuple(
                occurrence.initial_domain_index
                for occurrence in self.case.transcript.query_occurrences
            ),
            ResourceCounter(),
        )
        changed_request = canonical_relation_grounding_request(
            self.case.statement,
            changed_trace,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(request=changed_request, trace=changed_trace)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-028")

    def test_selected_native_answers_must_equal_authenticated_openings(self) -> None:
        # Add beta0 - X to the source polynomial.  Its first fold is zero, so
        # O1 and the terminal remain unchanged while every selected O0 pair is
        # different.  Both per-side verifiers accept; Relations must still
        # reject the cross-run answer/opening mismatch.
        coefficients = list(self.case.source_coefficients)
        coefficients[0] = coefficients[0] + self.case.transcript.beta0
        coefficients[1] = coefficients[1] - _fp2(1)
        changed_trace = derive_honest_native_trace(
            tuple(coefficients),
            self.case.transcript.beta0,
            self.case.transcript.beta1,
            tuple(
                occurrence.initial_domain_index
                for occurrence in self.case.transcript.query_occurrences
            ),
            ResourceCounter(),
        )
        changed_request = canonical_relation_grounding_request(
            self.case.statement,
            changed_trace,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(request=changed_request, trace=changed_trace)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-054")

    def test_wrong_carrier_kind_is_malformed(self) -> None:
        result = check_fri_relation_grounding(
            self.case.request.identity,
            self.case.trace,
            self.case.public_inputs,
            self.case.proof,
        )
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-055")


class RepresentationClassificationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()

    def test_publication_projection_is_explicitly_directional_and_lossy(self) -> None:
        claim = RepresentationBoundaryDeclaration(
            RepresentationBoundary.LOGICAL_ORACLE_PUBLICATION,
            RepresentationClass.DIRECTIONAL_LOSSY_PROJECTION,
        )
        result = check_representation_boundary(claim)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(
            result.evidence["classification"],
            "DirectionalLossyProjection",
        )
        self.assertEqual(
            result.evidence["classification_status"],
            "DeclaredNotChecked",
        )
        self.assertIs(result.evidence["establishes_classification_truth"], False)
        self.assertIs(result.evidence["establishes_bridge_law"], False)

    def test_logical_oracle_to_cap_is_a_non_isomorphic_construction(self) -> None:
        claim = RepresentationBoundaryDeclaration(
            RepresentationBoundary.LOGICAL_ORACLE_COMMITMENT_CAP,
            RepresentationClass.NON_ISOMORPHIC_CONSTRUCTION_RELATION,
        )
        result = check_representation_boundary(claim)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(
            result.evidence["classification"],
            "NonIsomorphicConstructionRelation",
        )
        self.assertEqual(
            result.evidence["classification_status"],
            "DeclaredNotChecked",
        )
        self.assertIs(result.evidence["establishes_classification_truth"], False)
        self.assertIs(result.evidence["establishes_commitment_security"], False)

    def test_equivalence_or_embedding_labels_are_refused(self) -> None:
        candidates = (
            RepresentationBoundaryDeclaration(
                RepresentationBoundary.LOGICAL_ORACLE_PUBLICATION,
                RepresentationClass.TOTAL_EQUIVALENCE,
            ),
            RepresentationBoundaryDeclaration(
                RepresentationBoundary.LOGICAL_ORACLE_COMMITMENT_CAP,
                RepresentationClass.INJECTIVE_EMBEDDING,
            ),
        )
        for candidate in candidates:
            with self.subTest(candidate=candidate.to_term()):
                result = check_representation_boundary(candidate)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, "FRI-IOR-RELATION-048")

    def test_distinct_oracle_material_collides_under_publication_observation(
        self,
    ) -> None:
        entries = list(self.case.trace.initial_oracle.entries)
        entries[-1] = OracleEntry(
            entries[-1].point,
            entries[-1].value + _fp2(1),
        )
        changed = replace(self.case.trace.initial_oracle, entries=tuple(entries))
        self.assertNotEqual(
            logical_oracle_material_id(self.case.trace.initial_oracle),
            logical_oracle_material_id(changed),
        )
        self.assertEqual(
            self.case.trace.initial_oracle.publication_observation(),
            changed.publication_observation(),
        )
        result = check_logical_publication_loss(
            self.case.trace.initial_oracle,
            changed,
        )
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-RELATION-101")
        self.assertEqual(
            result.evidence["classification"],
            "DirectionalLossyProjection",
        )

    def test_identical_material_is_not_a_loss_witness(self) -> None:
        result = check_logical_publication_loss(
            self.case.trace.initial_oracle,
            self.case.trace.initial_oracle,
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-050")


class OuterRelationBoundaryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()
        cls.grounding = check_fri_relation_grounding(
            cls.case.request,
            cls.case.trace,
            cls.case.public_inputs,
            cls.case.proof,
        )
        if cls.grounding.subject is None:
            raise AssertionError(cls.grounding.to_term())
        cls.outer_relation_id = semantic_id(
            "outer-computation-relation",
            "fri-ior.test.outer-computation-relation.v1",
            {"name": "example-air-or-computation-relation"},
        )

    def test_acceptance_and_proximity_residual_cannot_infer_outer_relation(
        self,
    ) -> None:
        for premise in OuterInferencePremise:
            with self.subTest(premise=premise.value):
                request = OuterRelationInferenceRequest(
                    self.grounding.subject,
                    self.outer_relation_id,
                    premise,
                )
                result = infer_outer_computation_relation(request)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, "FRI-IOR-RELATION-069")

    def test_wrong_kind_grounding_cannot_be_used_as_an_inference_premise(self) -> None:
        request = OuterRelationInferenceRequest(
            self.case.trace.identity,
            self.outer_relation_id,
            OuterInferencePremise.ACCEPTING_EXECUTION,
        )
        result = infer_outer_computation_relation(request)
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(result.code, "FRI-IOR-RELATION-068")


class RelationCarrierFormationTest(unittest.TestCase):
    @staticmethod
    def _inert_id(label: str) -> SemanticId:
        return semantic_id(
            "test-inert-coordinate",
            "fri-ior.test.inert-coordinate.v1",
            {"label": label},
        )

    def test_statement_identity_is_canonical_over_map_order(self) -> None:
        left = RelationStatementOccurrence(EXACT_PROFILE.identity, 0, STATEMENT)
        right = RelationStatementOccurrence(
            EXACT_PROFILE.identity,
            0,
            {
                "initial_oracle_role": "relation-supplied",
                "profile": "f97-binary-two-round",
                "schema": "zkc.fri-ior.statement.v1",
            },
        )
        self.assertEqual(left.identity, right.identity)

    def test_host_container_subclass_is_not_a_closed_statement(self) -> None:
        class AmbientMap(dict):
            pass

        with self.assertRaises(ModelFailure) as caught:
            RelationStatementOccurrence(
                EXACT_PROFILE.identity,
                0,
                AmbientMap(STATEMENT),
            )
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-RELATION-002")

    def test_directly_constructed_result_records_are_explicitly_inert(self) -> None:
        ids = tuple(self._inert_id(str(index)) for index in range(5))
        opening = OpeningOccurrenceGrounding(
            0,
            FriOracleLayer.INITIAL,
            ids[0],
            ids[1],
            ids[2],
            ids[3],
            ids[4],
            0,
        )
        residual = FriTerminalResidualBoundary(
            ids[0],
            ids[1],
            ids[2],
            ids[3],
            "Accept",
        )
        for record in (opening, residual):
            with self.subTest(record=type(record).__name__):
                self.assertIs(record.is_checked_capability, False)
                self.assertEqual(
                    record.to_term()["authority"],
                    "portable-inert-record-no-live-check-capability",
                )
                self.assertTrue(record.identity.subject_kind.endswith("-record"))


if __name__ == "__main__":
    unittest.main()
