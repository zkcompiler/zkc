"""Tests for exact finite FRI relation and occurrence grounding."""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
import inspect
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.constructions import (  # noqa: E402
    CheckedConstructionComposition,
    CheckedNativeToCommittedFreshRun,
    compose_checked_constructions,
    generate_committed_to_work_fresh,
    generate_native_to_committed_fresh,
)
from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.generation import (  # noqa: E402
    PrivateFriGenerationMaterial,
    generate_honest_native_to_committed_execution,
)
from friiormodel.native import (  # noqa: E402
    LogicalOracle,
    NativeFriTrace,
    OracleEntry,
)
from friiormodel.profile import D0, EXACT_PROFILE  # noqa: E402
from friiormodel.proof import (  # noqa: E402
    CommittedFriPublicInputs,
    PublicFriProof,
)
from friiormodel.relations import (  # noqa: E402
    CapOccurrenceReference,
    CheckedFriRelationGrounding,
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
from friiormodel.subjects import CHECKED_FIAT_SHAMIR_CONSTRUCTION  # noqa: E402
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


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _salts(prefix: int, pair_count: int) -> tuple[bytes, ...]:
    return tuple(bytes((prefix + index,)) * 16 for index in range(pair_count))


@dataclass(frozen=True, slots=True)
class _Case:
    public_inputs: CommittedFriPublicInputs
    proof: PublicFriProof
    transcript: FiatShamirTranscript
    trace: NativeFriTrace
    relation_initial_oracle: LogicalOracle
    commitment_receipt: CheckedNativeToCommittedFreshRun
    composition_receipt: CheckedConstructionComposition
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
    private_material = PrivateFriGenerationMaterial(
        source_coefficients,
        _salts(0x10, D0.order // 2),
        _salts(0x40, 4),
    )
    concrete_admission = generate_honest_native_to_committed_execution(
        private_material,
        public_inputs,
    )
    if concrete_admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
        raise AssertionError(concrete_admission.result.to_term())
    if concrete_admission.checked_execution is None:
        raise AssertionError("affirmative concrete generation omitted its receipt")
    concrete = concrete_admission.checked_execution
    proof = concrete.public_artifacts.proof
    trace = concrete.candidate.source_trace

    transcript = construct_fiat_shamir_transcript(
        public_inputs.transcript_plan,
        public_inputs.statement,
        public_inputs.application_context,
        proof.cap0,
        proof.cap1,
        proof.terminal_coefficients,
        ResourceCounter(),
    )
    if isinstance(transcript, CheckResult):
        raise AssertionError(transcript.to_term())
    if transcript.beta0 != trace.beta0 or transcript.beta1 != trace.beta1:
        raise AssertionError(
            "the issued concrete construction and transcript replay disagree"
        )
    query_indices = tuple(
        occurrence.initial_domain_index for occurrence in transcript.query_occurrences
    )
    commitment_admission = generate_native_to_committed_fresh(
        private_material,
        STATEMENT,
        APPLICATION_CONTEXT,
        transcript.beta0,
        transcript.beta1,
        query_indices,
    )
    if commitment_admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
        raise AssertionError(commitment_admission.result.to_term())
    if commitment_admission.checked_receipt is None:
        raise AssertionError("affirmative commitment construction omitted its receipt")
    commitment_receipt = commitment_admission.checked_receipt
    grinding_admission = generate_committed_to_work_fresh(
        commitment_receipt,
        transcript.work_seed,
        proof.grinding_nonce,
    )
    if grinding_admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
        raise AssertionError(grinding_admission.result.to_term())
    if grinding_admission.checked_receipt is None:
        raise AssertionError("affirmative grinding construction omitted its receipt")
    composition_admission = compose_checked_constructions(
        commitment_receipt,
        grinding_admission.checked_receipt,
        CHECKED_FIAT_SHAMIR_CONSTRUCTION,
        concrete,
    )
    if composition_admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
        raise AssertionError(composition_admission.result.to_term())
    if composition_admission.checked_receipt is None:
        raise AssertionError("affirmative construction composition omitted its receipt")
    composition_receipt = composition_admission.checked_receipt

    relation_initial_oracle = replace(trace.initial_oracle)
    statement = RelationStatementOccurrence(EXACT_PROFILE.identity, 0, STATEMENT)
    request = canonical_relation_grounding_request(
        statement,
        relation_initial_oracle,
        commitment_receipt,
        composition_receipt,
        public_inputs,
        proof,
    )
    return _Case(
        public_inputs,
        proof,
        transcript,
        trace,
        relation_initial_oracle,
        commitment_receipt,
        composition_receipt,
        statement,
        request,
        source_coefficients,
    )


class RelationGroundingPositiveTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()
        cls.admission = check_fri_relation_grounding(
            cls.case.request,
            cls.case.relation_initial_oracle,
            cls.case.commitment_receipt,
            cls.case.composition_receipt,
            cls.case.public_inputs,
            cls.case.proof,
        )
        cls.result = cls.admission.result
        if cls.admission.checked_grounding is None:
            raise AssertionError(cls.result.to_term())
        cls.checked = cls.admission.checked_grounding

    def test_exact_statement_oracle_cap_and_run_grounding_accepts(self) -> None:
        self.assertIs(self.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(self.result.code, "FRI-IOR-RELATION-102")
        self.assertIsInstance(self.result.subject, SemanticId)
        self.assertEqual(
            self.result.subject.subject_kind,
            "checked-fri-relation-grounding",
        )
        self.assertIsInstance(self.checked, CheckedFriRelationGrounding)
        self.assertEqual(self.result.subject, self.checked.identity)
        self.assertEqual(
            self.checked.commitment_receipt_id,
            self.case.commitment_receipt.identity,
        )
        self.assertEqual(
            self.checked.construction_composition_receipt_id,
            self.case.composition_receipt.identity,
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
        self.assertEqual(
            evidence["unique_physical_opening_count"],
            len(self.case.proof.opening_table),
        )
        self.assertLess(evidence["unique_physical_opening_count"], 8)
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
            (
                "request",
                "relation_initial_oracle",
                "commitment_receipt",
                "composition_receipt",
                "public_inputs",
                "proof",
            ),
        )
        self.assertEqual(
            {item.name for item in fields(FriRelationGroundingRequest)},
            {
                "statement",
                "initial_oracle_binding",
                "commitment_receipt_id",
                "construction_composition_receipt_id",
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
        relation_initial_oracle: LogicalOracle | None = None,
        commitment_receipt: CheckedNativeToCommittedFreshRun | None = None,
        composition_receipt: CheckedConstructionComposition | None = None,
    ) -> CheckResult:
        admission = check_fri_relation_grounding(
            self.case.request if request is None else request,
            (
                self.case.relation_initial_oracle
                if relation_initial_oracle is None
                else relation_initial_oracle
            ),
            (
                self.case.commitment_receipt
                if commitment_receipt is None
                else commitment_receipt
            ),
            (
                self.case.composition_receipt
                if composition_receipt is None
                else composition_receipt
            ),
            self.case.public_inputs,
            self.case.proof,
        )
        self.assertIsNone(admission.checked_grounding)
        return admission.result

    def test_statement_substitution_refuses_before_execution(self) -> None:
        statement = RelationStatementOccurrence(
            EXACT_PROFILE.identity,
            0,
            {**STATEMENT, "initial_oracle_role": "substituted"},
        )
        request = canonical_relation_grounding_request(
            statement,
            self.case.relation_initial_oracle,
            self.case.commitment_receipt,
            self.case.composition_receipt,
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
            self.case.relation_initial_oracle,
            self.case.commitment_receipt,
            self.case.composition_receipt,
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

    def test_inert_receipt_id_cannot_replace_the_live_capability(self) -> None:
        wrong = semantic_id(
            "checked-native-to-committed-fresh-execution",
            "fri-ior.checked-native-to-committed-fresh-execution.v1",
            {"different": True},
        )
        result = self._check(
            request=replace(self.case.request, commitment_receipt_id=wrong)
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

    def test_relation_oracle_is_supplied_independently_from_the_trace(self) -> None:
        entries = list(self.case.relation_initial_oracle.entries)
        entries[-1] = OracleEntry(entries[-1].point, entries[-1].value + _fp2(1))
        changed_oracle = replace(
            self.case.relation_initial_oracle,
            entries=tuple(entries),
        )
        changed_request = canonical_relation_grounding_request(
            self.case.statement,
            changed_oracle,
            self.case.commitment_receipt,
            self.case.composition_receipt,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(
            request=changed_request,
            relation_initial_oracle=changed_oracle,
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-078")

    def test_two_live_receipts_must_form_the_checked_join(self) -> None:
        changed_coefficients = list(self.case.source_coefficients)
        changed_coefficients[0] = changed_coefficients[0] + _fp2(1)
        alternate_material = PrivateFriGenerationMaterial(
            tuple(changed_coefficients),
            _salts(0x10, D0.order // 2),
            _salts(0x40, 4),
        )
        query_indices = tuple(
            occurrence.initial_domain_index
            for occurrence in self.case.transcript.query_occurrences
        )
        alternate_admission = generate_native_to_committed_fresh(
            alternate_material,
            STATEMENT,
            APPLICATION_CONTEXT,
            self.case.transcript.beta0,
            self.case.transcript.beta1,
            query_indices,
        )
        self.assertIs(
            alternate_admission.result.outcome,
            OutcomeClass.AFFIRMATIVE,
        )
        self.assertIsNotNone(alternate_admission.checked_receipt)
        assert alternate_admission.checked_receipt is not None
        alternate_receipt = alternate_admission.checked_receipt
        mixed_request = canonical_relation_grounding_request(
            self.case.statement,
            replace(alternate_receipt.candidate.source_trace.initial_oracle),
            alternate_receipt,
            self.case.composition_receipt,
            self.case.public_inputs,
            self.case.proof,
        )
        result = self._check(
            request=mixed_request,
            relation_initial_oracle=replace(
                alternate_receipt.candidate.source_trace.initial_oracle
            ),
            commitment_receipt=alternate_receipt,
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-074")

    def test_wrong_carrier_kind_is_malformed(self) -> None:
        admission = check_fri_relation_grounding(
            self.case.request.identity,
            self.case.relation_initial_oracle,
            self.case.commitment_receipt,
            self.case.composition_receipt,
            self.case.public_inputs,
            self.case.proof,
        )
        result = admission.result
        self.assertIsNone(admission.checked_grounding)
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-RELATION-055")

    def test_receipt_ids_are_not_accepted_as_live_receipts(self) -> None:
        candidates = (
            (
                self.case.commitment_receipt.identity,
                self.case.composition_receipt,
                "FRI-IOR-RELATION-057",
            ),
            (
                self.case.commitment_receipt,
                self.case.composition_receipt.identity,
                "FRI-IOR-RELATION-058",
            ),
        )
        for commitment, composition, code in candidates:
            with self.subTest(code=code):
                admission = check_fri_relation_grounding(
                    self.case.request,
                    self.case.relation_initial_oracle,
                    commitment,
                    composition,
                    self.case.public_inputs,
                    self.case.proof,
                )
                self.assertIs(admission.result.outcome, OutcomeClass.MALFORMED)
                self.assertEqual(admission.result.code, code)
                self.assertIsNone(admission.checked_grounding)


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
        cls.admission = check_fri_relation_grounding(
            cls.case.request,
            cls.case.relation_initial_oracle,
            cls.case.commitment_receipt,
            cls.case.composition_receipt,
            cls.case.public_inputs,
            cls.case.proof,
        )
        if cls.admission.checked_grounding is None:
            raise AssertionError(cls.admission.result.to_term())
        cls.grounding = cls.admission.checked_grounding
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
                    self.grounding,
                    self.outer_relation_id,
                    premise,
                )
                result = infer_outer_computation_relation(request)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, "FRI-IOR-RELATION-069")

    def test_id_shaped_pseudo_grounding_is_rejected_at_formation(self) -> None:
        pseudo = semantic_id(
            "checked-fri-relation-grounding",
            "fri-ior.relations.checked-grounding.v2",
            {"looks": "plausible"},
        )
        with self.assertRaises(ModelFailure) as caught:
            OuterRelationInferenceRequest(
                pseudo,
                self.outer_relation_id,
                OuterInferencePremise.ACCEPTING_EXECUTION,
            )
        self.assertEqual(caught.exception.code, "FRI-IOR-RELATION-060")

    def test_defensive_inference_boundary_rechecks_the_live_capability(self) -> None:
        forged = object.__new__(OuterRelationInferenceRequest)
        object.__setattr__(forged, "grounding", self.case.trace.identity)
        object.__setattr__(forged, "outer_relation_id", self.outer_relation_id)
        object.__setattr__(
            forged,
            "premise",
            OuterInferencePremise.ACCEPTING_EXECUTION,
        )
        result = infer_outer_computation_relation(forged)
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

    def test_cap_reference_wrong_layer_has_a_typed_failure(self) -> None:
        ids = tuple(self._inert_id(str(index)) for index in range(2))
        with self.assertRaises(ModelFailure) as caught:
            CapOccurrenceReference(
                "initial",
                "cap[0]",
                ids[0],
                ids[1],
            )
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-RELATION-013")

    def test_checked_grounding_cannot_be_directly_issued(self) -> None:
        with self.assertRaises(ModelFailure) as caught:
            CheckedFriRelationGrounding(
                None,
                None,
                None,
                None,
                (),
                None,
                {},
                _token=object(),
            )
        self.assertIs(caught.exception.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(caught.exception.code, "FRI-IOR-RELATION-079")


if __name__ == "__main__":
    unittest.main()
