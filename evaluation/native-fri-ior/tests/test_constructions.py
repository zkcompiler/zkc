"""Tests for separate concrete construction-arrow evidence."""

from __future__ import annotations

import copy
from dataclasses import replace
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.constructions import (  # noqa: E402
    CheckedCommittedToWorkFreshRun,
    CheckedConstructionComposition,
    CheckedNativeToCommittedFreshRun,
    CommitmentAdvice,
    DecisionMap,
    ExactResourceUsage,
    FreshPublicEnvironment,
    check_committed_to_work_fresh,
    check_native_to_committed_fresh,
    compose_checked_constructions,
    generate_committed_to_work_fresh,
    generate_native_to_committed_fresh,
    verify_committed_fresh_run,
    verify_work_augmented_fresh_run,
)
from friiormodel.committed import (  # noqa: E402
    ExplicitCommittedFriExecution,
    verify_committed_fri,
    verify_explicit_committed_fri,
    verify_explicit_committed_prefix,
)
from friiormodel.commitment import EXACT_COMMITMENT_PROFILE  # noqa: E402
from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.fixtures import (  # noqa: E402
    LOADED_REPOSITORY_ROOT,
    load_fixture,
    parse_private_generation,
)
from friiormodel.generation import (  # noqa: E402
    CheckedNativeToCommittedExecution,
    PrivateFriGenerationMaterial,
    generate_honest_native_to_committed_execution,
)
from friiormodel.native import RandomQueryDraw  # noqa: E402
from friiormodel.profile import DEFAULT_VALIDATION_LIMITS, D2, EXACT_PROFILE  # noqa: E402
from friiormodel.proof import CommittedFriPublicInputs  # noqa: E402
from friiormodel.provenance import (  # noqa: E402
    ValidationBasisId,
    artifact_content_id,
)
from friiormodel.subjects import (  # noqa: E402
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    WORK_AUGMENTED_COMMITTED_FRI_CORE,
    FiatShamirChallengeInterpretation,
)
from friiormodel.terms import (  # noqa: E402
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    SemanticId,
    semantic_id,
)
from friiormodel.transcript import (  # noqa: E402
    CANONICAL_CONSTRUCTION_PLAN,
    FiatShamirTranscript,
    admit_construction_plan,
    derive_fiat_shamir_transcript,
)


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _other_id(label: str = "other") -> SemanticId:
    return semantic_id("test-subject", "fri-ior.test-subject.v1", label)


def _private_material() -> PrivateFriGenerationMaterial:
    fixture = load_fixture(
        LOADED_REPOSITORY_ROOT,
        "evaluation/native-fri-ior/cases/private-generation.json",
        "owner-local-private-generation",
    )
    parsed = parse_private_generation(fixture.value)
    return PrivateFriGenerationMaterial(
        parsed.coefficients,
        parsed.initial_layer_salts,
        parsed.first_fold_layer_salts,
    )


def _public_inputs() -> CommittedFriPublicInputs:
    fixture = load_fixture(
        LOADED_REPOSITORY_ROOT,
        "evaluation/native-fri-ior/cases/public-inputs.json",
        "public-inputs",
    )
    return CommittedFriPublicInputs(
        EXACT_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        fixture.value["statement"],
        fixture.value["application_context"],
    )


def _require_compilation(
    *,
    beta0: Fp2 = _fp2(7),
    beta1: Fp2 = _fp2(11),
    draws: tuple[int, ...] = (0, 7, 7, 15),
) -> CheckedNativeToCommittedFreshRun:
    public_inputs = _public_inputs()
    admission = generate_native_to_committed_fresh(
        _private_material(),
        public_inputs.statement,
        public_inputs.application_context,
        beta0,
        beta1,
        draws,
    )
    if admission.checked_receipt is None:
        raise AssertionError(admission.result.to_term())
    return admission.checked_receipt


def _require_grinding(
    compilation: CheckedNativeToCommittedFreshRun,
    *,
    seed: bytes = b"W" * 32,
) -> CheckedCommittedToWorkFreshRun:
    for nonce in range(32):
        admission = generate_committed_to_work_fresh(
            compilation,
            seed,
            nonce,
        )
        if admission.checked_receipt is not None:
            return admission.checked_receipt
        if admission.result.code != "FRI-IOR-CONSTRUCTION-032":
            raise AssertionError(admission.result.to_term())
    raise AssertionError("the bounded test prefix contained no valid nonce")


def _require_concrete_fiat_shamir_execution() -> CheckedNativeToCommittedExecution:
    admission = generate_honest_native_to_committed_execution(
        _private_material(),
        _public_inputs(),
    )
    if admission.checked_execution is None:
        raise AssertionError(admission.result.to_term())
    return admission.checked_execution


def _derive_concrete_transcript(
    checked: CheckedNativeToCommittedExecution,
) -> FiatShamirTranscript:
    artifacts = checked.public_artifacts
    inputs = artifacts.public_inputs
    proof = artifacts.proof
    derived = derive_fiat_shamir_transcript(
        inputs.transcript_plan,
        inputs.statement,
        inputs.application_context,
        proof.cap0,
        proof.cap1,
        proof.terminal_coefficients,
        proof.grinding_nonce,
        ResourceCounter(),
    )
    if not isinstance(derived, FiatShamirTranscript):
        raise AssertionError(derived.to_term())
    return derived


def _require_aligned_composition_inputs() -> tuple[
    CheckedNativeToCommittedFreshRun,
    CheckedCommittedToWorkFreshRun,
    CheckedNativeToCommittedExecution,
]:
    concrete = _require_concrete_fiat_shamir_execution()
    transcript = _derive_concrete_transcript(concrete)
    public_inputs = concrete.public_artifacts.public_inputs
    compilation_admission = generate_native_to_committed_fresh(
        _private_material(),
        public_inputs.statement,
        public_inputs.application_context,
        transcript.beta0,
        transcript.beta1,
        tuple(
            occurrence.initial_domain_index
            for occurrence in transcript.query_occurrences
        ),
    )
    if compilation_admission.checked_receipt is None:
        raise AssertionError(compilation_admission.result.to_term())
    grinding_admission = generate_committed_to_work_fresh(
        compilation_admission.checked_receipt,
        transcript.work_seed,
        transcript.grinding_nonce,
    )
    if grinding_admission.checked_receipt is None:
        raise AssertionError(grinding_admission.result.to_term())
    return (
        compilation_admission.checked_receipt,
        grinding_admission.checked_receipt,
        concrete,
    )


class PositiveConstructionEvidenceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.compilation = _require_compilation()
        cls.grinding = _require_grinding(cls.compilation)
        (
            cls.fs_compilation,
            cls.fs_grinding,
            cls.concrete_fs,
        ) = _require_aligned_composition_inputs()

    def test_committed_fresh_run_is_explicit_and_has_no_later_construction(
        self,
    ) -> None:
        run = self.compilation.target_run
        result = verify_committed_fresh_run(run)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-100")
        self.assertEqual(run.algebra_profile_id, EXACT_PROFILE.identity)
        self.assertEqual(
            run.commitment_profile_id,
            EXACT_COMMITMENT_PROFILE.identity,
        )
        self.assertEqual(run.beta0, _fp2(7))
        self.assertEqual(run.beta1, _fp2(11))
        public_inputs = _public_inputs()
        self.assertEqual(run.statement, public_inputs.statement)
        self.assertEqual(run.application_context, public_inputs.application_context)
        self.assertEqual(
            tuple(draw.initial_domain_index for draw in run.query_draws),
            (0, 7, 7, 15),
        )
        rendered = repr(run.to_term()).lower()
        for absent in (
            "fiat",
            "transcript_plan",
            "grinding_nonce",
            "work_seed",
            "query_seed",
        ):
            self.assertNotIn(absent, rendered)

    def test_compilation_receipt_has_all_required_maps_and_no_owner_advice(
        self,
    ) -> None:
        candidate = self.compilation.candidate
        self.assertIsInstance(
            candidate.source_public_environment,
            FreshPublicEnvironment,
        )
        self.assertEqual(len(candidate.public_environment_map), 2)
        self.assertTrue(
            all(
                item.source_value_id == item.target_value_id
                for item in candidate.public_environment_map
            )
        )
        self.assertEqual(len(candidate.publication_map), 2)
        self.assertEqual(len(candidate.coin_map), 6)
        self.assertEqual(len(candidate.query_occurrence_map), 4)
        self.assertEqual(len(candidate.extracted_answer_map), 8)
        self.assertEqual(candidate.decision_map, DecisionMap("Accept", "Accept"))
        self.assertTrue(candidate.terminal_map.to_term()["equal"])

        # Repeated logical occurrences remain distinct while selecting the
        # same deduplicated physical rows.
        selectors = candidate.target_run.occurrence_selectors
        self.assertNotEqual(
            candidate.query_occurrence_map[1].source_occurrence_id,
            candidate.query_occurrence_map[2].source_occurrence_id,
        )
        self.assertEqual(
            selectors[1].layer0_opening_index,
            selectors[2].layer0_opening_index,
        )
        self.assertEqual(
            selectors[1].layer1_opening_index,
            selectors[2].layer1_opening_index,
        )

        term = self.compilation.to_term()
        rendered = repr(term).lower()
        for absent in (
            "initial_layer_salts",
            "first_fold_layer_salts",
            "commitmentadvice",
            "complete_logical_oracle",
            "private_material",
        ):
            self.assertNotIn(absent, rendered)
        self.assertIsInstance(self.compilation.resource_usage, ExactResourceUsage)
        self.assertGreater(self.compilation.resource_usage.hash_calls, 0)
        self.assertGreater(self.compilation.resource_usage.field_operations, 0)

    def test_public_environment_is_copied_and_immutable(self) -> None:
        statement = {"relation": "mutable-source", "values": [1, 2]}
        context = {"application": "mutable-source", "flags": [True]}
        admission = generate_native_to_committed_fresh(
            _private_material(),
            statement,
            context,
            _fp2(7),
            _fp2(11),
            (0, 7, 7, 15),
        )
        self.assertIsNotNone(admission.checked_receipt)
        assert admission.checked_receipt is not None
        before = admission.checked_receipt.target_run.to_term()
        statement["values"].append(3)
        context["flags"].append(False)
        self.assertEqual(admission.checked_receipt.target_run.to_term(), before)

    def test_commitment_advice_has_no_portable_semantic_surface(self) -> None:
        private = _private_material()
        advice = CommitmentAdvice(
            private.initial_layer_salts,
            private.first_fold_layer_salts,
        )
        self.assertFalse(hasattr(advice, "to_term"))
        self.assertFalse(hasattr(advice, "identity"))
        rendered = repr(advice).lower()
        self.assertNotIn("salt", rendered)

    def test_work_receipt_preserves_every_source_occurrence_and_inserts_three(
        self,
    ) -> None:
        result = verify_work_augmented_fresh_run(self.grinding.target_run)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-102")
        candidate = self.grinding.candidate
        self.assertEqual(len(candidate.preserved_occurrence_map), 12)
        self.assertEqual(len(candidate.inserted_work_map), 3)
        terminal = next(
            item.target_index
            for item in candidate.preserved_occurrence_map
            if item.occurrence == "publish-terminal-polynomial"
        )
        query = next(
            item.target_index
            for item in candidate.preserved_occurrence_map
            if item.occurrence == "sample-fresh-ordered-query-occurrence-vector"
        )
        self.assertTrue(
            all(
                terminal < item.target_index < query
                for item in candidate.inserted_work_map
            )
        )
        self.assertEqual(candidate.decision_map, DecisionMap("Accept", "Accept"))

    def test_three_checked_arrows_compose_only_at_the_final_operation(self) -> None:
        admission = compose_checked_constructions(
            self.fs_compilation,
            self.fs_grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-104")
        self.assertIsInstance(
            admission.checked_receipt,
            CheckedConstructionComposition,
        )
        term = admission.checked_receipt.to_term()
        self.assertEqual(len(term["checked_arrows"]), 3)
        self.assertEqual(len(term["concrete_fiat_shamir_anchor"]), 3)
        self.assertEqual(len(term["exact_shared_subjects"]), 5)

    def test_receipts_bind_exact_checker_sources_and_keep_limits_nonsemantic(
        self,
    ) -> None:
        composition = compose_checked_constructions(
            self.fs_compilation,
            self.fs_grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
        ).checked_receipt
        self.assertIsNotNone(composition)
        receipts = (self.compilation, self.grinding, composition)
        source_root = Path(__file__).resolve().parents[1] / "friiormodel"
        for receipt in receipts:
            with self.subTest(receipt=type(receipt).__name__):
                self.assertIsInstance(receipt.validation_basis_id, ValidationBasisId)
                self.assertTrue(receipt.validation_source_manifest)
                for source in receipt.validation_source_manifest:
                    raw = (source_root / source.path).read_bytes()
                    self.assertEqual(
                        source.artifact_content_id,
                        str(artifact_content_id(raw)),
                    )
                    self.assertEqual(source.byte_length, len(raw))

        alternate_limits = replace(
            DEFAULT_VALIDATION_LIMITS,
            proof_bytes=DEFAULT_VALIDATION_LIMITS.proof_bytes + 1,
        )
        alternate_compilation = check_native_to_committed_fresh(
            self.compilation.candidate,
            alternate_limits,
        ).checked_receipt
        alternate_grinding = check_committed_to_work_fresh(
            self.grinding.candidate,
            alternate_limits,
        ).checked_receipt
        alternate_composition = compose_checked_constructions(
            self.fs_compilation,
            self.fs_grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
            alternate_limits,
        ).checked_receipt
        self.assertIsNotNone(alternate_compilation)
        self.assertIsNotNone(alternate_grinding)
        self.assertIsNotNone(alternate_composition)
        self.assertEqual(
            self.compilation.semantic_execution_id,
            alternate_compilation.semantic_execution_id,
        )
        self.assertNotEqual(
            self.compilation.validation_basis_id,
            alternate_compilation.validation_basis_id,
        )
        self.assertEqual(
            self.grinding.semantic_execution_id,
            alternate_grinding.semantic_execution_id,
        )
        self.assertNotEqual(
            self.grinding.validation_basis_id,
            alternate_grinding.validation_basis_id,
        )
        self.assertEqual(
            composition.semantic_composition_id,
            alternate_composition.semantic_composition_id,
        )
        self.assertNotEqual(
            composition.validation_basis_id,
            alternate_composition.validation_basis_id,
        )


class CommittedFreshRefusalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.compilation = _require_compilation()
        cls.fresh_run = cls.compilation.target_run

    def test_wrong_subject_draw_coverage_and_selector_shape_refuse(self) -> None:
        wrong_core = replace(self.fresh_run, core_id=_other_id("core"))
        result = verify_committed_fresh_run(wrong_core)
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-004")

        wrong_algebra = replace(
            self.fresh_run,
            algebra_profile_id=_other_id("algebra-profile"),
        )
        result = verify_committed_fresh_run(wrong_algebra)
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-004")

        wrong_commitment = replace(
            self.fresh_run,
            commitment_profile_id=_other_id("commitment-profile"),
        )
        result = verify_committed_fresh_run(wrong_commitment)
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-004")

        missing_draw = replace(
            self.fresh_run,
            query_draws=self.fresh_run.query_draws[:-1],
        )
        result = verify_committed_fresh_run(missing_draw)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-013")

        reordered_table = replace(
            self.fresh_run,
            opening_table=tuple(reversed(self.fresh_run.opening_table)),
        )
        result = verify_committed_fresh_run(reordered_table)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-010")

        missing_selector = replace(
            self.fresh_run,
            occurrence_selectors=self.fresh_run.occurrence_selectors[:-1],
        )
        result = verify_committed_fresh_run(missing_selector)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-013")

    def test_each_arithmetic_stage_has_a_reachable_refusal(self) -> None:
        result = verify_committed_fresh_run(replace(self.fresh_run, beta0=_fp2(8)))
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-020")

        result = verify_committed_fresh_run(replace(self.fresh_run, beta1=_fp2(12)))
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-021")

        # Add the quadratic vanishing at exactly the two sampled D2 points.
        # The sampled equations still hold, so the late semantic degree gate
        # is reached rather than being masked by an earlier fold refusal.
        root0 = Fp2.from_base(D2.points()[0])
        root3 = Fp2.from_base(D2.points()[3])
        vanishing = (root0 * root3, -(root0 + root3), Fp2.one())
        base = list(self.fresh_run.terminal_coefficients) + [Fp2.zero()]
        high_degree = tuple(base[index] + vanishing[index] for index in range(3))
        result = verify_committed_fresh_run(
            replace(self.fresh_run, terminal_coefficients=high_degree)
        )
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-022")

    def test_exact_carriers_and_private_limits_are_required(self) -> None:
        result = verify_committed_fresh_run(object())
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-011")
        result = verify_committed_fresh_run(self.fresh_run, ResourceCounter())
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-012")

        with self.assertRaises(ModelFailure) as usage_failure:
            ExactResourceUsage.from_counter(object())
        self.assertEqual(usage_failure.exception.code, "FRI-IOR-CONSTRUCTION-001")

        with self.assertRaises(ModelFailure) as advice_failure:
            CommitmentAdvice((), ())
        self.assertEqual(advice_failure.exception.code, "FRI-IOR-CONSTRUCTION-002")

        with self.assertRaises(ModelFailure) as run_failure:
            replace(self.fresh_run, cap0=None)
        self.assertEqual(run_failure.exception.code, "FRI-IOR-CONSTRUCTION-003")

    def test_receipt_cannot_be_formed_without_the_checker(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            CheckedNativeToCommittedFreshRun(
                self.compilation.candidate,
                self.compilation.validation_limits,
                self.compilation.resource_usage,
                _token=object(),
            )
        self.assertEqual(raised.exception.code, "FRI-IOR-CONSTRUCTION-013")


class SharedCommittedCoreVerifierTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.concrete_fs = _require_concrete_fiat_shamir_execution()
        cls.transcript = _derive_concrete_transcript(cls.concrete_fs)
        artifacts = cls.concrete_fs.public_artifacts
        cls.explicit = ExplicitCommittedFriExecution(
            artifacts.public_inputs.profile.identity,
            EXACT_COMMITMENT_PROFILE.identity,
            artifacts.proof.cap0,
            cls.transcript.beta0,
            artifacts.proof.cap1,
            cls.transcript.beta1,
            artifacts.proof.terminal_coefficients,
            tuple(
                RandomQueryDraw(
                    occurrence.ordinal,
                    occurrence.initial_domain_index,
                )
                for occurrence in cls.transcript.query_occurrences
            ),
            artifacts.proof.opening_table,
            artifacts.proof.occurrence_selectors,
        )

    def test_fresh_and_fiat_shamir_paths_delegate_to_the_same_core_checks(self) -> None:
        explicit_resources = ResourceCounter()
        explicit = verify_explicit_committed_fri(self.explicit, explicit_resources)
        artifacts = self.concrete_fs.public_artifacts
        fiat_shamir_resources = ResourceCounter()
        fiat_shamir = verify_committed_fri(
            artifacts.public_inputs,
            artifacts.proof,
            fiat_shamir_resources,
        )
        self.assertIs(explicit.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(explicit.code, "FRI-IOR-COMMITTED-101")
        self.assertIs(fiat_shamir.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(fiat_shamir.code, "FRI-IOR-COMMITTED-100")
        for key in (
            "beta0",
            "beta1",
            "ordered_initial_domain_indices",
            "random_draw_count",
            "logical_layer_query_occurrences",
            "unique_authenticated_openings",
            "first_fold_checks",
            "second_fold_checks",
            "establishes_outer_relation",
        ):
            with self.subTest(key=key):
                self.assertEqual(explicit.evidence[key], fiat_shamir.evidence[key])
        self.assertEqual(
            fiat_shamir_resources.snapshot()["proof_bytes"],
            artifacts.proof.canonical_byte_length,
        )
        self.assertEqual(
            fiat_shamir.evidence["proof_bytes"],
            artifacts.proof.canonical_byte_length,
        )
        self.assertEqual(
            explicit_resources.snapshot()["proof_bytes"],
            explicit.evidence["proof_bytes"],
        )

    def test_prefix_check_performs_no_query_or_opening_work(self) -> None:
        resources = ResourceCounter()
        result = verify_explicit_committed_prefix(self.explicit, resources)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-102")
        snapshot = resources.snapshot()
        self.assertEqual(snapshot["logical_query_occurrences"], 0)
        self.assertEqual(snapshot["unique_openings"], 0)
        self.assertEqual(snapshot["proof_bytes"], 0)

    def test_explicit_core_entry_points_require_exact_carriers(self) -> None:
        self.assertEqual(
            verify_explicit_committed_fri(object(), ResourceCounter()).code,
            "FRI-IOR-COMMITTED-005",
        )
        self.assertEqual(
            verify_explicit_committed_fri(self.explicit, object()).code,
            "FRI-IOR-COMMITTED-006",
        )
        self.assertEqual(
            verify_explicit_committed_prefix(object(), ResourceCounter()).code,
            "FRI-IOR-COMMITTED-007",
        )
        self.assertEqual(
            verify_explicit_committed_prefix(self.explicit, object()).code,
            "FRI-IOR-COMMITTED-008",
        )
        alternate_algebra_id = semantic_id(
            "fri-algebra-profile",
            "fri-ior.algebra-profile.v1",
            {"name": "alternate-algebra"},
        )
        self.assertEqual(
            verify_explicit_committed_fri(
                replace(
                    self.explicit,
                    algebra_profile_id=alternate_algebra_id,
                ),
                ResourceCounter(),
            ).code,
            "FRI-IOR-COMMITTED-009",
        )
        self.assertEqual(
            verify_explicit_committed_prefix(
                replace(
                    self.explicit,
                    algebra_profile_id=alternate_algebra_id,
                ),
                ResourceCounter(),
            ).code,
            "FRI-IOR-COMMITTED-023",
        )


class CommitmentCompilationMapRefusalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.receipt = _require_compilation()
        cls.candidate = cls.receipt.candidate

    def _code(self, candidate: object) -> str:
        return check_native_to_committed_fresh(candidate).result.code

    def test_carrier_declaration_cap_and_commutation_refusals(self) -> None:
        self.assertEqual(
            self._code(object()),
            "FRI-IOR-CONSTRUCTION-014",
        )
        self.assertEqual(
            self._code(replace(self.candidate, declaration_id=_other_id("decl"))),
            "FRI-IOR-CONSTRUCTION-015",
        )
        self.assertEqual(
            self._code(replace(self.candidate, source_public_environment=object())),
            "FRI-IOR-CONSTRUCTION-058",
        )
        changed_environment = FreshPublicEnvironment(
            {"statement": "different"},
            self.candidate.source_public_environment.application_context,
        )
        self.assertEqual(
            self._code(
                replace(
                    self.candidate,
                    source_public_environment=changed_environment,
                )
            ),
            "FRI-IOR-CONSTRUCTION-059",
        )
        self.assertEqual(
            self._code(
                replace(
                    self.candidate,
                    public_environment_map=self.candidate.public_environment_map[:-1],
                )
            ),
            "FRI-IOR-CONSTRUCTION-059",
        )
        salts = list(self.candidate.advice.initial_layer_salts)
        salts[0] = b"Z" * 16
        wrong_advice = CommitmentAdvice(
            tuple(salts),
            self.candidate.advice.first_fold_layer_salts,
        )
        self.assertEqual(
            self._code(replace(self.candidate, advice=wrong_advice)),
            "FRI-IOR-CONSTRUCTION-016",
        )

        changed_draws = tuple(RandomQueryDraw(ordinal, ordinal) for ordinal in range(4))
        changed_source = replace(
            self.candidate.source_trace,
            query_draws=changed_draws,
        )
        self.assertEqual(
            self._code(replace(self.candidate, source_trace=changed_source)),
            "FRI-IOR-CONSTRUCTION-017",
        )

    def test_every_claimed_compilation_map_is_recomputed(self) -> None:
        cases = (
            (
                replace(
                    self.candidate,
                    publication_map=self.candidate.publication_map[:-1],
                ),
                "FRI-IOR-CONSTRUCTION-018",
            ),
            (
                replace(self.candidate, coin_map=self.candidate.coin_map[:-1]),
                "FRI-IOR-CONSTRUCTION-019",
            ),
            (
                replace(
                    self.candidate,
                    query_occurrence_map=self.candidate.query_occurrence_map[:-1],
                ),
                "FRI-IOR-CONSTRUCTION-020",
            ),
            (
                replace(
                    self.candidate,
                    extracted_answer_map=self.candidate.extracted_answer_map[:-1],
                ),
                "FRI-IOR-CONSTRUCTION-021",
            ),
            (
                replace(
                    self.candidate,
                    terminal_map=replace(
                        self.candidate.terminal_map,
                        target_terminal_id=_other_id("terminal"),
                    ),
                ),
                "FRI-IOR-CONSTRUCTION-022",
            ),
            (
                replace(
                    self.candidate,
                    decision_map=DecisionMap("Accept", "Reject"),
                ),
                "FRI-IOR-CONSTRUCTION-023",
            ),
        )
        for candidate, expected in cases:
            with self.subTest(expected=expected):
                self.assertEqual(self._code(candidate), expected)

    def test_generation_rejects_wrong_private_and_fresh_inputs(self) -> None:
        result = generate_native_to_committed_fresh(
            object(),
            {},
            {},
            _fp2(7),
            _fp2(11),
            (0, 7, 7, 15),
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-024")

        result = generate_native_to_committed_fresh(
            _private_material(),
            {},
            {},
            object(),
            _fp2(11),
            (0, 7, 7, 15),
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-025")

        result = generate_native_to_committed_fresh(
            _private_material(),
            {},
            {},
            _fp2(7),
            _fp2(11),
            [0, 7, 7, 15],
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-026")

        result = generate_native_to_committed_fresh(
            _private_material(),
            {1: "non-text-key"},
            {},
            _fp2(7),
            _fp2(11),
            (0, 7, 7, 15),
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-055")

        result = generate_native_to_committed_fresh(
            _private_material(),
            object(),
            {},
            _fp2(7),
            _fp2(11),
            (0, 7, 7, 15),
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-056")

        class PublicEnvironmentProxy(FreshPublicEnvironment):
            pass

        with self.assertRaises(ModelFailure) as raised:
            PublicEnvironmentProxy({}, {})
        self.assertEqual(raised.exception.code, "FRI-IOR-CONSTRUCTION-057")


class GrindingAugmentationRefusalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.compilation = _require_compilation()
        cls.grinding = _require_grinding(cls.compilation)
        cls.candidate = cls.grinding.candidate

    def _code(self, candidate: object) -> str:
        return check_committed_to_work_fresh(candidate).result.code

    def test_invalid_nonce_is_a_target_only_refusal(self) -> None:
        source_before = self.compilation.identity
        admission = generate_committed_to_work_fresh(
            self.compilation,
            b"W" * 32,
            0,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-032")
        self.assertEqual(admission.result.evidence["source_verdict"], "Accept")
        self.assertEqual(admission.result.evidence["target_verdict"], "Reject")
        self.assertIs(admission.result.evidence["target_only"], True)
        self.assertIs(
            admission.result.evidence["rejection_before_query_suffix"],
            True,
        )
        target_usage = admission.result.evidence["target_resource_usage"]
        self.assertEqual(target_usage["logical_query_occurrences"], 0)
        self.assertEqual(target_usage["unique_openings"], 0)
        self.assertEqual(target_usage["proof_bytes"], 0)
        self.assertEqual(target_usage["sampler_attempts"], 0)
        self.assertIsNone(admission.checked_receipt)
        self.assertEqual(self.compilation.identity, source_before)
        self.assertIs(
            verify_committed_fresh_run(self.compilation.target_run).outcome,
            OutcomeClass.AFFIRMATIVE,
        )

    def test_work_value_and_subject_refusals_are_distinct(self) -> None:
        target = self.candidate.target_run
        result = verify_work_augmented_fresh_run(
            replace(target, core_id=_other_id("work-core"))
        )
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-030")

        altered_digest = bytes((target.work_digest[0] ^ 1,)) + target.work_digest[1:]
        result = verify_work_augmented_fresh_run(
            replace(target, work_digest=altered_digest)
        )
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-031")

        result = verify_work_augmented_fresh_run(object())
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-033")

    def test_work_generation_validates_seed_nonce_and_receipt_carriers(self) -> None:
        result = generate_committed_to_work_fresh(
            self.compilation,
            b"short",
            0,
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-027")
        result = generate_committed_to_work_fresh(
            self.compilation,
            b"W" * 32,
            -1,
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-028")
        result = generate_committed_to_work_fresh(
            object(),
            b"W" * 32,
            3,
        ).result
        self.assertEqual(result.code, "FRI-IOR-CONSTRUCTION-042")

        with self.assertRaises(ModelFailure) as raised:
            replace(self.candidate.target_run, work_seed=b"short")
        self.assertEqual(raised.exception.code, "FRI-IOR-CONSTRUCTION-029")

    def test_grinding_checker_recomputes_every_map_and_join(self) -> None:
        self.assertEqual(self._code(object()), "FRI-IOR-CONSTRUCTION-035")
        self.assertEqual(
            self._code(replace(self.candidate, declaration_id=_other_id("grind"))),
            "FRI-IOR-CONSTRUCTION-036",
        )

        other = _require_compilation(beta0=_fp2(9))
        self.assertEqual(
            self._code(replace(self.candidate, source_run=other.target_run)),
            "FRI-IOR-CONSTRUCTION-037",
        )
        self.assertEqual(
            self._code(
                replace(
                    self.candidate,
                    preserved_occurrence_map=(
                        self.candidate.preserved_occurrence_map[:-1]
                    ),
                )
            ),
            "FRI-IOR-CONSTRUCTION-038",
        )
        wrong_value = replace(
            self.candidate.inserted_work_map[0],
            value_id=_other_id("work-value"),
        )
        self.assertEqual(
            self._code(
                replace(
                    self.candidate,
                    inserted_work_map=(
                        wrong_value,
                        *self.candidate.inserted_work_map[1:],
                    ),
                )
            ),
            "FRI-IOR-CONSTRUCTION-039",
        )
        wrong_position = replace(
            self.candidate.inserted_work_map[0],
            target_index=0,
        )
        self.assertEqual(
            self._code(
                replace(
                    self.candidate,
                    inserted_work_map=(
                        wrong_position,
                        *self.candidate.inserted_work_map[1:],
                    ),
                )
            ),
            "FRI-IOR-CONSTRUCTION-040",
        )
        self.assertEqual(
            self._code(
                replace(
                    self.candidate,
                    decision_map=DecisionMap("Accept", "Reject"),
                )
            ),
            "FRI-IOR-CONSTRUCTION-041",
        )

    def test_grinding_receipt_cannot_be_formed_without_the_checker(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            CheckedCommittedToWorkFreshRun(
                self.candidate,
                self.grinding.validation_limits,
                self.grinding.resource_usage,
                _token=object(),
            )
        self.assertEqual(raised.exception.code, "FRI-IOR-CONSTRUCTION-034")


class CompositionAndIsolationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        (
            cls.compilation,
            cls.grinding,
            cls.concrete_fs,
        ) = _require_aligned_composition_inputs()

    def test_composition_rejects_proxies_wrong_subjects_and_stale_joins(self) -> None:
        admission = compose_checked_constructions(
            self.compilation.identity,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-044")

        forged_fs = copy.copy(CHECKED_FIAT_SHAMIR_CONSTRUCTION)
        object.__setattr__(forged_fs, "protection_map", forged_fs.protection_map[:-1])
        admission = compose_checked_constructions(
            self.compilation,
            self.grinding,
            forged_fs,
            self.concrete_fs,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-045")

        forged_compilation = copy.copy(self.compilation)
        object.__setattr__(
            forged_compilation,
            "candidate",
            replace(
                self.compilation.candidate,
                declaration_id=_other_id("composition-subject"),
            ),
        )
        admission = compose_checked_constructions(
            forged_compilation,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-046")

        other = _require_compilation(beta0=_fp2(9))
        admission = compose_checked_constructions(
            other,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-047")

    def test_composition_receipt_requires_the_issuing_operation(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            CheckedConstructionComposition(
                self.compilation,
                self.grinding,
                CHECKED_FIAT_SHAMIR_CONSTRUCTION,
                self.concrete_fs,
                DEFAULT_VALIDATION_LIMITS,
                ExactResourceUsage.from_counter(ResourceCounter()),
                _token=object(),
            )
        self.assertEqual(raised.exception.code, "FRI-IOR-CONSTRUCTION-043")

    def test_concrete_fiat_shamir_anchor_is_checked_at_each_join(self) -> None:
        wrong_subject_candidate = replace(
            self.concrete_fs.candidate,
            checked_fiat_shamir_construction_id=_other_id("checked-fs"),
        )
        wrong_subject = copy.copy(self.concrete_fs)
        object.__setattr__(wrong_subject, "candidate", wrong_subject_candidate)
        admission = compose_checked_constructions(
            self.compilation,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            wrong_subject,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-048")

        other = _require_compilation(beta0=_fp2(9))
        wrong_source_candidate = replace(
            self.concrete_fs.candidate,
            source_trace=other.candidate.source_trace,
            claimed_source_trace_id=other.candidate.source_trace.identity,
        )
        wrong_source = copy.copy(self.concrete_fs)
        object.__setattr__(wrong_source, "candidate", wrong_source_candidate)
        admission = compose_checked_constructions(
            self.compilation,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            wrong_source,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-049")

        artifacts = self.concrete_fs.public_artifacts
        wrong_proof = replace(
            artifacts.proof,
            grinding_nonce=artifacts.proof.grinding_nonce + 1,
        )
        wrong_messages_candidate = replace(
            self.concrete_fs.candidate,
            public_artifacts=replace(artifacts, proof=wrong_proof),
        )
        wrong_messages = copy.copy(self.concrete_fs)
        object.__setattr__(wrong_messages, "candidate", wrong_messages_candidate)
        admission = compose_checked_constructions(
            self.compilation,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            wrong_messages,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-050")

        wrong_context_inputs = CommittedFriPublicInputs(
            artifacts.public_inputs.profile,
            artifacts.public_inputs.transcript_plan,
            artifacts.public_inputs.statement,
            {"application": "different-public-environment"},
        )
        wrong_context_candidate = replace(
            self.concrete_fs.candidate,
            public_artifacts=replace(
                artifacts,
                public_inputs=wrong_context_inputs,
            ),
        )
        wrong_context = copy.copy(self.concrete_fs)
        object.__setattr__(wrong_context, "candidate", wrong_context_candidate)
        admission = compose_checked_constructions(
            self.compilation,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            wrong_context,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-050")

        changed_run = replace(
            self.compilation.target_run,
            beta0=_fp2(self.compilation.target_run.beta0.real.value + 1),
        )
        wrong_compilation_candidate = replace(
            self.compilation.candidate,
            target_run=changed_run,
        )
        wrong_compilation = copy.copy(self.compilation)
        object.__setattr__(
            wrong_compilation,
            "candidate",
            wrong_compilation_candidate,
        )
        changed_work_run = replace(
            self.grinding.target_run,
            source_run=changed_run,
        )
        wrong_grinding_candidate = replace(
            self.grinding.candidate,
            source_run=changed_run,
            target_run=changed_work_run,
        )
        wrong_grinding = copy.copy(self.grinding)
        object.__setattr__(wrong_grinding, "candidate", wrong_grinding_candidate)
        admission = compose_checked_constructions(
            wrong_compilation,
            wrong_grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-051")

        admission = compose_checked_constructions(
            self.compilation,
            self.grinding,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            self.concrete_fs,
            ResourceCounter(),
        )
        self.assertEqual(admission.result.code, "FRI-IOR-CONSTRUCTION-052")

    def test_grinding_changes_do_not_retroactively_change_compilation(self) -> None:
        identity = self.compilation.identity
        first = _require_grinding(self.compilation, seed=b"W" * 32)
        second = _require_grinding(self.compilation, seed=b"X" * 32)
        self.assertEqual(self.compilation.identity, identity)
        self.assertNotEqual(first.identity, second.identity)
        self.assertEqual(
            first.candidate.source_run.identity,
            second.candidate.source_run.identity,
        )

    def test_unsupported_fs_plan_does_not_change_either_earlier_receipt(self) -> None:
        compilation_id = self.compilation.identity
        grinding_id = self.grinding.identity
        alternate_law = semantic_id(
            "fri-ior-semantic-law",
            "fri-ior.semantic-law.v1",
            {"name": "alternate-transcript-hash-law"},
        )
        alternate = replace(
            CANONICAL_CONSTRUCTION_PLAN,
            semantic_law_ids=(
                alternate_law,
                *CANONICAL_CONSTRUCTION_PLAN.semantic_law_ids[1:],
            ),
        )
        result = admit_construction_plan(alternate)
        self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-019")
        with self.assertRaises(ModelFailure) as raised:
            FiatShamirChallengeInterpretation(
                WORK_AUGMENTED_COMMITTED_FRI_CORE,
                alternate,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(raised.exception.code, "FRI-IOR-SUBJECT-003")
        self.assertEqual(self.compilation.identity, compilation_id)
        self.assertEqual(self.grinding.identity, grinding_id)


class ConstructionDiagnosticInventoryTest(unittest.TestCase):
    def test_every_construction_diagnostic_is_named_by_the_suite(self) -> None:
        """Keep additions visible; fault-only source-load errors stay explicit."""

        expected = {
            f"FRI-IOR-CONSTRUCTION-{number:03d}"
            for number in range(1, 60)
            if number not in range(5, 11)
        } | {
            "FRI-IOR-CONSTRUCTION-100",
            "FRI-IOR-CONSTRUCTION-101",
            "FRI-IOR-CONSTRUCTION-102",
            "FRI-IOR-CONSTRUCTION-103",
            "FRI-IOR-CONSTRUCTION-104",
        }
        source = (
            Path(__file__).resolve().parents[1] / "friiormodel" / "constructions.py"
        ).read_text(encoding="utf-8")
        actual = {
            token.strip('"')
            for token in source.replace("'", '"').split()
            if token.strip('" ,).').startswith("FRI-IOR-CONSTRUCTION-")
            for token in (token.strip(" ,)."),)
        }
        self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
