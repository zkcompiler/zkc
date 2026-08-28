"""Tests for the separately coded public replay verifier."""

from __future__ import annotations

import ast
from copy import deepcopy
from dataclasses import dataclass
import inspect
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import independent  # noqa: E402
from friiormodel.commitment import (  # noqa: E402
    EXACT_COMMITMENT_PROFILE,
    CommitmentTree,
    build_commitment,
)
from friiormodel.field import Fp, Fp2, evaluate_polynomial  # noqa: E402
from friiormodel.profile import (  # noqa: E402
    D0,
    D1,
    DEFAULT_VALIDATION_LIMITS,
    EXACT_ALGEBRA_PROFILE,
)
from friiormodel.proof import (  # noqa: E402
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
)
from friiormodel.terms import CheckResult, ResourceCounter, encode_term  # noqa: E402
from friiormodel.transcript import (  # noqa: E402
    CANONICAL_CONSTRUCTION_PLAN,
    EXACT_GRINDING_PROFILE,
    FiatShamirTranscript,
    _begin_transcript,
    _continue_transcript,
    construct_fiat_shamir_transcript,
)


STATEMENT = {
    "schema": "zkc.fri-ior.statement.v1",
    "profile": "f97-binary-two-round",
    "initial_oracle_role": "relation-supplied",
}
APPLICATION_CONTEXT = {
    "application": "native-fri-ior-validation",
    "case": "independent-replay",
    "suffix": 71394,
}
PRIMARY_COEFFICIENTS = (3, 5, 7, 11, 13, 17, 19, 23)


def _json(value):
    return json.loads(json.dumps(value))


def _public_terms(case):
    return _json(case.public_inputs.to_term()), _json(case.proof.to_term())


def _first_failing_nonce(inputs, proof):
    for nonce in range(64):
        candidate = deepcopy(proof)
        candidate["grinding_nonce"] = nonce
        result = independent.verify_public_fri(inputs, candidate)
        if result["code"] == "FRI-IOR-INDEPENDENT-026":
            return nonce
    raise AssertionError("the bounded test search found no failing work nonce")


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _fold_coefficients(
    coefficients: tuple[Fp2, ...], challenge: Fp2
) -> tuple[Fp2, ...]:
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
    corrupt_first_fold: bool = False,
    terminal_transform=None,
) -> _PublicCase:
    public_inputs = CommittedFriPublicInputs(
        EXACT_ALGEBRA_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        STATEMENT,
        APPLICATION_CONTEXT,
    )
    source_coefficients = tuple(_fp2(value) for value in coefficient_values)
    initial_evaluations = tuple(
        evaluate_polynomial(source_coefficients, point) for point in D0.points()
    )
    tree0 = build_commitment(
        D0,
        initial_evaluations,
        _salts(0x10, D0.order // 2),
    )
    first_round = _begin_transcript(
        public_inputs.transcript_plan,
        public_inputs.statement,
        public_inputs.application_context,
        tree0.cap,
        ResourceCounter(),
    )
    if isinstance(first_round, CheckResult):
        raise AssertionError(first_round.to_term())

    first_fold_coefficients = _fold_coefficients(source_coefficients, first_round.beta0)
    first_fold_evaluations = [
        evaluate_polynomial(first_fold_coefficients, point) for point in D1.points()
    ]
    if corrupt_first_fold:
        first_fold_evaluations = [value + _fp2(1) for value in first_fold_evaluations]
    tree1 = build_commitment(
        D1,
        tuple(first_fold_evaluations),
        _salts(0x40, D1.order // 2),
    )
    second_round = _continue_transcript(first_round, tree1.cap, ResourceCounter())
    if isinstance(second_round, CheckResult):
        raise AssertionError(second_round.to_term())

    terminal = _fold_coefficients(first_fold_coefficients, second_round.beta1)
    if terminal_transform is not None:
        terminal = terminal_transform(terminal)
    proof, transcript = _assemble_proof(public_inputs, tree0, tree1, terminal)
    if transcript.beta0 != first_round.beta0 or transcript.beta1 != second_round.beta1:
        raise AssertionError("staged and one-shot transcript derivation disagree")
    return _PublicCase(public_inputs, proof, transcript, tree0, tree1)


class IndependentSurfaceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()
        cls.inputs, cls.proof = _public_terms(cls.case)

    def test_source_has_only_standard_library_imports(self) -> None:
        source_path = PACKAGE_ROOT / "independent.py"
        source = source_path.read_text(encoding="utf-8")
        self.assertNotIn("friiormodel", source)
        imports = {
            node.names[0].name.split(".")[0]
            for node in ast.walk(ast.parse(source))
            if isinstance(node, ast.Import)
        }
        imports.update(
            node.module.split(".")[0]
            for node in ast.walk(ast.parse(source))
            if isinstance(node, ast.ImportFrom) and node.module is not None
        )
        self.assertEqual(imports, {"__future__", "hashlib", "hmac", "types", "typing"})

    def test_surface_accepts_only_raw_public_values_and_optional_limits(self) -> None:
        signature = inspect.signature(independent.verify_public_fri)
        self.assertEqual(
            tuple(signature.parameters), ("public_inputs", "proof", "limits")
        )
        self.assertEqual(
            signature.parameters["limits"].kind, inspect.Parameter.KEYWORD_ONLY
        )
        forbidden = (
            "expected_results",
            "private_generation",
            "native_trace",
            "semantic_checker_result",
            "producer_identity",
        )
        source = (PACKAGE_ROOT / "independent.py").read_text(encoding="utf-8")
        for name in forbidden:
            self.assertNotIn(name, source)

    def test_independent_canonical_framing_matches_the_public_terms(self) -> None:
        self.assertEqual(
            independent.canonical_term_bytes(self.inputs),
            encode_term(self.inputs),
        )
        self.assertEqual(
            independent.canonical_term_bytes(self.proof),
            encode_term(self.proof),
        )

    def test_split_semantic_terms_match_current_public_dependencies(self) -> None:
        self.assertEqual(
            independent._exact_algebra_profile(),
            EXACT_ALGEBRA_PROFILE.to_term(),
        )
        self.assertEqual(
            independent._exact_algebra_profile_id(),
            EXACT_ALGEBRA_PROFILE.identity.to_term(),
        )
        self.assertEqual(
            independent._exact_commitment_profile(),
            EXACT_COMMITMENT_PROFILE.to_term(),
        )
        self.assertEqual(
            independent._exact_commitment_profile_id(),
            EXACT_COMMITMENT_PROFILE.identity.to_term(),
        )
        self.assertEqual(
            independent._exact_grinding_profile(),
            EXACT_GRINDING_PROFILE.to_term(),
        )
        self.assertEqual(
            independent._exact_grinding_profile_id(),
            EXACT_GRINDING_PROFILE.identity.to_term(),
        )
        self.assertEqual(
            independent._exact_plan(),
            CANONICAL_CONSTRUCTION_PLAN.to_term(),
        )

    def test_non_json_and_extra_private_material_are_malformed(self) -> None:
        proof = deepcopy(self.proof)
        proof["private_generation"] = {"coefficients": [1, 2, 3]}
        result = independent.verify_public_fri(self.inputs, proof)
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-006")

        inputs = deepcopy(self.inputs)
        inputs["statement"] = b"not-json"
        result = independent.verify_public_fri(inputs, self.proof)
        self.assertEqual(result["outcome"], "Malformed")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-005")

    def test_profile_and_plan_variants_are_unsupported(self) -> None:
        profile_variant = deepcopy(self.inputs)
        profile_variant["profile"]["name"] = "different-profile"
        plan_variant = deepcopy(self.inputs)
        plan_variant["transcript_plan"]["query_count"] = 5
        for candidate, code in (
            (profile_variant, "FRI-IOR-INDEPENDENT-017"),
            (plan_variant, "FRI-IOR-INDEPENDENT-018"),
        ):
            with self.subTest(code=code):
                result = independent.verify_public_fri(candidate, self.proof)
                self.assertEqual(result["outcome"], "Unsupported")
                self.assertEqual(result["code"], code)

    def test_exact_semantic_terms_do_not_conflate_booleans_and_integers(
        self,
    ) -> None:
        profile_boolean = deepcopy(self.inputs)
        profile_boolean["profile"][
            "query_occurrences_preserve_order_and_multiplicity"
        ] = 1
        profile_version = deepcopy(self.inputs)
        profile_version["profile"]["semantic_law_ids"][0]["version"] = True
        extension_coefficient = deepcopy(self.inputs)
        extension_coefficient["profile"]["field"]["extension"]["polynomial"][1] = (
            False
        )
        plan_boolean = deepcopy(self.inputs)
        plan_boolean["transcript_plan"]["steps"][0]["feeds_transcript_state"] = 1
        opening_version = deepcopy(self.proof)
        opening_version["opening_table"][0]["opening"]["commitment_profile_id"][
            "version"
        ] = True

        cases = (
            (profile_boolean, self.proof, "FRI-IOR-INDEPENDENT-017"),
            (profile_version, self.proof, "FRI-IOR-INDEPENDENT-017"),
            (extension_coefficient, self.proof, "FRI-IOR-INDEPENDENT-017"),
            (plan_boolean, self.proof, "FRI-IOR-INDEPENDENT-018"),
            (self.inputs, opening_version, "FRI-IOR-INDEPENDENT-013"),
        )
        for inputs, proof, code in cases:
            with self.subTest(code=code):
                result = independent.verify_public_fri(inputs, proof)
                self.assertNotEqual(result["outcome"], "Affirmative")
                self.assertEqual(result["code"], code)

    def test_caps_and_openings_require_the_selected_commitment_identity(self) -> None:
        cap_variant = deepcopy(self.proof)
        cap_variant["cap0"]["commitment_profile_id"]["digest"] = "00" * 32
        opening_variant = deepcopy(self.proof)
        opening_variant["opening_table"][0]["opening"]["commitment_profile_id"][
            "digest"
        ] = "00" * 32
        for candidate, code in (
            (cap_variant, "FRI-IOR-INDEPENDENT-010"),
            (opening_variant, "FRI-IOR-INDEPENDENT-013"),
        ):
            with self.subTest(code=code):
                result = independent.verify_public_fri(self.inputs, candidate)
                self.assertEqual(result["outcome"], "Malformed")
                self.assertEqual(result["code"], code)


class IndependentPublicReplayTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()
        cls.inputs, cls.proof = _public_terms(cls.case)

    def test_primary_replay_matches_the_independent_known_answer(self) -> None:
        result = independent.verify_public_fri(self.inputs, self.proof)
        evidence = result["evidence"]
        self.assertEqual(evidence["beta0"], [69, 13])
        self.assertEqual(evidence["beta1"], [61, 26])
        self.assertEqual(evidence["ordered_initial_domain_indices"], [6, 14, 14, 4])
        self.assertEqual(self.proof["grinding_nonce"], 0)

    def test_primary_replay_accepts_exact_vector_and_narrow_claim(self) -> None:
        result = independent.verify_public_fri(self.inputs, self.proof)
        self.assertEqual(result["outcome"], "Affirmative")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-100")
        evidence = result["evidence"]
        self.assertEqual(evidence["beta0"], self.case.transcript.beta0.to_term())
        self.assertEqual(evidence["beta1"], self.case.transcript.beta1.to_term())
        self.assertEqual(
            evidence["ordered_initial_domain_indices"],
            [
                occurrence.initial_domain_index
                for occurrence in self.case.transcript.query_occurrences
            ],
        )
        self.assertEqual(evidence["random_draw_count"], 4)
        self.assertEqual(evidence["logical_layer_query_occurrences"], 8)
        self.assertEqual(
            evidence["unique_authenticated_openings"],
            len(self.case.proof.opening_table),
        )
        self.assertEqual(evidence["resource_usage"]["logical_query_occurrences"], 8)
        self.assertEqual(
            evidence["resource_usage"]["unique_openings"],
            len(self.case.proof.opening_table),
        )
        self.assertEqual(
            evidence["resource_usage"]["proof_bytes"], evidence["proof_bytes"]
        )
        self.assertFalse(evidence["establishes_outer_relation"])
        self.assertFalse(evidence["establishes_proximity_theorem"])
        self.assertFalse(evidence["establishes_checker_correspondence"])

    def test_ordered_draws_reuse_physical_rows_without_collapsing_occurrences(
        self,
    ) -> None:
        result = independent.verify_public_fri(self.inputs, self.proof)
        queries = result["evidence"]["ordered_initial_domain_indices"]
        logical_keys = [
            key for query in queries for key in ((0, query % 8), (1, query % 4))
        ]
        physical_keys = [
            (entry["layer"], entry["opening"]["pair_index"])
            for entry in self.proof["opening_table"]
        ]
        self.assertEqual(physical_keys, sorted(set(logical_keys)))
        self.assertLess(len(physical_keys), len(logical_keys))
        for ordinal, (query, selector) in enumerate(
            zip(queries, self.proof["occurrence_selectors"], strict=True)
        ):
            self.assertEqual(selector["ordinal"], ordinal)
            self.assertEqual(
                physical_keys[selector["layer0_opening_index"]], (0, query % 8)
            )
            self.assertEqual(
                physical_keys[selector["layer1_opening_index"]], (1, query % 4)
            )

    def test_nonce_is_rechecked_before_opening_coverage(self) -> None:
        proof = deepcopy(self.proof)
        proof["grinding_nonce"] = _first_failing_nonce(self.inputs, proof)
        proof["occurrence_selectors"] = []
        result = independent.verify_public_fri(self.inputs, proof)
        self.assertEqual(result["outcome"], "Refused")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-026")
        self.assertEqual(
            result["evidence"]["resource_usage"]["logical_query_occurrences"], 0
        )

    def test_statement_is_bound_before_every_derived_value(self) -> None:
        inputs = deepcopy(self.inputs)
        inputs["statement"]["initial_oracle_role"] = "mutated"
        result = independent.verify_public_fri(inputs, self.proof)
        self.assertNotEqual(result["outcome"], "Affirmative")
        self.assertIn(
            result["code"],
            {"FRI-IOR-INDEPENDENT-026", "FRI-IOR-INDEPENDENT-032"},
        )

    def test_opening_table_order_and_exact_coverage_are_checked(self) -> None:
        reordered = deepcopy(self.proof)
        reordered["opening_table"].reverse()
        missing = deepcopy(self.proof)
        missing["opening_table"].pop()
        for candidate, code in (
            (reordered, "FRI-IOR-INDEPENDENT-030"),
            (missing, "FRI-IOR-INDEPENDENT-032"),
        ):
            with self.subTest(code=code):
                result = independent.verify_public_fri(self.inputs, candidate)
                self.assertEqual(result["outcome"], "Refused")
                self.assertEqual(result["code"], code)

    def test_selector_count_bounds_and_mapping_are_checked(self) -> None:
        missing = deepcopy(self.proof)
        missing["occurrence_selectors"] = []
        outside = deepcopy(self.proof)
        outside["occurrence_selectors"][0]["layer0_opening_index"] = len(
            outside["opening_table"]
        )
        wrong = deepcopy(self.proof)
        current = wrong["occurrence_selectors"][0]["layer0_opening_index"]
        wrong["occurrence_selectors"][0]["layer0_opening_index"] = (current + 1) % len(
            wrong["opening_table"]
        )
        for candidate, code in (
            (missing, "FRI-IOR-INDEPENDENT-033"),
            (outside, "FRI-IOR-INDEPENDENT-034"),
            (wrong, "FRI-IOR-INDEPENDENT-035"),
        ):
            with self.subTest(code=code):
                result = independent.verify_public_fri(self.inputs, candidate)
                self.assertEqual(result["outcome"], "Refused")
                self.assertEqual(result["code"], code)

    def test_opening_authentication_rejects_a_salt_mutation(self) -> None:
        proof = deepcopy(self.proof)
        salt = proof["opening_table"][0]["opening"]["salt"]
        proof["opening_table"][0]["opening"]["salt"] = (
            "00" if salt[:2] != "00" else "01"
        ) + salt[2:]
        result = independent.verify_public_fri(self.inputs, proof)
        self.assertEqual(result["outcome"], "Refused")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-042")

    def test_authenticated_inconsistent_first_fold_is_rejected(self) -> None:
        case = _build_case(corrupt_first_fold=True)
        inputs, proof = _public_terms(case)
        result = independent.verify_public_fri(inputs, proof)
        self.assertEqual(result["outcome"], "Refused")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-050")

    def test_wrong_terminal_value_is_rejected_at_second_fold(self) -> None:
        case = _build_case(
            terminal_transform=lambda terminal: (
                terminal[0] + _fp2(1),
                terminal[1],
            )
        )
        inputs, proof = _public_terms(case)
        result = independent.verify_public_fri(inputs, proof)
        self.assertEqual(result["outcome"], "Refused")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-051")

    def test_late_terminal_degree_check_rejects_a_domain_alias(self) -> None:
        def add_vanishing(terminal):
            coefficient = _fp2(1)
            return (
                terminal[0] - coefficient,
                terminal[1],
                _fp2(0),
                _fp2(0),
                coefficient,
            )

        case = _build_case(terminal_transform=add_vanishing)
        inputs, proof = _public_terms(case)
        result = independent.verify_public_fri(inputs, proof)
        self.assertEqual(result["outcome"], "Refused")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-052")

    def test_coherent_alternate_public_commitments_can_accept(self) -> None:
        case = _build_case((4, 5, 7, 11, 13, 17, 19, 23))
        inputs, proof = _public_terms(case)
        result = independent.verify_public_fri(inputs, proof)
        self.assertEqual(result["outcome"], "Affirmative")
        self.assertFalse(result["evidence"]["establishes_outer_relation"])

    def test_query_resource_exhaustion_is_atomic(self) -> None:
        limits = DEFAULT_VALIDATION_LIMITS.to_term()
        limits["logical_query_occurrences"] = 7
        result = independent.verify_public_fri(self.inputs, self.proof, limits=limits)
        self.assertEqual(result["outcome"], "DeterministicLimitExceeded")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-090")
        usage = result["evidence"]["resource_usage"]
        self.assertEqual(usage["logical_query_occurrences"], 0)
        self.assertEqual(usage["unique_openings"], 0)
        self.assertEqual(usage["proof_bytes"], 0)

    def test_fp2_rejection_cap_uses_the_selected_sampler_limit(self) -> None:
        limits = dict(independent.DEFAULT_LIMITS)
        limits["sampler_attempts"] = 65
        counter = independent._Counter(independent._selected_limits(limits))

        def reject_through_the_old_boundary(
            _state, _namespace, _sampler, attempt, _counter
        ):
            return b"\xff" * 32 if attempt < 64 else b"\x00" * 32

        with patch.object(
            independent,
            "_squeeze",
            side_effect=reject_through_the_old_boundary,
        ) as squeeze:
            value, state = independent._sample_fp2(
                b"\x00" * 32,
                "test/fp2-rejection-cap/v1",
                counter,
            )

        self.assertEqual(value, (0, 0))
        self.assertEqual(state, b"\x00" * 32)
        self.assertEqual(squeeze.call_count, 65)
        self.assertEqual(counter.snapshot()["sampler_attempts"], 65)

    def test_malformed_hex_and_boolean_indices_fail_closed(self) -> None:
        bad_hex = deepcopy(self.proof)
        bad_hex["cap0"]["nodes"][0] = bad_hex["cap0"]["nodes"][0].upper()
        boolean_index = deepcopy(self.proof)
        boolean_index["opening_table"][0]["opening"]["pair_index"] = False
        for candidate in (bad_hex, boolean_index):
            with self.subTest(candidate=candidate is boolean_index):
                result = independent.verify_public_fri(self.inputs, candidate)
                self.assertEqual(result["outcome"], "Malformed")


if __name__ == "__main__":
    unittest.main()
