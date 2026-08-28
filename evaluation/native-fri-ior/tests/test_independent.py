"""Tests for the separately coded public replay verifier."""

from __future__ import annotations

import ast
from copy import deepcopy
import inspect
import json
from pathlib import Path
import sys
import unittest


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))
sys.path.insert(0, str(PACKAGE_ROOT / "tests"))

import independent  # noqa: E402
from friiormodel.profile import DEFAULT_VALIDATION_LIMITS  # noqa: E402
from friiormodel.terms import encode_term  # noqa: E402
from test_public_verification import (  # noqa: E402
    _build_case,
    _fp2,
)


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


class IndependentPublicReplayTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = _build_case()
        cls.inputs, cls.proof = _public_terms(cls.case)

    def test_primary_replay_accepts_exact_vector_and_narrow_claim(self) -> None:
        result = independent.verify_public_fri(self.inputs, self.proof)
        self.assertEqual(result["outcome"], "Affirmative")
        self.assertEqual(result["code"], "FRI-IOR-INDEPENDENT-100")
        evidence = result["evidence"]
        self.assertEqual(evidence["beta0"], [10, 34])
        self.assertEqual(evidence["beta1"], [23, 31])
        self.assertEqual(evidence["ordered_initial_domain_indices"], [6, 6, 1, 9])
        self.assertEqual(evidence["random_draw_count"], 4)
        self.assertEqual(evidence["logical_layer_query_occurrences"], 8)
        self.assertEqual(evidence["unique_authenticated_openings"], 4)
        self.assertEqual(evidence["resource_usage"]["logical_query_occurrences"], 8)
        self.assertEqual(evidence["resource_usage"]["unique_openings"], 4)
        self.assertEqual(
            evidence["resource_usage"]["proof_bytes"], evidence["proof_bytes"]
        )
        self.assertFalse(evidence["establishes_outer_relation"])
        self.assertFalse(evidence["establishes_proximity_theorem"])
        self.assertFalse(evidence["establishes_checker_correspondence"])

    def test_duplicate_and_opposite_draws_reuse_physical_rows_without_collapsing_occurrences(
        self,
    ) -> None:
        result = independent.verify_public_fri(self.inputs, self.proof)
        queries = result["evidence"]["ordered_initial_domain_indices"]
        self.assertEqual(queries[0], queries[1])
        self.assertEqual((queries[2] + 8) % 16, queries[3])
        self.assertEqual(len(self.proof["opening_table"]), 4)
        self.assertEqual(
            self.proof["occurrence_selectors"][0]["layer0_opening_index"],
            self.proof["occurrence_selectors"][1]["layer0_opening_index"],
        )
        self.assertEqual(
            self.proof["occurrence_selectors"][2]["layer1_opening_index"],
            self.proof["occurrence_selectors"][3]["layer1_opening_index"],
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
        wrong["occurrence_selectors"][0]["layer0_opening_index"] = 0
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
        case = _build_case(expected_beta1=(17, 10), corrupt_first_fold_index=0)
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
        case = _build_case(
            (4, 5, 7, 11, 13, 17, 19, 23),
            expected_beta0=(31, 75),
            expected_beta1=(7, 75),
        )
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
