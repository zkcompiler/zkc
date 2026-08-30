"""Focused parity tests for the independent exact classical FRI replay."""

from __future__ import annotations

import ast
from copy import deepcopy
from dataclasses import replace
import inspect
from pathlib import Path
import sys
import unittest


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import classical_independent  # noqa: E402
from friiormodel.classical import (  # noqa: E402
    ClassicalCommittedProof,
    ClassicalLogicalOracle,
    ClassicalOccurrenceSelector,
    DEFAULT_CLASSICAL_LIMITS,
    GoldilocksElement,
    build_classical_commitment,
    build_honest_classical_case,
    derive_fiat_shamir_values,
    derive_layer_query_occurrences,
    encode_classical_proof,
    encode_classical_public_inputs,
    form_classical_public_inputs,
    verify_committed_fiat_shamir,
)


def _public_terms(case):
    return (
        deepcopy(case.fiat_shamir_run.public_inputs.to_term()),
        deepcopy(case.fiat_shamir_run.proof.to_term()),
    )


def _proof_for_trees(public_inputs, trees, terminal_scalar):
    roots = tuple(tree.root for tree in trees)
    values = derive_fiat_shamir_values(public_inputs, roots, terminal_scalar)
    occurrences = derive_layer_query_occurrences(values.query_indices)
    required_keys = tuple(
        sorted(
            {
                (occurrence.layer, occurrence.pair_index)
                for occurrence in occurrences
            }
        )
    )
    opening_table = tuple(
        trees[layer].open_pair(pair_index) for layer, pair_index in required_keys
    )
    table_index = {
        opening.key: index for index, opening in enumerate(opening_table)
    }
    selectors = tuple(
        ClassicalOccurrenceSelector(
            occurrence.ordinal,
            table_index[(occurrence.layer, occurrence.pair_index)],
        )
        for occurrence in occurrences
    )
    return ClassicalCommittedProof(
        roots=roots,
        terminal_scalar=terminal_scalar,
        opening_table=opening_table,
        occurrence_selectors=selectors,
    )


class ClassicalIndependentReplayTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = build_honest_classical_case()
        cls.public_inputs = cls.case.fiat_shamir_run.public_inputs
        cls.proof = cls.case.fiat_shamir_run.proof
        cls.inputs_term, cls.proof_term = _public_terms(cls.case)

    def assert_refusal_parity(self, public_inputs, proof) -> dict:
        producer = verify_committed_fiat_shamir(public_inputs, proof)
        independent = classical_independent.verify_public_classical_fri(
            deepcopy(public_inputs.to_term()),
            deepcopy(proof.to_term()),
        )
        self.assertEqual(producer.outcome.value, "Refused", producer.to_term())
        self.assertEqual(independent["outcome"], "Refused", independent)
        return independent

    def test_implementation_does_not_call_producer_operations(self) -> None:
        source_path = PACKAGE_ROOT / "classical_independent.py"
        tree = ast.parse(source_path.read_text(encoding="utf-8"))
        imported = {
            alias.name
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
            and node.module == "friiormodel.classical"
            for alias in node.names
        }
        allowed = {
            "DEFAULT_CLASSICAL_LIMITS",
            "DIGEST_BYTES",
            "DOMAIN_GENERATORS",
            "DOMAIN_ORDERS",
            "EXACT_CLASSICAL_COMMITTED_CORE",
            "EXACT_CLASSICAL_COMMITMENT_PROFILE",
            "EXACT_CLASSICAL_FRI_PROFILE",
            "FOLD_ROUNDS",
            "FS_FOLD_DOMAIN",
            "FS_FOLD_LABELS",
            "FS_PREFIX_SCHEMA",
            "FS_QUERY_DOMAIN",
            "FS_QUERY_LABELS",
            "GOLDILOCKS_MODULUS",
            "LAYER_QUERY_OCCURRENCES",
            "LEAF_HASH_DOMAIN",
            "MAX_FS_SAMPLER_ATTEMPTS",
            "NODE_HASH_DOMAIN",
            "PUBLIC_INPUT_SCHEMA",
            "PUBLIC_PROOF_SCHEMA",
            "QUERY_REPETITIONS",
            "SALT_BYTES",
        }
        self.assertEqual(imported, allowed)
        forbidden_calls = {
            "binary_fold",
            "build_classical_commitment",
            "build_honest_classical_case",
            "classical_fiat_shamir_prefix_term",
            "derive_fiat_shamir_values",
            "derive_layer_query_occurrences",
            "verify_committed_fiat_shamir",
            "verify_committed_fresh",
            "verify_committed_run",
        }
        called_names = {
            node.func.id
            for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        }
        self.assertTrue(forbidden_calls.isdisjoint(called_names))

    def test_surface_is_only_two_public_terms_and_optional_limits(self) -> None:
        signature = inspect.signature(
            classical_independent.verify_public_classical_fri
        )
        self.assertEqual(
            tuple(signature.parameters), ("public_inputs", "proof", "limits")
        )
        self.assertEqual(
            signature.parameters["limits"].kind,
            inspect.Parameter.KEYWORD_ONLY,
        )

    def test_canonical_bytes_and_honest_replay_match(self) -> None:
        self.assertEqual(
            classical_independent.canonical_term_bytes(self.inputs_term),
            encode_classical_public_inputs(self.public_inputs),
        )
        self.assertEqual(
            classical_independent.canonical_term_bytes(self.proof_term),
            encode_classical_proof(self.proof),
        )
        producer = verify_committed_fiat_shamir(self.public_inputs, self.proof)
        independent = classical_independent.verify_public_classical_fri(
            self.inputs_term,
            self.proof_term,
        )
        self.assertEqual(producer.outcome.value, "Affirmative")
        self.assertEqual(independent["outcome"], "Affirmative", independent)
        self.assertEqual(
            independent["evidence"]["fold_challenges"],
            [challenge.value for challenge in self.case.fiat_shamir_run.fold_challenges],
        )
        self.assertEqual(
            independent["evidence"]["ordered_initial_domain_indices"],
            list(self.case.fiat_shamir_run.query_indices),
        )
        self.assertEqual(
            independent["evidence"]["resource_usage"],
            producer.evidence["resources"],
        )
        self.assertEqual(independent["evidence"]["fold_checks"], 12)
        self.assertEqual(
            independent["evidence"]["authenticated_oracle_value_occurrences"],
            24,
        )

    def test_statement_and_context_each_influence_the_transcript(self) -> None:
        original_values = derive_fiat_shamir_values(
            self.public_inputs,
            self.proof.roots,
            self.proof.terminal_scalar,
        )
        variants = (
            form_classical_public_inputs(
                {"claim": "different-public-statement", "public_instance": 7},
                {"application": "zkc-exact-classical-fri-control", "version": 1},
            ),
            form_classical_public_inputs(
                {"claim": "degree-below-eight-on-goldilocks-l0", "public_instance": 7},
                {"application": "different-public-context", "version": 1},
            ),
        )
        for variant in variants:
            with self.subTest(field=variant.to_term()):
                changed = derive_fiat_shamir_values(
                    variant,
                    self.proof.roots,
                    self.proof.terminal_scalar,
                )
                self.assertNotEqual(changed, original_values)
                self.assert_refusal_parity(variant, self.proof)

    def test_selector_mutation_is_rejected_by_both_lanes(self) -> None:
        selectors = list(self.proof.occurrence_selectors)
        selectors[0] = replace(
            selectors[0],
            opening_index=(selectors[0].opening_index + 1)
            % len(self.proof.opening_table),
        )
        mutated = replace(self.proof, occurrence_selectors=tuple(selectors))
        independent = self.assert_refusal_parity(self.public_inputs, mutated)
        self.assertEqual(independent["code"], "FRI-IOR-CLASSICAL-INDEPENDENT-033")

    def test_authentication_mutation_is_rejected_by_both_lanes(self) -> None:
        openings = list(self.proof.opening_table)
        salt = bytearray(openings[0].salt)
        salt[0] ^= 1
        openings[0] = replace(openings[0], salt=bytes(salt))
        mutated = replace(self.proof, opening_table=tuple(openings))
        independent = self.assert_refusal_parity(self.public_inputs, mutated)
        self.assertEqual(independent["code"], "FRI-IOR-CLASSICAL-INDEPENDENT-041")

    def test_authenticated_middle_fold_mutation_is_rejected(self) -> None:
        trees = [
            build_classical_commitment(oracle, self.case.owner_salts[layer])
            for layer, oracle in enumerate(self.case.native_trace.oracles)
        ]
        middle_target_oracle = self.case.native_trace.oracles[2]
        shifted_values = tuple(
            value + GoldilocksElement(1) for value in middle_target_oracle.values
        )
        shifted_oracle = ClassicalLogicalOracle(
            layer=middle_target_oracle.layer,
            domain=middle_target_oracle.domain,
            origin=middle_target_oracle.origin,
            values=shifted_values,
        )
        trees[2] = build_classical_commitment(
            shifted_oracle,
            self.case.owner_salts[2],
        )
        mutated = _proof_for_trees(
            self.public_inputs,
            tuple(trees),
            self.proof.terminal_scalar,
        )
        independent = self.assert_refusal_parity(self.public_inputs, mutated)
        self.assertEqual(independent["code"], "FRI-IOR-CLASSICAL-INDEPENDENT-052")

    def test_authenticated_final_scalar_mutation_is_rejected(self) -> None:
        trees = tuple(
            build_classical_commitment(oracle, self.case.owner_salts[layer])
            for layer, oracle in enumerate(self.case.native_trace.oracles)
        )
        terminal = GoldilocksElement.reduce(self.proof.terminal_scalar.value + 1)
        mutated = _proof_for_trees(self.public_inputs, trees, terminal)
        independent = self.assert_refusal_parity(self.public_inputs, mutated)
        self.assertEqual(independent["code"], "FRI-IOR-CLASSICAL-INDEPENDENT-053")

    def test_resource_exhaustion_matches_the_producer_classification(self) -> None:
        producer_limits = replace(DEFAULT_CLASSICAL_LIMITS, field_operations=95)
        producer = verify_committed_fiat_shamir(
            self.public_inputs,
            self.proof,
            producer_limits,
        )
        independent_limits = dict(classical_independent.DEFAULT_LIMITS)
        independent_limits["field_operations"] = 95
        independent = classical_independent.verify_public_classical_fri(
            self.inputs_term,
            self.proof_term,
            limits=independent_limits,
        )
        self.assertEqual(producer.outcome.value, "DeterministicLimitExceeded")
        self.assertEqual(independent["outcome"], "DeterministicLimitExceeded")
        self.assertEqual(
            independent["code"], "FRI-IOR-CLASSICAL-INDEPENDENT-090"
        )


if __name__ == "__main__":
    unittest.main()
