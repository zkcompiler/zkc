"""Focused executable checks for the exact classical FRI control."""

from __future__ import annotations

from dataclasses import fields, replace
import inspect
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.classical import (  # noqa: E402
    CLASSICAL_DOMAINS,
    DEFAULT_CLASSICAL_LIMITS,
    DEGREE_BOUNDS,
    DOMAIN_GENERATORS,
    DOMAIN_ORDERS,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_NATIVE_CORE,
    EXACT_COMMITTED_SCHEDULE,
    EXACT_NATIVE_SCHEDULE,
    FIAT_SHAMIR_INTERPRETATION,
    FOLD_ROUNDS,
    FRESH_INTERPRETATION,
    GOLDILOCKS_MODULUS,
    LAYER_QUERY_OCCURRENCES,
    QUERY_REPETITIONS,
    ClassicalCommittedProof,
    ClassicalCommittedRun,
    ClassicalMerkleRoot,
    ClassicalPublicEnvironment,
    GoldilocksElement,
    build_honest_classical_case,
    derive_fiat_shamir_values,
    derive_honest_native_trace,
    encode_classical_proof,
    form_classical_public_environment,
    form_classical_public_inputs,
    verify_committed_fiat_shamir,
    verify_committed_fresh,
    verify_committed_run,
    verify_native_trace,
)
from friiormodel.terms import ModelFailure, OutcomeClass, semantic_id  # noqa: E402


def _increment(value: GoldilocksElement) -> GoldilocksElement:
    return GoldilocksElement.reduce(value.value + 1)


def _assert_json_safe(test: unittest.TestCase, value: object) -> None:
    if value is None or type(value) in (bool, int, str):
        return
    if type(value) is list:
        for item in value:
            _assert_json_safe(test, item)
        return
    if type(value) is dict:
        test.assertTrue(all(type(key) is str for key in value))
        for item in value.values():
            _assert_json_safe(test, item)
        return
    test.fail(f"non-JSON public term member: {type(value)!r}")


class ExactClassicalProfileTest(unittest.TestCase):
    def test_profile_is_the_goldilocks_three_fold_scalar_terminal_control(self) -> None:
        self.assertEqual(GOLDILOCKS_MODULUS, (1 << 64) - (1 << 32) + 1)
        self.assertEqual(DOMAIN_ORDERS, (64, 32, 16, 8))
        self.assertEqual(
            DOMAIN_GENERATORS,
            (512, 262144, 68719476736, 1099511627520),
        )
        self.assertEqual(DEGREE_BOUNDS, (8, 4, 2, 1))
        self.assertEqual(FOLD_ROUNDS, 3)
        self.assertEqual(QUERY_REPETITIONS, 4)
        self.assertEqual(LAYER_QUERY_OCCURRENCES, 12)
        self.assertEqual(EXACT_CLASSICAL_FRI_PROFILE.domains, CLASSICAL_DOMAINS)
        for domain in CLASSICAL_DOMAINS:
            self.assertEqual(domain.generator**domain.order, GoldilocksElement(1))
            self.assertNotEqual(
                domain.generator ** (domain.order // 2),
                GoldilocksElement(1),
            )

    def test_native_and_committed_cores_have_distinct_exact_schedules(self) -> None:
        self.assertNotEqual(
            EXACT_CLASSICAL_NATIVE_CORE.identity,
            EXACT_CLASSICAL_COMMITTED_CORE.identity,
        )
        self.assertEqual(EXACT_CLASSICAL_NATIVE_CORE.schedule, EXACT_NATIVE_SCHEDULE)
        self.assertEqual(
            EXACT_CLASSICAL_COMMITTED_CORE.schedule,
            EXACT_COMMITTED_SCHEDULE,
        )
        self.assertEqual(
            EXACT_CLASSICAL_COMMITTED_CORE.source_core_id,
            EXACT_CLASSICAL_NATIVE_CORE.identity,
        )
        for core in (EXACT_CLASSICAL_NATIVE_CORE, EXACT_CLASSICAL_COMMITTED_CORE):
            coordinates = core.to_term()["public_environment_coordinates"]
            self.assertEqual(
                tuple(item["semantic_purpose"] for item in coordinates),
                ("Statement", "ApplicationContext"),
            )


class ExactNativeExecutionTest(unittest.TestCase):
    def test_honest_native_trace_accepts_all_twelve_occurrences(self) -> None:
        trace = derive_honest_native_trace()
        result = verify_native_trace(trace)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-NATIVE-100")
        self.assertEqual(len(trace.oracles), 3)
        self.assertEqual(
            tuple(oracle.name for oracle in trace.oracles), ("G0", "G1", "G2")
        )
        self.assertEqual(len(trace.query_occurrences), 12)
        self.assertEqual(
            result.evidence["oracle_value_occurrences"],
            24,
        )
        self.assertEqual(
            result.evidence["public_environment_id"],
            trace.public_environment.identity,
        )
        self.assertEqual(
            result.evidence["statement_coordinate_id"],
            trace.public_environment.statement_coordinate_id,
        )
        self.assertEqual(
            result.evidence["application_context_coordinate_id"],
            trace.public_environment.application_context_coordinate_id,
        )

    def test_native_public_environment_is_formed_and_profile_checked(self) -> None:
        trace = derive_honest_native_trace()
        with self.assertRaises(ModelFailure) as caught:
            replace(trace, public_environment=b"not-a-public-environment")
        self.assertEqual(caught.exception.code, "FRI-IOR-CLASSICAL-FORMATION-008")

        other_profile = semantic_id(
            "classical-fri-profile",
            "classical-fri.profile.v1",
            {"name": "substituted-profile"},
        )
        changed_environment = replace(
            trace.public_environment,
            profile_id=other_profile,
        )
        result = verify_native_trace(
            replace(trace, public_environment=changed_environment)
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-NATIVE-009")

    def test_public_environment_has_two_distinct_typed_coordinates(self) -> None:
        environment = form_classical_public_environment(
            {"claim": "coordinate-test"},
            {"application": "coordinate-test"},
        )
        self.assertIsInstance(environment, ClassicalPublicEnvironment)
        self.assertNotEqual(
            environment.statement_coordinate_id,
            environment.application_context_coordinate_id,
        )
        self.assertEqual(
            tuple(
                item["semantic_purpose"]
                for item in environment.to_term()["coordinates"]
            ),
            ("Statement", "ApplicationContext"),
        )

    def test_repeated_query_is_not_collapsed_as_a_logical_occurrence(self) -> None:
        trace = derive_honest_native_trace()
        self.assertEqual(trace.query_indices, (5, 17, 17, 42))
        second = trace.query_occurrences[3:6]
        third = trace.query_occurrences[6:9]
        self.assertEqual(
            tuple(item.sampled_index for item in second),
            tuple(item.sampled_index for item in third),
        )
        self.assertNotEqual(
            tuple(item.ordinal for item in second),
            tuple(item.ordinal for item in third),
        )
        self.assertNotEqual(
            tuple(item.identity for item in second),
            tuple(item.identity for item in third),
        )

    def test_non_scalar_terminal_is_malformed_at_formation(self) -> None:
        trace = derive_honest_native_trace()
        with self.assertRaises(ModelFailure) as caught:
            replace(trace, terminal_scalar=(trace.terminal_scalar,))
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-CLASSICAL-FORMATION-004")

    def test_wrong_scalar_reaches_and_fails_the_third_fold(self) -> None:
        honest = derive_honest_native_trace()
        trace = derive_honest_native_trace(
            terminal_scalar_override=_increment(honest.terminal_scalar)
        )
        result = verify_native_trace(trace)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "classical-fri:fold-2")
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-NATIVE-022")


class ExactCommittedExecutionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.case = build_honest_classical_case()

    def test_deterministic_vector_and_both_interpretations_accept(self) -> None:
        case = self.case
        self.assertEqual(
            tuple(value.value for value in case.fresh_run.fold_challenges),
            (18302912802533455500, 10089388910461611512, 10652350149053350211),
        )
        self.assertEqual(case.fresh_run.query_indices, (49, 9, 4, 24))
        self.assertEqual(
            case.fresh_run.proof.terminal_scalar.value, 7961261751171662295
        )
        self.assertEqual(
            tuple(root.digest.hex() for root in case.fresh_run.proof.roots),
            (
                "75ffbae2cb65813aefe8e8a32cc637c7f4990c6d4351cc6300c123061e7b74db",
                "e2c41895d03cac10794d271eb294221d0da4c6b2a9b9a3a402a314fa074faae4",
                "e6b9d22b66f00c808038efd4295448992a5d0df8135a48190bb7172efeb4e294",
            ),
        )
        fresh = verify_committed_run(case.fresh_run)
        fiat_shamir = verify_committed_run(case.fiat_shamir_run)
        self.assertIs(fresh.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIs(fiat_shamir.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(case.fresh_run.proof, case.fiat_shamir_run.proof)
        self.assertEqual(
            case.fresh_run.committed_core_id,
            case.fiat_shamir_run.committed_core_id,
        )
        self.assertNotEqual(
            case.fresh_run.protocol_id, case.fiat_shamir_run.protocol_id
        )
        self.assertEqual(case.fresh_run.interpretation, FRESH_INTERPRETATION)
        self.assertEqual(
            case.fiat_shamir_run.interpretation,
            FIAT_SHAMIR_INTERPRETATION,
        )
        self.assertEqual(
            case.native_trace.public_environment,
            case.fresh_run.public_environment,
        )
        self.assertEqual(
            case.native_trace.public_environment,
            case.fiat_shamir_run.public_environment,
        )
        self.assertEqual(
            fresh.evidence["public_environment_id"],
            case.native_trace.public_environment.identity,
        )

    def test_case_refuses_native_and_fresh_environment_mismatch(self) -> None:
        changed_native = derive_honest_native_trace(
            statement={"claim": "different-native-statement"}
        )
        with self.assertRaises(ModelFailure) as caught:
            replace(self.case, native_trace=changed_native)
        self.assertEqual(caught.exception.code, "FRI-IOR-CLASSICAL-CASE-005")

    def test_fs_derivation_matches_the_committed_run(self) -> None:
        run = self.case.fiat_shamir_run
        values = derive_fiat_shamir_values(
            run.public_inputs,
            run.proof.roots,
            run.proof.terminal_scalar,
        )
        self.assertEqual(values.fold_challenges, run.fold_challenges)
        self.assertEqual(values.query_indices, run.query_indices)
        self.assertIs(
            verify_committed_fiat_shamir(run.public_inputs, run.proof).outcome,
            OutcomeClass.AFFIRMATIVE,
        )
        self.assertIs(
            verify_committed_fresh(
                run.public_inputs,
                run.proof,
                run.fold_challenges,
                run.query_indices,
            ).outcome,
            OutcomeClass.AFFIRMATIVE,
        )

    def test_public_terms_are_json_safe_and_have_no_full_private_tables(self) -> None:
        public_inputs_term = self.case.fresh_run.public_inputs.to_term()
        proof_term = self.case.fresh_run.proof.to_term()
        _assert_json_safe(self, public_inputs_term)
        _assert_json_safe(self, proof_term)
        self.assertNotIn("oracles", proof_term)
        self.assertNotIn("oracle_values", proof_term)
        self.assertNotIn("owner_salts", proof_term)
        self.assertTrue(
            all(
                character in "0123456789abcdef"
                for character in public_inputs_term["statement"]
            )
        )
        self.assertLess(len(encode_classical_proof(self.case.fresh_run.proof)), 1 << 15)
        proof_fields = {item.name for item in fields(ClassicalCommittedProof)}
        self.assertEqual(
            proof_fields,
            {
                "roots",
                "terminal_scalar",
                "opening_table",
                "occurrence_selectors",
                "committed_core_id",
                "schema",
            },
        )
        run_fields = {item.name for item in fields(ClassicalCommittedRun)}
        self.assertNotIn("oracles", run_fields)
        self.assertNotIn("salts", run_fields)
        self.assertEqual(
            tuple(inspect.signature(verify_committed_run).parameters),
            ("run", "limits"),
        )

    def test_statement_mutation_is_rejected_by_strong_fs_first(self) -> None:
        run = self.case.fiat_shamir_run
        changed_inputs = form_classical_public_inputs(
            {"claim": "different-public-statement"},
            {"application": "same-context"},
        )
        changed_run = replace(run, public_inputs=changed_inputs)
        result = verify_committed_run(changed_run)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "classical-fri:fiat-shamir-interpretation")
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-FS-013")

    def test_wrong_root_is_rejected_at_authentication_in_fresh_mode(self) -> None:
        run = self.case.fresh_run
        root = run.proof.roots[0]
        changed_digest = bytes((root.digest[0] ^ 1,)) + root.digest[1:]
        changed_root = replace(root, digest=changed_digest)
        changed_proof = replace(
            run.proof,
            roots=(changed_root,) + run.proof.roots[1:],
        )
        result = verify_committed_run(replace(run, proof=changed_proof))
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "classical-fri:opening-authentication")
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-COMMITMENT-020")

    def test_wrong_opening_is_rejected_before_any_fold(self) -> None:
        run = self.case.fresh_run
        opening = run.proof.opening_table[0]
        changed_opening = replace(opening, positive=_increment(opening.positive))
        changed_proof = replace(
            run.proof,
            opening_table=(changed_opening,) + run.proof.opening_table[1:],
        )
        result = verify_committed_run(replace(run, proof=changed_proof))
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "classical-fri:opening-authentication")
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-COMMITMENT-020")

    def test_wrong_selector_is_rejected_at_selector_coverage(self) -> None:
        run = self.case.fresh_run
        first = run.proof.occurrence_selectors[0]
        changed = replace(
            first,
            opening_index=(first.opening_index + 1) % len(run.proof.opening_table),
        )
        changed_proof = replace(
            run.proof,
            occurrence_selectors=(changed,) + run.proof.occurrence_selectors[1:],
        )
        result = verify_committed_run(replace(run, proof=changed_proof))
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "classical-fri:occurrence-selectors")
        self.assertEqual(result.code, "FRI-IOR-CLASSICAL-COMMITTED-010")

    def test_coherent_wrong_scalar_reaches_the_third_fold_in_both_modes(self) -> None:
        wrong = _increment(self.case.native_trace.terminal_scalar)
        case = build_honest_classical_case(terminal_scalar_override=wrong)
        for run in (case.fresh_run, case.fiat_shamir_run):
            with self.subTest(interpretation=run.interpretation):
                result = verify_committed_run(run)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.boundary, "classical-fri:fold-2")
                self.assertEqual(result.code, "FRI-IOR-CLASSICAL-COMMITTED-023")

    def test_non_scalar_public_terminal_is_malformed_at_formation(self) -> None:
        proof = self.case.fresh_run.proof
        with self.assertRaises(ModelFailure) as caught:
            replace(proof, terminal_scalar=(proof.terminal_scalar,))
        self.assertIs(caught.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(caught.exception.code, "FRI-IOR-CLASSICAL-PROOF-003")

    def test_proof_byte_limit_is_a_typed_deterministic_failure(self) -> None:
        run = self.case.fresh_run
        exact_bytes = len(encode_classical_proof(run.proof))
        limits = replace(DEFAULT_CLASSICAL_LIMITS, proof_bytes=exact_bytes - 1)
        result = verify_committed_run(run, limits)
        self.assertIs(result.outcome, OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED)
        self.assertEqual(result.boundary, "resources:accounting")
        self.assertEqual(result.code, "FRI-IOR-RESOURCE-008")

    def test_root_statement_and_terminal_mutations_rotate_public_identity(self) -> None:
        run = self.case.fresh_run
        changed_inputs = form_classical_public_inputs(
            {"claim": "rotated"},
            {"application": "zkc-exact-classical-fri-control", "version": 1},
        )
        self.assertNotEqual(changed_inputs.identity, run.public_inputs.identity)
        root = run.proof.roots[0]
        changed_root = ClassicalMerkleRoot(
            root.layer,
            bytes((root.digest[0] ^ 1,)) + root.digest[1:],
        )
        changed_proof = replace(
            run.proof,
            roots=(changed_root,) + run.proof.roots[1:],
        )
        self.assertNotEqual(changed_proof.identity, run.proof.identity)
        scalar_proof = replace(
            run.proof,
            terminal_scalar=_increment(run.proof.terminal_scalar),
        )
        self.assertNotEqual(scalar_proof.identity, run.proof.identity)


if __name__ == "__main__":
    unittest.main()
