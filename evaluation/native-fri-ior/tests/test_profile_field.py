"""Tests for the exact profile, field, domain chain, and binary fold."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.field import (  # noqa: E402
    BINARY_FOLD_FIELD_OPERATIONS,
    Fp,
    Fp2,
    binary_fold,
    canonical_polynomial,
    evaluate_polynomial,
    polynomial_degree,
)
from friiormodel.profile import (  # noqa: E402
    D0,
    D1,
    D2,
    EXACT_PROFILE,
    EvaluationDomain,
    admit_exact_profile,
)
from friiormodel.terms import (  # noqa: E402
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    SEMANTIC_REGIME_ID,
    SemanticId,
    check_semantic_id,
    semantic_id,
)


def _extension(real: int, imag: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imag))


class FieldTest(unittest.TestCase):
    def test_base_field_uses_canonical_representatives(self) -> None:
        self.assertEqual(Fp.reduce(194), Fp(0))
        self.assertEqual(Fp(96) + Fp(2), Fp(1))
        self.assertEqual(Fp(2) - Fp(3), Fp(96))
        self.assertEqual(Fp(12) * Fp(89), Fp.reduce(12 * 89))
        self.assertEqual(Fp(7) / Fp(5) * Fp(5), Fp(7))

    def test_noncanonical_base_field_input_is_malformed(self) -> None:
        for value in (-1, 97, True, "3"):
            with self.subTest(value=value), self.assertRaises(ModelFailure) as raised:
                Fp(value)  # type: ignore[arg-type]
            self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
            self.assertEqual(raised.exception.code, "FRI-IOR-FIELD-001")

    def test_zero_inverse_is_a_refusal_not_malformed_input(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            Fp(0).inverse()
        self.assertIs(raised.exception.outcome, OutcomeClass.REFUSED)
        self.assertEqual(raised.exception.code, "FRI-IOR-FIELD-005")

    def test_base_and_extension_codecs_are_exact(self) -> None:
        base = Fp(96)
        extension = _extension(17, 91)
        self.assertEqual(Fp.from_bytes(base.to_bytes()), base)
        self.assertEqual(Fp2.from_bytes(extension.to_bytes()), extension)
        with self.assertRaises(ModelFailure) as raised:
            Fp.from_bytes(b"\x00\x01")
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-FIELD-003")

    def test_extension_polynomial_is_irreducible_and_u_squared_is_five(self) -> None:
        u = _extension(0, 1)
        self.assertEqual(u * u, _extension(5))
        self.assertEqual(Fp(5) ** 48, Fp(96))

    def test_extension_inverse_round_trips_every_nonzero_element(self) -> None:
        samples = (_extension(1), _extension(0, 1), _extension(19, 27), _extension(96, 4))
        for value in samples:
            with self.subTest(value=value):
                self.assertEqual(value * value.inverse(), Fp2.one())


class ProfileTest(unittest.TestCase):
    def test_primitive_generator_has_order_ninety_six(self) -> None:
        generator = Fp(5)
        self.assertEqual(generator**96, Fp(1))
        self.assertNotEqual(generator**48, Fp(1))
        self.assertNotEqual(generator**32, Fp(1))

    def test_domain_chain_has_exact_generators_and_orders(self) -> None:
        self.assertEqual(
            tuple((domain.generator.value, domain.order) for domain in EXACT_PROFILE.domains),
            ((8, 16), (64, 8), (22, 4)),
        )
        self.assertEqual(D0.generator * D0.generator, D1.generator)
        self.assertEqual(D1.generator * D1.generator, D2.generator)

    def test_domain_points_are_distinct_and_antipodal_in_declared_order(self) -> None:
        for domain in EXACT_PROFILE.domains:
            points = domain.points()
            self.assertEqual(len(set(points)), domain.order)
            for first, second in domain.antipodal_index_pairs():
                self.assertEqual(points[second], -points[first])

    def test_exact_profile_admits_and_has_stable_identity(self) -> None:
        result = admit_exact_profile(EXACT_PROFILE)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-PROFILE-100")
        self.assertEqual(result.subject, EXACT_PROFILE.identity)
        self.assertEqual(EXACT_PROFILE.identity, EXACT_PROFILE.identity)

    def test_well_formed_alternate_profile_is_unsupported(self) -> None:
        alternate = replace(EXACT_PROFILE, name="another-finite-profile")
        result = admit_exact_profile(alternate)
        self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(result.code, "FRI-IOR-PROFILE-018")

    def test_request_limits_do_not_enter_profile_identity(self) -> None:
        profile_term = EXACT_PROFILE.to_term()
        profile_identity = EXACT_PROFILE.identity
        small_request = ResourceCounter(ResourceLimits(8, 1, 64, 0))
        larger_request = ResourceCounter(ResourceLimits(80, 10, 640, 6))

        self.assertNotEqual(small_request.limits, larger_request.limits)
        self.assertNotIn("resources", profile_term)
        self.assertEqual(EXACT_PROFILE.to_term(), profile_term)
        self.assertEqual(EXACT_PROFILE.identity, profile_identity)

    def test_non_profile_input_is_malformed_at_admission(self) -> None:
        result = admit_exact_profile({"name": EXACT_PROFILE.name})
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-PROFILE-017")

    def test_invalid_domain_order_is_malformed(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            EvaluationDomain("bad", Fp(8), 12)
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-PROFILE-003")

    def test_ordinary_hash_charge_does_not_count_a_merkle_node(self) -> None:
        counter = ResourceCounter(ResourceLimits(0, 1, 32, 0))
        counter.consume_hash(32)
        self.assertEqual(counter.hash_calls, 1)
        self.assertEqual(counter.hash_bytes, 32)
        self.assertEqual(counter.merkle_nodes, 0)


class SemanticIdentityTest(unittest.TestCase):
    def test_operational_outcome_partition_is_exact(self) -> None:
        self.assertEqual(
            tuple(outcome.value for outcome in OutcomeClass),
            (
                "Affirmative",
                "Unsupported",
                "MissingDependency",
                "KindMismatch",
                "Malformed",
                "Refused",
                "DeterministicLimitExceeded",
                "CheckerFailure",
            ),
        )

    def test_profile_identity_carries_kind_domain_regime_and_digest(self) -> None:
        identity = EXACT_PROFILE.identity
        self.assertIsInstance(identity, SemanticId)
        self.assertEqual(identity.subject_kind, "fri-ior-profile")
        self.assertEqual(identity.domain, "fri-ior.profile.v1")
        self.assertEqual(identity.semantic_regime, SEMANTIC_REGIME_ID)
        self.assertEqual(len(identity.digest), 32)
        self.assertEqual(identity.to_term()["digest"], identity.digest.hex())
        self.assertEqual(str(identity), identity.to_text())
        self.assertIn(identity.digest.hex(), identity.to_text())

    def test_subject_kind_is_part_of_the_hashed_preimage(self) -> None:
        alternate_kind = semantic_id(
            "other-profile-kind",
            EXACT_PROFILE.identity.domain,
            EXACT_PROFILE.to_term(),
        )
        self.assertNotEqual(alternate_kind.digest, EXACT_PROFILE.identity.digest)

    def test_wrong_formed_kind_is_a_kind_mismatch(self) -> None:
        wrong_kind = replace(EXACT_PROFILE.identity, subject_kind="merkle-cap")
        result = check_semantic_id(
            wrong_kind,
            expected_subject_kind="fri-ior-profile",
            expected_domain="fri-ior.profile.v1",
        )
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(result.code, "FRI-IOR-IDENTITY-009")

    def test_wrong_formed_domain_is_a_kind_mismatch(self) -> None:
        wrong_domain = replace(
            EXACT_PROFILE.identity,
            domain="fri-ior.other-profile.v1",
        )
        result = check_semantic_id(
            wrong_domain,
            expected_subject_kind="fri-ior-profile",
            expected_domain="fri-ior.profile.v1",
        )
        self.assertIs(result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(result.code, "FRI-IOR-IDENTITY-010")

    def test_wrong_formed_regime_is_unsupported(self) -> None:
        wrong_regime = replace(
            EXACT_PROFILE.identity,
            semantic_regime="other.closed-finite-term.v1",
        )
        result = check_semantic_id(
            wrong_regime,
            expected_subject_kind="fri-ior-profile",
            expected_domain="fri-ior.profile.v1",
        )
        self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(result.code, "FRI-IOR-IDENTITY-008")

    def test_unformed_identity_is_malformed(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            SemanticId(
                subject_kind="FriIorProfile",
                domain="fri-ior.profile.v1",
                semantic_regime=SEMANTIC_REGIME_ID,
                digest=b"\x00" * 32,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-IDENTITY-001")

        result = check_semantic_id(
            "sha256:naked-digest",
            expected_subject_kind="fri-ior-profile",
            expected_domain="fri-ior.profile.v1",
        )
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-IDENTITY-005")

        with self.assertRaises(ModelFailure) as naked_subject:
            CheckResult(
                OutcomeClass.AFFIRMATIVE,
                "identity:test",
                "FRI-IOR-IDENTITY-100",
                "invalid result formation",
                subject="sha256:naked-digest",  # type: ignore[arg-type]
            )
        self.assertIs(naked_subject.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(naked_subject.exception.code, "FRI-IOR-IDENTITY-011")


class BinaryFoldTest(unittest.TestCase):
    def setUp(self) -> None:
        self.coefficients = (
            _extension(3, 2),
            _extension(5, 7),
            _extension(11, 13),
            _extension(17, 19),
            _extension(23, 29),
            _extension(31, 37),
            _extension(41, 43),
            _extension(47, 53),
        )
        self.first_challenge = _extension(59, 61)
        self.second_challenge = _extension(67, 71)

    def test_one_fold_matches_even_odd_polynomial_decomposition(self) -> None:
        source_values = tuple(
            evaluate_polynomial(self.coefficients, point) for point in D0.points()
        )
        expected_coefficients = (
            self.coefficients[0] + self.first_challenge * self.coefficients[1],
            self.coefficients[2] + self.first_challenge * self.coefficients[3],
            self.coefficients[4] + self.first_challenge * self.coefficients[5],
            self.coefficients[6] + self.first_challenge * self.coefficients[7],
        )
        for index, point in enumerate(D0.points()[: D0.order // 2]):
            folded = binary_fold(
                point,
                source_values[index],
                source_values[index + D0.order // 2],
                self.first_challenge,
            )
            self.assertEqual(
                folded,
                evaluate_polynomial(expected_coefficients, D1.points()[index]),
            )

    def test_two_rounds_reduce_degree_less_than_eight_below_degree_two(self) -> None:
        source_values = tuple(
            evaluate_polynomial(self.coefficients, point) for point in D0.points()
        )
        first_layer = tuple(
            binary_fold(
                D0.points()[index],
                source_values[index],
                source_values[index + D0.order // 2],
                self.first_challenge,
            )
            for index in range(D1.order)
        )
        second_layer = tuple(
            binary_fold(
                D1.points()[index],
                first_layer[index],
                first_layer[index + D1.order // 2],
                self.second_challenge,
            )
            for index in range(D2.order)
        )
        first_coefficients = (
            self.coefficients[0] + self.first_challenge * self.coefficients[1],
            self.coefficients[2] + self.first_challenge * self.coefficients[3],
            self.coefficients[4] + self.first_challenge * self.coefficients[5],
            self.coefficients[6] + self.first_challenge * self.coefficients[7],
        )
        terminal_coefficients = (
            first_coefficients[0] + self.second_challenge * first_coefficients[1],
            first_coefficients[2] + self.second_challenge * first_coefficients[3],
        )
        self.assertEqual(
            second_layer,
            tuple(
                evaluate_polynomial(terminal_coefficients, point)
                for point in D2.points()
            ),
        )
        self.assertEqual(EXACT_PROFILE.initial_degree_bound_exclusive, 8)
        self.assertEqual(EXACT_PROFILE.terminal_max_coefficient_count, 5)
        self.assertEqual(EXACT_PROFILE.terminal_degree_bound_exclusive, 2)

    def test_terminal_syntax_can_carry_a_late_degree_violation(self) -> None:
        honest = (_extension(9, 4), _extension(12, 7))
        displacement = _extension(15, 8)
        same_on_terminal_domain = canonical_polynomial(
            (
                honest[0] - displacement,
                honest[1],
                Fp2.zero(),
                Fp2.zero(),
                displacement,
            ),
            EXACT_PROFILE.terminal_max_coefficient_count,
        )
        self.assertEqual(polynomial_degree(honest), 1)
        self.assertEqual(polynomial_degree(same_on_terminal_domain), 4)
        self.assertTrue(
            polynomial_degree(honest)
            < EXACT_PROFILE.terminal_degree_bound_exclusive
        )
        self.assertFalse(
            polynomial_degree(same_on_terminal_domain)
            < EXACT_PROFILE.terminal_degree_bound_exclusive
        )
        for point in D2.points():
            self.assertEqual(
                evaluate_polynomial(honest, point),
                evaluate_polynomial(same_on_terminal_domain, point),
            )

    def test_polynomial_syntax_has_one_canonical_zero_encoding(self) -> None:
        self.assertEqual(canonical_polynomial((Fp2.zero(),), 5), (Fp2.zero(),))
        with self.assertRaises(ModelFailure) as raised:
            canonical_polynomial((_extension(1), Fp2.zero()), 5)
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-FIELD-017")

    def test_fold_resource_charge_is_atomic(self) -> None:
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=BINARY_FOLD_FIELD_OPERATIONS - 1,
                hash_calls=0,
                hash_bytes=0,
                merkle_nodes=0,
            )
        )
        with self.assertRaises(ModelFailure) as raised:
            binary_fold(Fp(1), _extension(1), _extension(2), _extension(3), counter)
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(raised.exception.code, "FRI-IOR-RESOURCE-008")
        self.assertEqual(counter.field_operations, 0)


if __name__ == "__main__":
    unittest.main()
