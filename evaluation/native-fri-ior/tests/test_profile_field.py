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
    POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS,
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
    MAX_TERM_BYTES,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    SEMANTIC_REGIME_ID,
    SemanticId,
    check_semantic_id,
    encode_term,
    semantic_id,
)


def _extension(real: int, imag: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imag))


class CanonicalTermTest(unittest.TestCase):
    def test_host_container_subclasses_are_not_closed_term_authority(self) -> None:
        class DictSubclass(dict[str, object]):
            pass

        class ListSubclass(list[object]):
            pass

        class StringSubclass(str):
            pass

        class BytesSubclass(bytes):
            pass

        for value in (
            DictSubclass({"a": 1}),
            ListSubclass([1]),
            StringSubclass("x"),
            BytesSubclass(b"x"),
        ):
            with self.subTest(type=type(value).__name__), self.assertRaises(
                ModelFailure
            ) as raised:
                encode_term(value)
            self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
            self.assertEqual(raised.exception.code, "FRI-IOR-TERM-004")

    def test_oversized_scalars_refuse_before_canonical_allocation(self) -> None:
        values = (
            "x" * (MAX_TERM_BYTES + 1),
            b"x" * MAX_TERM_BYTES,
            1 << (8 * MAX_TERM_BYTES),
        )
        for value in values:
            with self.subTest(type=type(value).__name__), self.assertRaises(
                ModelFailure
            ) as raised:
                encode_term(value)
            self.assertIs(
                raised.exception.outcome,
                OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            )
            self.assertEqual(raised.exception.code, "FRI-IOR-TERM-005")

    def test_composite_encoding_enforces_a_cumulative_byte_bound(self) -> None:
        with self.assertRaises(ModelFailure) as sequence_failure:
            encode_term(tuple(b"x" * 100 for _ in range(700)))
        self.assertEqual(sequence_failure.exception.code, "FRI-IOR-TERM-005")

        oversized_keys = {
            f"key-{index:04d}-" + "x" * 70: None for index in range(1000)
        }
        with self.assertRaises(ModelFailure) as map_failure:
            encode_term(oversized_keys)
        self.assertEqual(map_failure.exception.code, "FRI-IOR-TERM-005")


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

        for encoded in (b"\x61", b"\xff"):
            with self.subTest(encoded=encoded), self.assertRaises(
                ModelFailure
            ) as noncanonical:
                Fp.from_bytes(encoded)
            self.assertIs(noncanonical.exception.outcome, OutcomeClass.MALFORMED)
            self.assertEqual(noncanonical.exception.boundary, "field:codec")
            self.assertEqual(noncanonical.exception.code, "FRI-IOR-FIELD-003")

        with self.assertRaises(ModelFailure) as extension_noncanonical:
            Fp2.from_bytes(b"\x00\x61")
        self.assertIs(
            extension_noncanonical.exception.outcome,
            OutcomeClass.MALFORMED,
        )
        self.assertEqual(extension_noncanonical.exception.boundary, "field:codec")
        self.assertEqual(extension_noncanonical.exception.code, "FRI-IOR-FIELD-003")

    def test_polynomial_evaluation_charges_exact_declared_cost(self) -> None:
        coefficients = (_extension(3), _extension(5, 7), _extension(11, 13))
        expected_charge = (
            len(coefficients) * POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS
        )
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=expected_charge,
                hash_calls=0,
                hash_bytes=0,
                merkle_nodes=0,
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
            )
        )

        self.assertEqual(
            evaluate_polynomial(coefficients, Fp(8), counter),
            evaluate_polynomial(coefficients, Fp(8)),
        )
        self.assertEqual(counter.field_operations, expected_charge)
        self.assertEqual(
            counter.snapshot(),
            {**counter.limits.to_term(), "field_operations": expected_charge},
        )

    def test_polynomial_evaluation_resource_charge_is_atomic(self) -> None:
        coefficients = (_extension(3), _extension(5, 7), _extension(11, 13))
        required = len(coefficients) * POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=required - 1,
                hash_calls=0,
                hash_bytes=0,
                merkle_nodes=0,
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
            )
        )

        with self.assertRaises(ModelFailure) as raised:
            evaluate_polynomial(coefficients, Fp(8), counter)
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(raised.exception.code, "FRI-IOR-RESOURCE-008")
        self.assertEqual(counter.snapshot(), {name: 0 for name in counter.snapshot()})

    def test_polynomial_evaluation_meter_requires_resource_counter(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            evaluate_polynomial(
                (_extension(3), _extension(5)),
                Fp(8),
                object(),  # type: ignore[arg-type]
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.boundary, "field:polynomial")
        self.assertEqual(raised.exception.code, "FRI-IOR-FIELD-018")

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
    def test_resource_carrier_subclasses_cannot_override_accounting(self) -> None:
        class CounterSubclass(ResourceCounter):
            def consume_hash(self, payload_bytes: int, *, merkle_nodes: int = 0) -> None:
                return None

        class LimitsSubclass(ResourceLimits):
            pass

        with self.assertRaises(ModelFailure) as counter_failure:
            CounterSubclass()
        self.assertEqual(counter_failure.exception.code, "FRI-IOR-RESOURCE-010")

        with self.assertRaises(ModelFailure) as limits_failure:
            LimitsSubclass(
                field_operations=0,
                hash_calls=0,
                hash_bytes=0,
                merkle_nodes=0,
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
            )
        self.assertEqual(limits_failure.exception.code, "FRI-IOR-RESOURCE-009")

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
        for alternate in (
            replace(EXACT_PROFILE, name="another-finite-profile"),
            replace(EXACT_PROFILE, merkle_hash="another-hash"),
        ):
            with self.subTest(alternate=alternate.name):
                result = admit_exact_profile(alternate)
                self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
                self.assertEqual(result.code, "FRI-IOR-PROFILE-018")

    def test_incoherent_profile_parameters_are_malformed_at_formation(self) -> None:
        cases = (
            ({"modulus": 101}, "FRI-IOR-PROFILE-025"),
            ({"primitive_generator": 1}, "FRI-IOR-PROFILE-026"),
            ({"extension_nonresidue": 1}, "FRI-IOR-PROFILE-027"),
            ({"merkle_hash": ""}, "FRI-IOR-PROFILE-028"),
            ({"domains": (D0, D0, D2)}, "FRI-IOR-PROFILE-029"),
            ({"initial_degree_bound_exclusive": 17}, "FRI-IOR-PROFILE-030"),
            ({"terminal_max_coefficient_count": 9}, "FRI-IOR-PROFILE-031"),
            ({"terminal_degree_bound_exclusive": 5}, "FRI-IOR-PROFILE-032"),
            ({"ordered_query_count": 257}, "FRI-IOR-PROFILE-033"),
            ({"merkle_salt_bytes": 0}, "FRI-IOR-PROFILE-034"),
            ({"merkle_cap_size": 3}, "FRI-IOR-PROFILE-035"),
            ({"merkle_cap_size": 4}, "FRI-IOR-PROFILE-036"),
        )
        for changes, expected_code in cases:
            with self.subTest(changes=changes), self.assertRaises(
                ModelFailure
            ) as raised:
                replace(EXACT_PROFILE, **changes)
            self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
            self.assertEqual(raised.exception.code, expected_code)

    def test_request_limits_do_not_enter_profile_identity(self) -> None:
        profile_term = EXACT_PROFILE.to_term()
        profile_identity = EXACT_PROFILE.identity
        small_request = ResourceCounter(
            ResourceLimits(
                field_operations=8,
                hash_calls=1,
                hash_bytes=64,
                merkle_nodes=0,
                transcript_frames=1,
                sampler_attempts=2,
                grinding_trials=3,
                logical_query_occurrences=4,
                unique_openings=2,
                proof_bytes=128,
            )
        )
        larger_request = ResourceCounter(
            ResourceLimits(
                field_operations=80,
                hash_calls=10,
                hash_bytes=640,
                merkle_nodes=6,
                transcript_frames=10,
                sampler_attempts=20,
                grinding_trials=30,
                logical_query_occurrences=40,
                unique_openings=20,
                proof_bytes=1280,
            )
        )

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
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=0,
                hash_calls=1,
                hash_bytes=32,
                merkle_nodes=0,
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
            )
        )
        counter.consume_hash(32)
        self.assertEqual(counter.hash_calls, 1)
        self.assertEqual(counter.hash_bytes, 32)
        self.assertEqual(counter.merkle_nodes, 0)

    def test_composite_resource_dimensions_are_counted_explicitly(self) -> None:
        limits = ResourceLimits(
            field_operations=0,
            hash_calls=0,
            hash_bytes=0,
            merkle_nodes=0,
            transcript_frames=2,
            sampler_attempts=3,
            grinding_trials=4,
            logical_query_occurrences=5,
            unique_openings=2,
            proof_bytes=100,
        )
        counter = ResourceCounter(limits)
        counter.consume_transcript_frames(2)
        counter.consume_sampler_attempts(3)
        counter.consume_grinding_trials(4)
        counter.consume_logical_query_occurrences(5)
        counter.consume_unique_openings(2)
        counter.consume_proof_bytes(100)
        self.assertEqual(counter.snapshot(), limits.to_term())

    def test_query_opening_composite_charge_is_atomic(self) -> None:
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=0,
                hash_calls=0,
                hash_bytes=0,
                merkle_nodes=0,
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=4,
                unique_openings=2,
                proof_bytes=100,
            )
        )
        counter.consume_query_opening_resources(
            logical_query_occurrences=3,
            unique_openings=1,
            proof_bytes=80,
        )
        before = counter.snapshot()
        with self.assertRaises(ModelFailure) as raised:
            counter.consume_query_opening_resources(
                logical_query_occurrences=1,
                unique_openings=1,
                proof_bytes=21,
            )
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(counter.snapshot(), before)


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
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
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
