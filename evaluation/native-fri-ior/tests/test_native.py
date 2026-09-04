"""Tests for the exact native logical-oracle FRI execution."""

from __future__ import annotations

from dataclasses import FrozenInstanceError, replace
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.native import (  # noqa: E402
    LayerQueryAnswerOccurrence,
    LogicalOracle,
    NativeEvent,
    NativeEventKind,
    NativeOracleLayer,
    OracleEntry,
    OracleOrigin,
    TerminalPolynomial,
    derive_honest_native_trace,
    resolve_layer_query_answers,
    verify_native_trace,
)
from friiormodel.profile import D0, D1  # noqa: E402
from friiormodel.terms import (  # noqa: E402
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    SemanticId,
)


def _extension(real: int, imag: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imag))


def _honest_trace():
    coefficients = (
        _extension(3),
        _extension(5),
        _extension(7),
        _extension(11),
        _extension(13),
        _extension(17),
        _extension(19),
        _extension(23),
    )
    return derive_honest_native_trace(
        coefficients,
        _extension(59, 61),
        _extension(67, 71),
        (1, 1, 6, 11),
        ResourceCounter(),
    )


class NativePublicationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.trace = _honest_trace()

    def test_publication_is_logical_access_without_disclosure_or_binding(self) -> None:
        observation = self.trace.initial_oracle.publication_observation()

        self.assertEqual(observation["publication_mode"], "LogicalAccess")
        self.assertEqual(
            observation["effects"],
            (
                "fix-immutable-oracle",
                "grant-declared-logical-query-access",
            ),
        )
        for forbidden in (
            "entries",
            "values",
            "carrier",
            "digest",
            "commitment",
            "public_binding",
        ):
            self.assertNotIn(forbidden, observation)

    def test_oracle_carrier_is_immutable_after_formation(self) -> None:
        with self.assertRaises(FrozenInstanceError):
            self.trace.initial_oracle.entries = ()  # type: ignore[misc]

    def test_initial_and_prover_oracle_origins_are_distinct(self) -> None:
        wrong_initial = replace(
            self.trace.initial_oracle,
            origin=OracleOrigin.PROVER_ORACLE,
        )
        result = verify_native_trace(
            replace(self.trace, initial_oracle=wrong_initial),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-031")

        wrong_prover = replace(
            self.trace.prover_oracle,
            origin=OracleOrigin.INITIAL_ORACLE,
        )
        result = verify_native_trace(
            replace(self.trace, prover_oracle=wrong_prover),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-031")

    def test_exact_totality_rejects_a_missing_domain_entry(self) -> None:
        shortened = replace(
            self.trace.initial_oracle,
            entries=self.trace.initial_oracle.entries[:-1],
        )
        result = verify_native_trace(
            replace(self.trace, initial_oracle=shortened),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-033")

    def test_exact_totality_rejects_extra_and_duplicate_domain_entries(self) -> None:
        original = self.trace.initial_oracle.entries
        candidates = (
            original + (original[0],),
            original[:1] + (original[0],) + original[2:],
        )
        for entries in candidates:
            with self.subTest(entry_count=len(entries)):
                changed = replace(self.trace.initial_oracle, entries=entries)
                result = verify_native_trace(
                    replace(self.trace, initial_oracle=changed),
                    ResourceCounter(),
                )
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, "FRI-IOR-NATIVE-033")

    def test_exact_entry_order_rejects_a_reordered_total_oracle(self) -> None:
        entries = list(self.trace.prover_oracle.entries)
        entries[0], entries[1] = entries[1], entries[0]
        reordered = replace(self.trace.prover_oracle, entries=tuple(entries))

        result = verify_native_trace(
            replace(self.trace, prover_oracle=reordered),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-033")

    def test_exact_domain_entries_cover_d0_and_d1_in_declared_order(self) -> None:
        self.assertEqual(
            tuple(entry.point for entry in self.trace.initial_oracle.entries),
            D0.points(),
        )
        self.assertEqual(
            tuple(entry.point for entry in self.trace.prover_oracle.entries),
            D1.points(),
        )


class NativeTraceIdentityTest(unittest.TestCase):
    def setUp(self) -> None:
        self.trace = _honest_trace()

    def test_affirmative_subject_is_exact_native_trace_not_profile(self) -> None:
        result = verify_native_trace(self.trace, ResourceCounter())

        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIsInstance(result.subject, SemanticId)
        self.assertEqual(result.subject, self.trace.identity)
        self.assertEqual(result.subject.subject_kind, "native-fri-trace")
        self.assertEqual(result.subject.domain, "fri-ior.native-trace.v1")
        self.assertNotEqual(result.subject, self.trace.profile.identity)
        self.assertEqual(
            result.evidence["profile_dependency"],
            self.trace.profile.identity,
        )

    def test_identity_binds_every_native_verdict_input_lane(self) -> None:
        base = self.trace.identity
        initial_entries = list(self.trace.initial_oracle.entries)
        initial_entries[0] = replace(
            initial_entries[0],
            value=initial_entries[0].value + _extension(1),
        )
        changed_event = list(self.trace.events)
        changed_event[-1] = replace(changed_event[-1], subject="query-draw[changed]")
        changed_draws = list(self.trace.query_draws)
        changed_draws[0] = replace(changed_draws[0], initial_domain_index=2)
        changed_reductions = tuple(reversed(self.trace.structural_chain.reductions))

        variants = (
            replace(
                self.trace,
                profile=replace(self.trace.profile, name="alternate-native-profile"),
            ),
            replace(
                self.trace,
                initial_oracle=replace(
                    self.trace.initial_oracle,
                    entries=tuple(initial_entries),
                ),
            ),
            replace(
                self.trace,
                first_challenge=replace(
                    self.trace.first_challenge,
                    value=self.trace.beta0 + _extension(1),
                ),
            ),
            replace(
                self.trace,
                terminal=replace(
                    self.trace.terminal,
                    coefficients=(
                        self.trace.terminal.coefficients[0] + _extension(1),
                        self.trace.terminal.coefficients[1],
                    ),
                ),
            ),
            replace(self.trace, query_draws=tuple(changed_draws)),
            replace(self.trace, events=tuple(changed_event)),
            replace(
                self.trace,
                structural_chain=replace(
                    self.trace.structural_chain,
                    reductions=changed_reductions,
                ),
            ),
        )
        self.assertTrue(all(variant.identity != base for variant in variants))

    def test_request_limits_do_not_enter_native_trace_identity(self) -> None:
        identity = self.trace.identity
        narrow = ResourceCounter(
            ResourceLimits(
                field_operations=80,
                hash_calls=0,
                hash_bytes=0,
                merkle_nodes=0,
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=8,
                unique_openings=0,
                proof_bytes=0,
            )
        )
        wider = ResourceCounter()

        first = verify_native_trace(self.trace, narrow)
        second = verify_native_trace(self.trace, wider)
        self.assertEqual(first.subject, identity)
        self.assertEqual(second.subject, identity)
        self.assertNotEqual(narrow.limits, wider.limits)


class DeclaredDependencyOrderTest(unittest.TestCase):
    def setUp(self) -> None:
        self.trace = _honest_trace()

    def test_honest_event_order_places_every_fixation_before_its_coin(self) -> None:
        self.assertEqual(
            tuple((event.kind.value, event.subject) for event in self.trace.events),
            (
                ("PublishOracle", "O0"),
                ("FreshChallenge", "beta0"),
                ("PublishOracle", "O1"),
                ("FreshChallenge", "beta1"),
                ("TerminalMaterial", "terminal"),
                ("RandomQueryDraw", "query-draw[0]"),
                ("RandomQueryDraw", "query-draw[1]"),
                ("RandomQueryDraw", "query-draw[2]"),
                ("RandomQueryDraw", "query-draw[3]"),
            ),
        )

    def test_prover_dependency_cannot_declare_future_second_challenge(self) -> None:
        dependency = replace(
            self.trace.prover_oracle.declared_strategy_dependency,
            declared_read_set=("O0", "beta0", "beta1"),
        )
        oracle = replace(
            self.trace.prover_oracle,
            declared_strategy_dependency=dependency,
        )

        result = verify_native_trace(
            replace(self.trace, prover_oracle=oracle),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-039")

    def test_terminal_dependency_cannot_declare_future_query_draw(self) -> None:
        dependency = replace(
            self.trace.terminal.declared_strategy_dependency,
            declared_read_set=("O1", "beta1", "query-draw[0]"),
        )
        terminal = replace(
            self.trace.terminal,
            declared_strategy_dependency=dependency,
        )

        result = verify_native_trace(
            replace(self.trace, terminal=terminal),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-039")

    def test_second_publication_of_a_fixed_oracle_is_refused_first(self) -> None:
        events = list(self.trace.events)
        events[2] = NativeEvent(2, NativeEventKind.PUBLISH_ORACLE, "O0")

        result = verify_native_trace(
            replace(self.trace, events=tuple(events)),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-034")

    def test_terminal_before_second_challenge_is_refused_as_bad_schedule(self) -> None:
        events = list(self.trace.events)
        events[3], events[4] = (
            NativeEvent(3, NativeEventKind.TERMINAL_MATERIAL, "terminal"),
            NativeEvent(4, NativeEventKind.FRESH_CHALLENGE, "beta1"),
        )

        result = verify_native_trace(
            replace(self.trace, events=tuple(events)),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-035")


class LayerQueryAnswerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.trace = _honest_trace()

    def test_exact_two_layer_occurrence_sequence_and_answers(self) -> None:
        resources = ResourceCounter()
        resolved = resolve_layer_query_answers(self.trace, resources)
        self.assertIsInstance(resolved, tuple)
        assert isinstance(resolved, tuple)

        self.assertEqual(
            tuple(
                (
                    record.top_level_ordinal,
                    record.layer,
                    record.oracle_name,
                    record.pair_index,
                    record.positive_answer_index,
                    record.negative_answer_index,
                )
                for record in resolved
            ),
            (
                (0, NativeOracleLayer.INITIAL, "O0", 1, 1, 9),
                (0, NativeOracleLayer.FIRST_FOLD, "O1", 1, 1, 5),
                (1, NativeOracleLayer.INITIAL, "O0", 1, 1, 9),
                (1, NativeOracleLayer.FIRST_FOLD, "O1", 1, 1, 5),
                (2, NativeOracleLayer.INITIAL, "O0", 6, 6, 14),
                (2, NativeOracleLayer.FIRST_FOLD, "O1", 2, 2, 6),
                (3, NativeOracleLayer.INITIAL, "O0", 3, 3, 11),
                (3, NativeOracleLayer.FIRST_FOLD, "O1", 3, 3, 7),
            ),
        )
        for record in resolved:
            oracle = (
                self.trace.initial_oracle
                if record.layer is NativeOracleLayer.INITIAL
                else self.trace.prover_oracle
            )
            self.assertEqual(
                record.ordered_answers,
                (
                    (
                        record.positive_answer_index,
                        oracle.entries[record.positive_answer_index].value,
                    ),
                    (
                        record.negative_answer_index,
                        oracle.entries[record.negative_answer_index].value,
                    ),
                ),
            )
        self.assertEqual(resources.logical_query_occurrences, 8)

    def test_repeated_draw_preserves_repeated_layer_occurrences(self) -> None:
        resolved = resolve_layer_query_answers(self.trace, ResourceCounter())
        assert isinstance(resolved, tuple)

        self.assertEqual(len(resolved), 8)
        for first, repeated in zip(resolved[:2], resolved[2:4], strict=True):
            self.assertEqual(first.top_level_ordinal, 0)
            self.assertEqual(repeated.top_level_ordinal, 1)
            self.assertEqual(first.layer, repeated.layer)
            self.assertEqual(first.oracle_name, repeated.oracle_name)
            self.assertEqual(first.pair_index, repeated.pair_index)
            self.assertEqual(first.ordered_answers, repeated.ordered_answers)

    def test_each_pair_answer_is_fetched_once_per_occurrence(self) -> None:
        calls: list[tuple[str, int]] = []
        original = LogicalOracle.logical_answer_at

        def counted(oracle: LogicalOracle, index: int) -> Fp2:
            calls.append((oracle.name, index))
            return original(oracle, index)

        with patch.object(LogicalOracle, "logical_answer_at", new=counted):
            result = verify_native_trace(self.trace, ResourceCounter())

        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(
            calls,
            [
                ("O0", 1),
                ("O0", 9),
                ("O1", 1),
                ("O1", 5),
                ("O0", 1),
                ("O0", 9),
                ("O1", 1),
                ("O1", 5),
                ("O0", 6),
                ("O0", 14),
                ("O1", 2),
                ("O1", 6),
                ("O0", 3),
                ("O0", 11),
                ("O1", 3),
                ("O1", 7),
            ],
        )

    def test_resolution_requires_admitted_shape_and_typed_inputs(self) -> None:
        shortened = replace(
            self.trace.initial_oracle,
            entries=self.trace.initial_oracle.entries[:-1],
        )
        counter = ResourceCounter()
        refused = resolve_layer_query_answers(
            replace(self.trace, initial_oracle=shortened),
            counter,
        )
        self.assertIsInstance(refused, CheckResult)
        assert isinstance(refused, CheckResult)
        self.assertIs(refused.outcome, OutcomeClass.REFUSED)
        self.assertEqual(refused.code, "FRI-IOR-NATIVE-033")
        self.assertEqual(counter.logical_query_occurrences, 0)

        malformed_trace = resolve_layer_query_answers({}, ResourceCounter())
        self.assertIsInstance(malformed_trace, CheckResult)
        assert isinstance(malformed_trace, CheckResult)
        self.assertEqual(malformed_trace.code, "FRI-IOR-NATIVE-054")

        malformed_counter = resolve_layer_query_answers(
            self.trace,
            object(),  # type: ignore[arg-type]
        )
        self.assertIsInstance(malformed_counter, CheckResult)
        assert isinstance(malformed_counter, CheckResult)
        self.assertEqual(malformed_counter.code, "FRI-IOR-NATIVE-055")

        with self.assertRaises(ModelFailure) as malformed_record:
            LayerQueryAnswerOccurrence(
                0,
                NativeOracleLayer.INITIAL,
                "O1",
                1,
                1,
                9,
                _extension(1),
                _extension(2),
            )
        self.assertEqual(malformed_record.exception.code, "FRI-IOR-NATIVE-053")

    def test_layer_query_answer_record_is_immutable(self) -> None:
        resolved = resolve_layer_query_answers(self.trace, ResourceCounter())
        assert isinstance(resolved, tuple)
        with self.assertRaises(FrozenInstanceError):
            resolved[0].pair_index = 2  # type: ignore[misc]


class NativeExecutionTest(unittest.TestCase):
    def setUp(self) -> None:
        self.trace = _honest_trace()

    def test_honest_native_execution_accepts(self) -> None:
        resources = ResourceCounter()
        result = verify_native_trace(self.trace, resources)

        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-100")
        self.assertEqual(result.evidence["protocol_verdict"], "Accept")
        self.assertEqual(result.evidence["fold_checks"], 8)
        self.assertEqual(result.evidence["authentication_checks"], 0)
        self.assertEqual(result.evidence["random_query_draw_count"], 4)
        self.assertEqual(result.evidence["logical_query_occurrence_count"], 8)
        self.assertEqual(resources.logical_query_occurrences, 8)
        self.assertEqual(resources.field_operations, 80)
        self.assertTrue(result.evidence["declared_dependency_order_checked"])
        self.assertFalse(result.evidence["establishes_strategy_nonanticipation"])

    def test_duplicate_query_draws_remain_distinct_ordered_occurrences(self) -> None:
        resources = ResourceCounter()
        result = verify_native_trace(self.trace, resources)

        self.assertEqual(
            result.evidence["ordered_random_query_indices"],
            (1, 1, 6, 11),
        )
        self.assertEqual(result.evidence["random_query_draw_count"], 4)
        self.assertEqual(result.evidence["unique_random_query_index_count"], 3)
        self.assertEqual(result.evidence["logical_query_occurrence_count"], 8)
        self.assertEqual(result.evidence["unique_logical_pair_count"], 6)
        self.assertEqual(result.evidence["fold_checks"], 8)
        self.assertEqual(resources.logical_query_occurrences, 8)

    def test_fold_inconsistency_rejects_without_any_authentication_layer(self) -> None:
        entries = list(self.trace.prover_oracle.entries)
        entries[1] = OracleEntry(entries[1].point, entries[1].value + _extension(1))
        changed_oracle = replace(self.trace.prover_oracle, entries=tuple(entries))

        result = verify_native_trace(
            replace(self.trace, prover_oracle=changed_oracle),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-048")
        self.assertEqual(result.evidence["protocol_verdict"], "Reject")

    def test_second_fold_inconsistency_is_the_first_failure(self) -> None:
        coefficients = self.trace.terminal.coefficients
        changed_terminal = TerminalPolynomial(
            (coefficients[0] + _extension(1), coefficients[1]),
            self.trace.terminal.declared_strategy_dependency,
        )

        result = verify_native_trace(
            replace(self.trace, terminal=changed_terminal),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "native:verification")
        self.assertEqual(result.code, "FRI-IOR-NATIVE-049")

    def test_fold_consistent_trace_reaches_late_terminal_degree_boundary(self) -> None:
        honest_coefficients = self.trace.terminal.coefficients
        self.assertEqual(len(honest_coefficients), 2)
        displacement = _extension(15, 8)
        same_on_d2 = (
            honest_coefficients[0] - displacement,
            honest_coefficients[1],
            Fp2.zero(),
            Fp2.zero(),
            displacement,
        )
        terminal = TerminalPolynomial(
            same_on_d2,
            self.trace.terminal.declared_strategy_dependency,
        )

        result = verify_native_trace(
            replace(self.trace, terminal=terminal),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-050")
        self.assertEqual(result.evidence["terminal_degree"], 4)

    def test_structural_chain_does_not_infer_theorem_or_outer_relation(self) -> None:
        result = verify_native_trace(self.trace, ResourceCounter())
        claim = self.trace.structural_chain.claim

        self.assertFalse(claim.establishes_proximity)
        self.assertFalse(claim.implies_outer_relation)
        self.assertTrue(
            all(
                not reduction.establishes_proximity_preservation
                for reduction in self.trace.structural_chain.reductions
            )
        )
        self.assertFalse(result.evidence["establishes_proximity"])
        self.assertFalse(result.evidence["establishes_proximity_preservation"])
        self.assertFalse(result.evidence["infers_outer_relation"])

    def test_malformed_refused_limit_and_checker_outcomes_are_distinct(self) -> None:
        malformed = verify_native_trace({"trace": "not-typed"}, ResourceCounter())

        entries = list(self.trace.prover_oracle.entries)
        entries[1] = OracleEntry(entries[1].point, entries[1].value + _extension(1))
        refused = verify_native_trace(
            replace(
                self.trace,
                prover_oracle=replace(
                    self.trace.prover_oracle,
                    entries=tuple(entries),
                ),
            ),
            ResourceCounter(),
        )

        limited = verify_native_trace(
            self.trace,
            ResourceCounter(
                ResourceLimits(
                    field_operations=79,
                    hash_calls=0,
                    hash_bytes=0,
                    merkle_nodes=0,
                    transcript_frames=0,
                    sampler_attempts=0,
                    grinding_trials=0,
                    logical_query_occurrences=8,
                    unique_openings=0,
                    proof_bytes=0,
                )
            ),
        )

        with patch(
            "friiormodel.native.binary_fold",
            side_effect=RuntimeError("fault injection"),
        ):
            checker = verify_native_trace(self.trace, ResourceCounter())

        self.assertIs(malformed.outcome, OutcomeClass.MALFORMED)
        self.assertIs(refused.outcome, OutcomeClass.REFUSED)
        self.assertIs(
            limited.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertIs(checker.outcome, OutcomeClass.CHECKER_FAILURE)
        self.assertEqual(checker.code, "FRI-IOR-CHECKER-001")


if __name__ == "__main__":
    unittest.main()
