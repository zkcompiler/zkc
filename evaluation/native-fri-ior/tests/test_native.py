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
    NativeEvent,
    NativeEventKind,
    OracleEntry,
    OracleOrigin,
    TerminalPolynomial,
    derive_honest_native_trace,
    verify_native_trace,
)
from friiormodel.profile import D0, D1  # noqa: E402
from friiormodel.terms import (  # noqa: E402
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
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


class NativeCausalityTest(unittest.TestCase):
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
                ("LogicalQuery", "query[0]"),
                ("LogicalQuery", "query[1]"),
                ("LogicalQuery", "query[2]"),
                ("LogicalQuery", "query[3]"),
            ),
        )

    def test_prover_oracle_cannot_read_the_future_second_challenge(self) -> None:
        decision = replace(
            self.trace.prover_oracle.strategy_decision,
            read_set=("O0", "beta0", "beta1"),
        )
        oracle = replace(self.trace.prover_oracle, strategy_decision=decision)

        result = verify_native_trace(
            replace(self.trace, prover_oracle=oracle),
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-NATIVE-039")

    def test_terminal_cannot_read_query_randomness(self) -> None:
        decision = replace(
            self.trace.terminal.strategy_decision,
            read_set=("O1", "beta1", "query[0]"),
        )
        terminal = replace(self.trace.terminal, strategy_decision=decision)

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
        self.assertEqual(resources.logical_query_occurrences, 4)
        self.assertEqual(resources.field_operations, 80)

    def test_duplicate_query_draws_remain_distinct_ordered_occurrences(self) -> None:
        resources = ResourceCounter()
        result = verify_native_trace(self.trace, resources)

        self.assertEqual(result.evidence["ordered_query_indices"], (1, 1, 6, 11))
        self.assertEqual(result.evidence["logical_query_count"], 4)
        self.assertEqual(result.evidence["unique_query_count"], 3)
        self.assertEqual(result.evidence["fold_checks"], 8)
        self.assertEqual(resources.logical_query_occurrences, 4)

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
            self.trace.terminal.strategy_decision,
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
                    field_operations=63,
                    hash_calls=0,
                    hash_bytes=0,
                    merkle_nodes=0,
                    transcript_frames=0,
                    sampler_attempts=0,
                    grinding_trials=0,
                    logical_query_occurrences=4,
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
