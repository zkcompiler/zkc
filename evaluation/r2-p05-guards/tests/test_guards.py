"""COST-1, settled by measurement."""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p05model.guards import (  # noqa: E402
    GuardProfile,
    admit_guard,
    interleaved_order,
    pairing_predicate,
    robdd_size,
    separated_order,
)
from p05model.terms import OutcomeClass  # noqa: E402


class CanonicalityIsNotCompactnessTest(unittest.TestCase):
    """The same formula, two legitimate fixed orders, two cost classes."""

    def test_the_interleaved_order_is_linear(self) -> None:
        sizes = [robdd_size(pairing_predicate(n), interleaved_order(n)) for n in range(1, 9)]
        deltas = {b - a for a, b in zip(sizes, sizes[1:])}
        self.assertEqual(deltas, {2}, msg=f"expected a constant step, got {sizes}")

    def test_the_separated_order_doubles(self) -> None:
        sizes = [robdd_size(pairing_predicate(n), separated_order(n)) for n in range(1, 9)]
        ratios = {b // a for a, b in zip(sizes, sizes[1:])}
        self.assertEqual(ratios, {2}, msg=f"expected doubling, got {sizes}")

    def test_the_gap_is_already_large_at_eight_pairs(self) -> None:
        interleaved = robdd_size(pairing_predicate(8), interleaved_order(8))
        separated = robdd_size(pairing_predicate(8), separated_order(8))
        self.assertEqual(interleaved, 18)
        self.assertEqual(separated, 512)
        self.assertGreater(separated / interleaved, 28)

    def test_both_orders_are_legitimate_fixed_orders(self) -> None:
        """Neither is malformed; a regime simply has to pick one."""

        n = 5
        self.assertEqual(sorted(interleaved_order(n)), sorted(separated_order(n)))
        self.assertNotEqual(interleaved_order(n), separated_order(n))


class BoundedIdentityWorkTest(unittest.TestCase):
    """A guard beyond the envelope is a resource fact, not a verdict."""

    def setUp(self) -> None:
        self.profile = GuardProfile("r2.p05.guard.default")

    def test_a_small_guard_admits(self) -> None:
        result = admit_guard(self.profile, pairing_predicate(4), interleaved_order(4))
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.evidence["nodes"], 10)

    def test_an_oversized_guard_is_a_resource_refusal_not_a_negative(self) -> None:
        """`ResourceExceeded`, so no protocol conclusion is drawn from it."""

        narrow = GuardProfile("r2.p05.guard.narrow", max_nodes=64)
        result = admit_guard(narrow, pairing_predicate(8), separated_order(8))
        self.assertIs(result.outcome, OutcomeClass.RESOURCE_EXCEEDED)
        self.assertEqual(result.boundary, "guard:representation")
        self.assertEqual(result.evidence["nodes"], 512)

    def test_the_same_formula_admits_under_a_better_order(self) -> None:
        """The refusal is about representation, not about the guard's meaning."""

        narrow = GuardProfile("r2.p05.guard.narrow", max_nodes=64)
        self.assertIs(
            admit_guard(narrow, pairing_predicate(8), separated_order(8)).outcome,
            OutcomeClass.RESOURCE_EXCEEDED,
        )
        self.assertIs(
            admit_guard(narrow, pairing_predicate(8), interleaved_order(8)).outcome,
            OutcomeClass.AFFIRMATIVE,
        )


if __name__ == "__main__":
    unittest.main()
