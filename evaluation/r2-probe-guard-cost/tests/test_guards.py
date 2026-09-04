"""COST-1, settled by measurement — of size and of work, which differ."""

from __future__ import annotations

from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from guard_model.guards import (  # noqa: E402
    FALSE,
    TRUE,
    And,
    BooleanAtom,
    GuardError,
    GuardProfile,
    Not,
    Or,
    Robdd,
    admit_guard,
    atom_keys,
    finite_domain_formula,
    interleaved_order,
    pairing_formula,
    pairing_predicate,
    robdd_cost,
    robdd_size,
    separated_order,
)
from guard_model.terms import OutcomeClass  # noqa: E402


def _evaluate(diagram: Robdd, root: int, assignment: dict[str, bool]) -> bool:
    """Follow the diagram to a terminal under one assignment."""

    node = root
    while node not in (FALSE, TRUE):
        index, low, high = diagram.nodes[node]
        node = high if assignment[diagram.order[index]] else low
    return node == TRUE


class TheDiagramDenotesTheFormulaTest(unittest.TestCase):
    """The rewrite is only worth anything if the diagram is still correct.

    Size and work are properties of a structure; they say nothing unless the
    structure denotes the formula it was built from.  So this is checked by
    exhaustion before any cost claim is made from it.
    """

    def test_both_orders_denote_the_same_function_as_the_predicate(self) -> None:
        for n in (1, 2, 3, 4):
            predicate = pairing_predicate(n)
            for order in (interleaved_order(n), separated_order(n)):
                diagram = Robdd(order)
                root = diagram.build(pairing_formula(n))
                for bits in product((False, True), repeat=len(order)):
                    keyed = dict(zip(order, bits))
                    plain = {name.split(":", 1)[1]: value for name, value in keyed.items()}
                    with self.subTest(n=n, order=order[:2], bits=bits):
                        self.assertEqual(_evaluate(diagram, root, keyed), predicate(plain))

    def test_negation_and_double_negation_are_exact(self) -> None:
        order = ("bool:a", "bool:b")
        diagram = Robdd(order)
        formula = And((BooleanAtom("a"), BooleanAtom("b")))
        root = diagram.build(formula)
        negated = diagram.build(Not(formula))
        self.assertNotEqual(root, negated)
        self.assertEqual(diagram.build(Not(Not(formula))), root)

    def test_a_variable_outside_the_declared_order_is_malformed(self) -> None:
        with self.assertRaises(GuardError):
            Robdd(("bool:a",)).build(BooleanAtom("b"))

    def test_a_repeated_variable_order_is_malformed(self) -> None:
        with self.assertRaises(GuardError):
            Robdd(("bool:a", "bool:a"))


class CanonicalityIsNotCompactnessTest(unittest.TestCase):
    """The same formula, two legitimate fixed orders, two cost classes."""

    def test_the_interleaved_order_is_linear(self) -> None:
        sizes = [robdd_size(pairing_formula(n), interleaved_order(n)) for n in range(1, 9)]
        deltas = {b - a for a, b in zip(sizes, sizes[1:])}
        self.assertEqual(deltas, {2}, msg=f"expected a constant step, got {sizes}")

    def test_the_separated_order_doubles(self) -> None:
        sizes = [robdd_size(pairing_formula(n), separated_order(n)) for n in range(1, 9)]
        ratios = {b // a for a, b in zip(sizes, sizes[1:])}
        self.assertEqual(ratios, {2}, msg=f"expected doubling, got {sizes}")

    def test_the_gap_is_already_large_at_eight_pairs(self) -> None:
        interleaved = robdd_size(pairing_formula(8), interleaved_order(8))
        separated = robdd_size(pairing_formula(8), separated_order(8))
        self.assertEqual(interleaved, 18)
        self.assertEqual(separated, 512)
        self.assertGreater(separated / interleaved, 28)

    def test_both_orders_are_legitimate_fixed_orders(self) -> None:
        """Neither is malformed; a regime simply has to pick one."""

        n = 5
        self.assertEqual(sorted(interleaved_order(n)), sorted(separated_order(n)))
        self.assertNotEqual(interleaved_order(n), separated_order(n))


class WorkIsNotSizeTest(unittest.TestCase):
    """The measurement the ledger asks for, and the one it is easy to fake.

    The row's required pressure reads "Real/adversarial node **and work**
    measurements".  A previous version of this witness enumerated every
    assignment, so it reported the right node counts while doing identical work
    for both orders — 65536 predicate evaluations each at ``n = 8``.  These
    tests fail against any build whose cost does not depend on the diagram.
    """

    def test_work_separates_the_two_orders(self) -> None:
        interleaved = robdd_cost(pairing_formula(8), interleaved_order(8))
        separated = robdd_cost(pairing_formula(8), separated_order(8))
        self.assertEqual(interleaved.nodes, 18)
        self.assertEqual(separated.nodes, 512)
        self.assertGreater(separated.expansions, 10 * interleaved.expansions)

    def test_work_is_not_a_function_of_input_width_alone(self) -> None:
        """Same variable count, same formula, different work."""

        interleaved = robdd_cost(pairing_formula(8), interleaved_order(8))
        separated = robdd_cost(pairing_formula(8), separated_order(8))
        self.assertEqual(interleaved.variables, separated.variables)
        self.assertNotEqual(interleaved.expansions, separated.expansions)

    def test_the_good_order_costs_a_polynomial_in_the_atom_count(self) -> None:
        """Exactly ``n^2`` expansions, which is a claim a wrong build fails."""

        measured = {
            n: robdd_cost(pairing_formula(n), interleaved_order(n)).expansions
            for n in range(2, 10)
        }
        self.assertEqual(measured, {n: n * n for n in range(2, 10)})

    def test_the_bad_order_costs_an_exponential(self) -> None:
        """Each added pair more than doubles the work, all the way up."""

        work = [
            robdd_cost(pairing_formula(n), separated_order(n)).expansions
            for n in range(3, 10)
        ]
        ratios = [b / a for a, b in zip(work, work[1:])]
        self.assertTrue(
            all(ratio > 2.0 for ratio in ratios),
            msg=f"expected every step to more than double, got {work}",
        )

    def test_the_separation_widens_with_scale(self) -> None:
        """A constant-factor gap would be a different and much weaker claim."""

        gaps = [
            robdd_cost(pairing_formula(n), separated_order(n)).expansions
            / robdd_cost(pairing_formula(n), interleaved_order(n)).expansions
            for n in range(3, 10)
        ]
        self.assertEqual(gaps, sorted(gaps))
        self.assertGreater(gaps[-1] / gaps[0], 10)


class TheFiniteAtomIsModelledTest(unittest.TestCase):
    """The corpus admits two atom kinds; only one used to be exercised.

    `FiniteValueEquals` is the kind whose encoding makes the variable count
    depend on the declared domain size rather than on how many members the
    author mentioned, so its cost behaviour is not inherited from the Boolean
    case.
    """

    def test_a_finite_domain_atom_carries_its_member_into_the_key(self) -> None:
        formula = finite_domain_formula("side", ("prover", "verifier", "environment"))
        self.assertEqual(
            atom_keys(formula),
            ("eq:side=prover", "eq:side=verifier", "eq:side=environment"),
        )

    def test_domain_size_drives_the_diagram_not_the_reference_count(self) -> None:
        small = finite_domain_formula("side", ("a", "b"))
        large = finite_domain_formula("side", tuple("abcdefgh"))
        small_cost = robdd_cost(small, atom_keys(small))
        large_cost = robdd_cost(large, atom_keys(large))
        self.assertEqual(small_cost.variables, 2)
        self.assertEqual(large_cost.variables, 8)
        self.assertGreater(large_cost.nodes, small_cost.nodes)

    def test_the_two_atom_kinds_do_not_collide_in_the_order(self) -> None:
        mixed = Or((BooleanAtom("side"), Or((finite_domain_formula("side", ("a",)),))))
        self.assertEqual(atom_keys(mixed), ("bool:side", "eq:side=a"))


class BoundedIdentityWorkTest(unittest.TestCase):
    """A guard beyond the envelope is a resource fact, not a verdict."""

    def setUp(self) -> None:
        self.profile = GuardProfile("r2.probe.guard.default")

    def test_a_small_guard_admits(self) -> None:
        result = admit_guard(self.profile, pairing_formula(4), interleaved_order(4))
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.evidence["nodes"], 10)

    def test_the_declared_default_bound_refuses_the_adversarial_case(self) -> None:
        """The envelope has to bind on something, or it declares nothing.

        An earlier default of 512 sat exactly on the separated-order diagram at
        ``n = 8``, and against a ``>`` comparison it admitted it.  Every refusal
        the witness demonstrated came from an ad-hoc narrower profile, so the
        number the module actually declares was never shown to refuse anything.
        """

        result = admit_guard(self.profile, pairing_formula(8), separated_order(8))
        self.assertIs(result.outcome, OutcomeClass.RESOURCE_EXCEEDED)
        self.assertEqual(result.boundary, "guard:representation")
        self.assertEqual(result.code, "R2-GUARD-001")
        self.assertEqual(result.evidence["nodes"], 512)

    def test_an_oversized_guard_is_a_resource_refusal_not_a_negative(self) -> None:
        """`ResourceExceeded`, so no protocol conclusion is drawn from it."""

        narrow = GuardProfile("r2.probe.guard.narrow", max_nodes=64)
        result = admit_guard(narrow, pairing_formula(8), separated_order(8))
        self.assertIs(result.outcome, OutcomeClass.RESOURCE_EXCEEDED)
        self.assertEqual(result.boundary, "guard:representation")
        self.assertEqual(result.evidence["nodes"], 512)

    def test_the_same_formula_admits_under_a_better_order(self) -> None:
        """The refusal is about representation, not about the guard's meaning."""

        self.assertIs(
            admit_guard(self.profile, pairing_formula(8), separated_order(8)).outcome,
            OutcomeClass.RESOURCE_EXCEEDED,
        )
        self.assertIs(
            admit_guard(self.profile, pairing_formula(8), interleaved_order(8)).outcome,
            OutcomeClass.AFFIRMATIVE,
        )

    def test_a_work_refusal_is_distinct_from_a_size_refusal(self) -> None:
        """Two bounds, two boundaries: a bound on one does not bound the other."""

        thrifty = GuardProfile("r2.probe.guard.thrifty", max_nodes=4096, max_work=100)
        result = admit_guard(thrifty, pairing_formula(8), separated_order(8))
        self.assertIs(result.outcome, OutcomeClass.RESOURCE_EXCEEDED)
        self.assertEqual(result.boundary, "guard:work")
        self.assertEqual(result.code, "R2-GUARD-002")
        self.assertLess(result.evidence["nodes"], thrifty.max_nodes)

    def test_a_malformed_guard_is_not_a_resource_refusal(self) -> None:
        result = admit_guard(self.profile, BooleanAtom("absent"), ("bool:present",))
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "R2-GUARD-000")


if __name__ == "__main__":
    unittest.main()
