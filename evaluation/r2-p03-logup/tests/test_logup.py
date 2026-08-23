"""Logup: the first witness whose subject is a claim graph.

Two positive inhabitants (the two shipped origin variants) and six named
negative mutations.  Two of the negatives reproduce fixtures the shipped suite
already authors, with the boundaries it already names; four isolate laws no
existing scenario tests.
"""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p03model.logup import (  # noqa: E402
    ANCHORS,
    BUS_CHALLENGE_SPACE,
    ROLES,
    Mutation,
    Origin,
    Seat,
    Variant,
    admit_core,
    build_core,
    correspondence,
    load_fixture,
    mutate,
)
from p03model.terms import OutcomeClass  # noqa: E402


REPO_ROOT = Path(__file__).resolve().parents[3]


class PositiveInhabitantTest(unittest.TestCase):
    """Both shipped origin variants must inhabit the model."""

    def test_the_bus_variant_admits(self) -> None:
        result = admit_core(build_core(Variant.BUS))
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE, msg=result.detail)

    def test_the_range_check_variant_admits(self) -> None:
        result = admit_core(build_core(Variant.RANGE_CHECK))
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE, msg=result.detail)

    def test_the_two_variants_differ_only_in_seats(self) -> None:
        bus = {c.role: (c.origin, c.seat) for c in build_core(Variant.BUS).columns}
        rng = {c.role: (c.origin, c.seat) for c in build_core(Variant.RANGE_CHECK).columns}
        self.assertEqual(bus["queries"], rng["queries"])
        self.assertEqual(bus["multiplicities"], rng["multiplicities"])
        self.assertNotEqual(bus["table"], rng["table"])
        self.assertEqual(rng["table"], (Origin.PREPROCESSED, Seat.SEAL_BINDING))

    def test_a_seal_bound_table_needs_no_material_binding(self) -> None:
        """It absorbs its own digest; a binding would spell that fact twice."""

        core = build_core(Variant.RANGE_CHECK)
        self.assertNotIn("table", core.material_bindings)
        self.assertIn("queries", core.material_bindings)
        self.assertIn("multiplicities", core.material_bindings)

    def test_the_identity_claim_leaves_undischarged(self) -> None:
        core = build_core(Variant.BUS)
        self.assertEqual(
            [r.route for r in core.residuals],
            ["logup-identity-discharge-not-modeled"],
        )
        result = admit_core(core)
        self.assertEqual(
            result.evidence["residual"], "logup-identity-discharge-not-modeled"
        )


class ClaimGraphTest(unittest.TestCase):
    """The subject no other witness reaches."""

    def setUp(self) -> None:
        self.core = build_core(Variant.BUS)

    def test_an_inclusion_claim_is_produced_and_consumed_exactly_once(self) -> None:
        consumers = [r for r in self.core.reductions if "inclusion" in r.consumes]
        self.assertEqual(len(consumers), 1)
        self.assertEqual(consumers[0].produces, ("identity",))

    def test_double_consumption_breaks_linearity(self) -> None:
        result = admit_core(mutate(self.core, Mutation.CLAIM_CONSUMED_TWICE))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.boundary, "logup:claim-linearity")
        self.assertEqual(result.code, "P03-012")

    def test_an_unrouted_claim_at_the_terminal_is_refused(self) -> None:
        result = admit_core(mutate(self.core, Mutation.CLAIM_UNROUTED_AT_TERMINAL))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.boundary, "logup:terminal-closure")
        self.assertEqual(result.code, "P03-013")

    def test_a_claim_cannot_be_both_consumed_and_routed_out(self) -> None:
        from dataclasses import replace

        from p03model.logup import Residual

        doubled = replace(
            self.core, residuals=self.core.residuals + (Residual("inclusion", "x"),)
        )
        doubled = replace(doubled, schedule=doubled.canonical_schedule())
        result = admit_core(doubled)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P03-014")


class ShippedNegativeTest(unittest.TestCase):
    """The two mutations the shipped suite already authors."""

    def setUp(self) -> None:
        self.core = build_core(Variant.BUS)

    def test_a_widened_role_is_refused_rather_than_chosen_between(self) -> None:
        """`invalid_payload at apply.parameters.lookups ... more than one arity`.

        The point is the outcome class: the rule reading the role has two
        numbers and no reason to prefer either, so it refuses instead of
        picking.  A `Mismatch` here would mean the model had chosen.
        """

        result = admit_core(mutate(self.core, Mutation.ROLE_WIDENED))
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.boundary, "apply.parameters.lookups")
        self.assertIn("more than one arity", result.detail)

    def test_an_unanchored_inclusion_breaks_material_identity(self) -> None:
        """`[zkc-E325] an admitted material-identity constraint does not hold`."""

        result = admit_core(mutate(self.core, Mutation.UNANCHORED_INCLUSION))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.boundary, "logup:material-identity")
        self.assertIn("material-identity constraint does not hold", result.detail)


class DerivedNegativeTest(unittest.TestCase):
    """Laws the shipped fixtures do not isolate."""

    def setUp(self) -> None:
        self.core = build_core(Variant.BUS)

    def test_a_table_committed_after_its_challenge_is_the_weak_fs_shape(self) -> None:
        """The ordering law, now reachable because the schedule is authored.

        Deriving the schedule would have made this rule unfalsifiable: it could
        not fire against a core built column-before-challenge by construction.
        The mutation moves the occurrence in the spine, which is what the real
        attack does.
        """

        result = admit_core(mutate(self.core, Mutation.CHALLENGE_BEFORE_MATERIAL))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.boundary, "logup:transcript-prefix")
        self.assertEqual(result.code, "P03-005")
        self.assertIn("committed after the challenge", result.detail)

    def test_a_column_the_challenge_does_not_bind_is_refused(self) -> None:
        result = admit_core(mutate(self.core, Mutation.CHALLENGE_UNBOUND_MATERIAL))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P03-006")

    def test_a_claim_anchoring_a_role_nothing_binds_is_refused(self) -> None:
        result = admit_core(mutate(self.core, Mutation.CLAIM_ANCHORS_UNBOUND_ROLE))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P03-007")

    def test_origin_and_seat_must_agree(self) -> None:
        result = admit_core(mutate(self.core, Mutation.ORIGIN_SEAT_MISMATCH))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.boundary, "logup:origin-seat")
        self.assertEqual(result.code, "P03-004")


class FixtureCorrespondenceTest(unittest.TestCase):
    """The declared scenario is checked against pinned shipped fixtures."""

    def test_the_bus_fixture_is_pinned_and_corresponds(self) -> None:
        fixture = load_fixture(
            REPO_ROOT,
            "bus",
            "5623d87877e2609d959a6d01c5edfd4f212bc1826a2ebdee02cdb5db98bd0f16",
        )
        self.assertEqual(fixture.roles, tuple(sorted(ROLES)))
        self.assertEqual(fixture.challenge_space, BUS_CHALLENGE_SPACE)
        result = correspondence(build_core(Variant.BUS), fixture)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE, msg=result.detail)

    def test_the_range_check_fixture_is_pinned_and_corresponds(self) -> None:
        fixture = load_fixture(
            REPO_ROOT,
            "range_check",
            "ec398b7da40409b10e69e6b9e0d7a440202a0748c7d25e6a655eac8b48d3dbc8",
        )
        result = correspondence(build_core(Variant.RANGE_CHECK), fixture)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE, msg=result.detail)

    def test_a_moved_fixture_is_refused(self) -> None:
        from p03model.logup import LogupError

        with self.assertRaises(LogupError):
            load_fixture(REPO_ROOT, "bus", "00" * 32)

    def test_the_challenge_space_is_the_mersenne_prime(self) -> None:
        self.assertEqual(BUS_CHALLENGE_SPACE, (1 << 61) - 1)


class IdentityTest(unittest.TestCase):
    def test_core_identity_is_deterministic(self) -> None:
        self.assertEqual(
            build_core(Variant.BUS).identity, build_core(Variant.BUS).identity
        )

    def test_the_two_variants_have_different_identities(self) -> None:
        self.assertNotEqual(
            build_core(Variant.BUS).identity, build_core(Variant.RANGE_CHECK).identity
        )

    def test_every_role_carries_its_anchor(self) -> None:
        for column in build_core(Variant.BUS).columns:
            self.assertEqual(column.anchor, ANCHORS[column.role])


if __name__ == "__main__":
    unittest.main()
