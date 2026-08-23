"""Three lanes, and the substitutions each refuses."""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p04model.bridges import (  # noqa: E402
    ANCHOR_PROJECTION,
    DISCARDED_BITS,
    PREIMAGE_PREMISE,
    PROJECTED_BITS,
    SOURCE_BITS,
    Bridge,
    Lane,
    admit_bridge,
    price_projection,
    project216,
    projection_collision,
    round_trip,
)
from p04model.terms import OutcomeClass  # noqa: E402


def _bijection(**over: object) -> Bridge:
    base = dict(name="b", lane=Lane.BIJECTION, source_domain="s", target_domain="t")
    base.update(over)
    return Bridge(**base)  # type: ignore[arg-type]


def _embedding(**over: object) -> Bridge:
    base = dict(
        name="e", lane=Lane.EMBEDDING, source_domain="s", target_domain="t",
        image_predicate="in-image",
    )
    base.update(over)
    return Bridge(**base)  # type: ignore[arg-type]


def _projection(**over: object) -> Bridge:
    base = dict(
        name="p", lane=Lane.PROJECTION, source_domain="s", target_domain="t",
        collision_relation="agree-under-f", loss_bits=40, occurrence_count=1,
    )
    base.update(over)
    return Bridge(**base)  # type: ignore[arg-type]


class LaneTest(unittest.TestCase):
    def test_each_lane_admits_when_it_carries_its_own_obligations(self) -> None:
        for bridge in (_bijection(), _embedding(), _projection()):
            with self.subTest(lane=bridge.lane.value):
                self.assertIs(admit_bridge(bridge).outcome, OutcomeClass.AFFIRMATIVE)

    def test_an_embedding_without_an_image_predicate_is_incomplete(self) -> None:
        result = admit_bridge(_embedding(image_predicate=None))
        self.assertIs(result.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(result.code, "P04-003")

    def test_a_lossy_mapping_may_not_pose_as_an_embedding(self) -> None:
        result = admit_bridge(_embedding(loss_bits=40))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P04-004")

    def test_a_lossy_mapping_may_not_pose_as_a_bijection(self) -> None:
        result = admit_bridge(_bijection(loss_bits=40, collision_relation="c"))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P04-002")

    def test_a_bijection_declaring_an_image_predicate_is_an_embedding(self) -> None:
        result = admit_bridge(_bijection(image_predicate="in-image"))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P04-001")

    def test_a_projection_declaring_an_image_predicate_is_refused(self) -> None:
        result = admit_bridge(_projection(image_predicate="in-image"))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P04-005")

    def test_a_projection_must_name_its_collision_relation(self) -> None:
        result = admit_bridge(_projection(collision_relation=None))
        self.assertIs(result.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(result.code, "P04-006")

    def test_a_projection_must_state_its_loss(self) -> None:
        result = admit_bridge(_projection(loss_bits=0))
        self.assertIs(result.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(result.code, "P04-007")

    def test_a_projection_must_be_counted(self) -> None:
        result = admit_bridge(_projection(occurrence_count=None))
        self.assertIs(result.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(result.code, "P04-008")


class ShippedProjectionTest(unittest.TestCase):
    def test_the_shipped_projection_admits_as_a_projection(self) -> None:
        self.assertIs(admit_bridge(ANCHOR_PROJECTION).outcome, OutcomeClass.AFFIRMATIVE)

    def test_the_arithmetic_is_the_shipped_arithmetic(self) -> None:
        self.assertEqual(PROJECTED_BITS, 216)
        self.assertEqual(SOURCE_BITS - PROJECTED_BITS, DISCARDED_BITS)
        self.assertEqual(DISCARDED_BITS, 40)

    def test_a_projection_collision_is_constructible_in_constant_time(self) -> None:
        """The projection cannot be the source of hardness."""

        left, right = projection_collision()
        self.assertNotEqual(left, right)
        self.assertEqual(project216(left), project216(right))

    def test_pricing_refuses_without_a_preimage_rule(self) -> None:
        result = price_projection(ANCHOR_PROJECTION, anchor_count=1, preimage_rule=None)
        self.assertIs(result.outcome, OutcomeClass.CANNOT_ANSWER)
        self.assertEqual(result.evidence["required_assumption"], PREIMAGE_PREMISE)
        self.assertEqual(result.evidence["truncated_bits"], 40)

    def test_pricing_succeeds_once_a_preimage_rule_exists(self) -> None:
        result = price_projection(
            ANCHOR_PROJECTION, anchor_count=3, preimage_rule="anchors-are-sealed-digests"
        )
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.evidence["anchor_count"], 3)

    def test_the_addend_vanishes_when_no_anchor_enters(self) -> None:
        result = price_projection(ANCHOR_PROJECTION, anchor_count=0, preimage_rule=None)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)

    def test_only_a_projection_carries_a_priced_loss(self) -> None:
        result = price_projection(_embedding(), anchor_count=1, preimage_rule=None)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "P04-010")


class RoundTripTest(unittest.TestCase):
    def test_a_bijection_round_trips_in_both_directions(self) -> None:
        domain = tuple(range(16))
        self.assertTrue(round_trip(lambda v: v + 100, lambda v: v - 100, domain))

    def test_a_lossy_map_fails_the_round_trip(self) -> None:
        domain = tuple(range(16))
        self.assertFalse(round_trip(lambda v: v // 2, lambda v: v * 2, domain))


if __name__ == "__main__":
    unittest.main()
