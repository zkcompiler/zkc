"""Does an opening need a new action kind?

The design claim is that it does not: an opening is a prover message carrying
an ``Opening`` value plus a verifier check that consumes it.  These tests
exercise that claim against the FRI witness's shape law, ported unchanged.

The claim is falsified if the core cannot admit without relaxing a ported rule,
or if the commitment and an element of its content class turn out to be
interchangeable.
"""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from commitment_model.commitment import (  # noqa: E402
    BINDING_ASSUMPTION,
    CommitmentConstruction,
    CONSTRUCTIONS,
)
from commitment_model.core import (  # noqa: E402
    CHECK,
    COMMITMENT,
    OPENING,
    QUERY,
    ActionKind,
    Mutation,
    ValueSort,
    admit_core,
    build_core,
    honest_leaves,
    mutate_core,
    run_opening,
)
from commitment_model.terms import OutcomeClass  # noqa: E402


def _construction(arity_log2: int = 3) -> CommitmentConstruction:
    base = CONSTRUCTIONS["r2.commit.binary-merkle.v1"]
    return CommitmentConstruction(
        name=base.name,
        element_sort=base.element_sort,
        arity_log2=arity_log2,
        query_sort=base.query_sort,
        domain_separation=base.domain_separation,
        binding_game=base.binding_game,
    )


class NoNewActionKindTest(unittest.TestCase):
    """The claim under test."""

    def setUp(self) -> None:
        self.construction = _construction()
        self.core = build_core(self.construction)
        self.leaves = honest_leaves(self.construction)

    def test_the_commitment_core_admits_under_the_ported_shape_law(self) -> None:
        result = admit_core(self.core)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE, msg=result.detail)
        self.assertEqual(result.boundary, "closed-core")

    def test_every_action_uses_an_existing_kind(self) -> None:
        inherited = {
            ActionKind.STATEMENT, ActionKind.CHALLENGE, ActionKind.MESSAGE,
            ActionKind.CHECK, ActionKind.ROUTE, ActionKind.RESIDUAL,
        }
        self.assertEqual({a.kind for a in self.core.actions} - inherited, set())

    def test_the_opening_is_a_message_and_its_consumer_is_a_check(self) -> None:
        by_occurrence = {a.occurrence: a for a in self.core.actions}
        self.assertIs(by_occurrence[OPENING].kind, ActionKind.MESSAGE)
        self.assertIs(by_occurrence[OPENING].value_sort, ValueSort.OPENING)
        self.assertIs(by_occurrence[CHECK].kind, ActionKind.CHECK)

    def test_the_query_challenge_binds_the_commitment(self) -> None:
        by_occurrence = {a.occurrence: a for a in self.core.actions}
        self.assertIn(COMMITMENT, by_occurrence[QUERY].required_influences)

    def test_the_query_domain_is_the_declared_arity(self) -> None:
        by_occurrence = {a.occurrence: a for a in self.core.actions}
        self.assertEqual(
            by_occurrence[QUERY].cardinality, self.construction.cardinality
        )


class OperandDisciplineTest(unittest.TestCase):
    """A commitment is not an element of the class its content is drawn from."""

    def setUp(self) -> None:
        self.construction = _construction()
        self.core = build_core(self.construction)

    def test_a_commitment_satisfies_no_operand_slot(self) -> None:
        published = next(a for a in self.core.actions if a.occurrence == COMMITMENT)
        self.assertIsNotNone(published.profile)
        self.assertIsNone(published.operand_sort)

    def test_an_unprofiled_value_does_satisfy_its_slot(self) -> None:
        published = next(a for a in self.core.actions if a.occurrence == OPENING)
        self.assertIsNone(published.profile)
        self.assertIs(published.operand_sort, ValueSort.OPENING)

    def test_stripping_the_profile_is_refused_at_publication(self) -> None:
        """Un-profiling the commitment is caught before any operand rule.

        The core then publishes no commitment at all, which R2-CMT-CORE-013
        refuses.  There is deliberately no separate operand check: a profiled
        value cannot reach an operand slot by construction, so a rule asserting
        it could never fail.
        """

        posed = mutate_core(self.core, Mutation.COMMITMENT_AS_CHECK_OPERAND)
        result = admit_core(posed)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-CORE-013")

    def test_an_opening_without_a_consumer_is_refused(self) -> None:
        orphan = mutate_core(self.core, Mutation.OPENING_WITHOUT_CHECK)
        result = admit_core(orphan)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-CORE-016")


class OpeningMutationTest(unittest.TestCase):
    """The five named mutations, run inside the core."""

    def setUp(self) -> None:
        self.construction = _construction()
        self.core = build_core(self.construction)
        self.leaves = honest_leaves(self.construction)

    def test_an_honest_opening_authenticates(self) -> None:
        for query in range(self.construction.cardinality):
            result = run_opening(self.core, self.leaves, query)
            self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
            self.assertEqual(
                result.evidence["required_assumption"], BINDING_ASSUMPTION
            )

    def test_named_mutations_fail_at_named_boundaries(self) -> None:
        expected = {
            Mutation.FOREIGN_COMMITMENT: ("R2-CMT-001", "commitment:opening"),
            Mutation.QUERY_OUT_OF_RANGE: ("R2-CMT-002", "commitment:opening"),
            Mutation.SHORT_AUTHENTICATION: ("R2-CMT-003", "commitment:opening"),
            Mutation.NODE_POSED_AS_LEAF: ("R2-CMT-005", "commitment:domain-separation"),
        }
        for mutation, (code, boundary) in expected.items():
            with self.subTest(mutation=mutation.value):
                result = run_opening(self.core, self.leaves, 0, mutation)
                self.assertIs(result.outcome, OutcomeClass.MISMATCH)
                self.assertEqual(result.code, code)
                self.assertEqual(result.boundary, boundary)

    def test_understatement_is_invisible_inside_the_core(self) -> None:
        """The fifth mutation: it must pass, and say what it rests on."""

        cardinality = self.construction.cardinality
        held = tuple(f"e{index}" for index in range(2 * cardinality))
        understated = held[:cardinality]

        honest_terms, understated_terms = [], []
        for query in range(cardinality):
            honest = run_opening(self.core, self.leaves, query)
            shaded = run_opening(self.core, understated, query)
            for result in (honest, shaded):
                self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
                self.assertEqual(
                    result.evidence["required_assumption"], BINDING_ASSUMPTION
                )
            honest_terms.append(honest.to_term())
            understated_terms.append(shaded.to_term())

        self.assertEqual(len(held), 2 * cardinality)
        self.assertEqual(
            honest_terms,
            understated_terms,
            msg="the core must not distinguish understatement from honesty",
        )


class IdentityTest(unittest.TestCase):
    def setUp(self) -> None:
        self.construction = _construction()

    def test_core_identity_is_deterministic(self) -> None:
        self.assertEqual(
            build_core(self.construction).identity,
            build_core(self.construction).identity,
        )

    def test_the_profile_enters_the_identity_term(self) -> None:
        core = build_core(self.construction)
        published = next(a for a in core.actions if a.occurrence == COMMITMENT)
        self.assertIn("profile", published.term())

    def test_an_unprofiled_action_omits_the_key_entirely(self) -> None:
        core = build_core(self.construction)
        opening = next(a for a in core.actions if a.occurrence == OPENING)
        self.assertNotIn(
            "profile",
            opening.term(),
            msg=(
                "an unprofiled action must encode as it did before the "
                "commitment subject existed"
            ),
        )

    def test_a_wider_construction_is_a_different_core(self) -> None:
        self.assertNotEqual(
            build_core(self.construction).identity,
            build_core(_construction(arity_log2=4)).identity,
        )


if __name__ == "__main__":
    unittest.main()
