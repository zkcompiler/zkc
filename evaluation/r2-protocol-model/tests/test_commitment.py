"""The commitment subject: one positive inhabitant and five named mutations.

Four mutations must fail at named boundaries.  The fifth must **pass**, because
a prover who commits to fewer elements than it holds answers every query in the
declared range honestly.  A design that claimed to catch it would be lying, so
the test asserts the affirmative outcome *and* that the result names the
hypothesis it rests on.
"""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from r2model.commitment import (  # noqa: E402
    BINDING_ASSUMPTION,
    CommitmentConstruction,
    CommitmentError,
    CommittedValueProfile,
    Opening,
    authentication_path,
    commitment_root,
    construction_table_id,
    resolve_construction,
    verify_opening,
)
from r2model.terms import CheckResult, OutcomeClass  # noqa: E402


ROUTE = "r2.commit.binary-merkle.v1"
OCCURRENCE = "statement:f_root"


def _small_construction(arity_log2: int = 3) -> CommitmentConstruction:
    return CommitmentConstruction(
        name=ROUTE,
        element_sort="rs",
        arity_log2=arity_log2,
        query_sort="query_index",
        domain_separation="leaf-and-node-tagged",
        binding_game="r2.game.merkle-collision",
    )


def _profile(construction: CommitmentConstruction) -> CommittedValueProfile:
    return CommittedValueProfile(
        name="r2.profile.fri-input-layer",
        construction=construction.name,
        origin="prover_message",
        arity_log2=construction.arity_log2,
        element_sort=construction.element_sort,
        opens_at=(OCCURRENCE,),
    )


def _leaves(construction: CommitmentConstruction, prefix: str = "e") -> tuple[str, ...]:
    return tuple(f"{prefix}{index}" for index in range(construction.cardinality))


class CommitmentSubjectTest(unittest.TestCase):
    def setUp(self) -> None:
        self.construction = _small_construction()
        self.profile = _profile(self.construction)
        self.leaves = _leaves(self.construction)
        self.root = commitment_root(self.construction, self.leaves)

    def _opening(self, query: int) -> Opening:
        return Opening(
            commitment_occurrence=OCCURRENCE,
            query=query,
            answer=self.leaves[query],
            auth_path=authentication_path(self.construction, self.leaves, query),
        )

    # -- positive inhabitant -------------------------------------------------

    def test_an_honest_opening_authenticates_and_names_its_hypothesis(self) -> None:
        for query in range(self.construction.cardinality):
            result = verify_opening(
                self.construction, self.profile, self.root, self._opening(query)
            )
            self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE, msg=f"query {query}")
            self.assertEqual(result.boundary, "commitment:opening")
            self.assertEqual(result.evidence["required_assumption"], BINDING_ASSUMPTION)

    def test_authentication_length_is_the_declared_depth(self) -> None:
        self.assertEqual(self.construction.auth_depth, self.construction.arity_log2)
        self.assertEqual(
            len(self._opening(0).auth_path), self.construction.arity_log2
        )

    # -- mutations that must fail -------------------------------------------

    def test_opening_against_a_different_commitment_fails(self) -> None:
        opening = Opening(
            commitment_occurrence="message:other_root",
            query=0,
            answer=self.leaves[0],
            auth_path=authentication_path(self.construction, self.leaves, 0),
        )
        result = verify_opening(self.construction, self.profile, self.root, opening)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-001")

    def test_query_outside_the_declared_arity_fails(self) -> None:
        opening = Opening(
            commitment_occurrence=OCCURRENCE,
            query=self.construction.cardinality,
            answer=self.leaves[0],
            auth_path=authentication_path(self.construction, self.leaves, 0),
        )
        result = verify_opening(self.construction, self.profile, self.root, opening)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-002")

    def test_authentication_length_other_than_the_declared_depth_fails(self) -> None:
        base = self._opening(0)
        short = Opening(
            commitment_occurrence=base.commitment_occurrence,
            query=base.query,
            answer=base.answer,
            auth_path=base.auth_path[:-1],
        )
        result = verify_opening(self.construction, self.profile, self.root, short)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-003")

    def test_an_internal_node_presented_as_a_leaf_fails(self) -> None:
        base = self._opening(0)
        posed = Opening(
            commitment_occurrence=base.commitment_occurrence,
            query=base.query,
            answer=base.answer,
            auth_path=base.auth_path,
            leaf_tagged=False,
        )
        result = verify_opening(self.construction, self.profile, self.root, posed)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-005")

    def test_a_forged_answer_does_not_reconstruct_the_commitment(self) -> None:
        base = self._opening(0)
        forged = Opening(
            commitment_occurrence=base.commitment_occurrence,
            query=base.query,
            answer="forged",
            auth_path=base.auth_path,
        )
        result = verify_opening(self.construction, self.profile, self.root, forged)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-006")

    # -- the mutation that must PASS ----------------------------------------

    def test_understatement_is_indistinguishable_from_honesty(self) -> None:
        """The case the design must not claim to detect.

        Invisibility is a claim about two worlds, so the test builds both: an
        honest prover holding exactly what it committed, and a prover holding
        twice that and committing to half.  Every opening either can produce is
        answered honestly inside the declared range, and the checker's
        judgments are **identical** across the two worlds.

        Asserting only that the dishonest world verifies would be vacuous — it
        is the same computation as the honest one.  What carries the claim is
        that the two are indistinguishable here, and that the affirmative
        result names the assumption its arity rests on.
        """

        cardinality = self.construction.cardinality
        honest = tuple(f"e{index}" for index in range(cardinality))
        held = tuple(f"e{index}" for index in range(2 * cardinality))
        understated = held[:cardinality]

        self.assertEqual(len(held), 2 * len(understated))
        self.assertEqual(honest, understated)

        honest_terms, understated_terms = [], []
        for query in range(cardinality):
            for leaves, sink in ((honest, honest_terms), (understated, understated_terms)):
                root = commitment_root(self.construction, leaves)
                opening = Opening(
                    commitment_occurrence=OCCURRENCE,
                    query=query,
                    answer=leaves[query],
                    auth_path=authentication_path(self.construction, leaves, query),
                )
                result = verify_opening(self.construction, self.profile, root, opening)
                self.assertIs(
                    result.outcome,
                    OutcomeClass.AFFIRMATIVE,
                    msg="understatement must not be reported as a detected defect",
                )
                self.assertEqual(
                    result.evidence["required_assumption"], BINDING_ASSUMPTION
                )
                sink.append(result.to_term())

        self.assertEqual(
            honest_terms,
            understated_terms,
            msg=(
                "the checker must not distinguish a prover holding exactly what "
                "it committed from one holding twice that"
            ),
        )

    def test_overstatement_is_caught_where_understatement_is_not(self) -> None:
        """The asymmetry that makes the assumption the honest form.

        A prover declaring a wider arity than it realized cannot answer a query
        in the declared-but-unrealized range: the authentication it would need
        does not exist.  That is what a length-indexed opening buys, and it is
        the direction that does not shrink a bound.
        """

        narrow = _small_construction(arity_log2=self.construction.arity_log2 - 1)
        realized = _leaves(narrow)
        root = commitment_root(narrow, realized)

        with self.assertRaises(CommitmentError):
            authentication_path(self.construction, realized, narrow.cardinality)

        fabricated = Opening(
            commitment_occurrence=OCCURRENCE,
            query=narrow.cardinality,
            answer="fabricated",
            auth_path=tuple("00" * 32 for _ in range(self.construction.auth_depth)),
        )
        result = verify_opening(self.construction, self.profile, root, fabricated)
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-006")

    # -- binding-route resolution -------------------------------------------

    def test_an_unresolved_binding_route_is_a_missing_dependency(self) -> None:
        result = resolve_construction("zkc.commit.toy-vector")
        self.assertIsInstance(result, CheckResult)
        assert isinstance(result, CheckResult)
        self.assertIs(result.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(result.boundary, "commitment:binding-route")

    def test_an_admitted_binding_route_resolves(self) -> None:
        resolved = resolve_construction(ROUTE)
        self.assertIsInstance(resolved, CommitmentConstruction)

    def test_a_profile_naming_another_construction_is_a_missing_dependency(self) -> None:
        other = CommitmentConstruction(
            name="r2.commit.other.v1",
            element_sort="rs",
            arity_log2=self.construction.arity_log2,
            query_sort="query_index",
            domain_separation="leaf-and-node-tagged",
            binding_game="r2.game.merkle-collision",
        )
        result = verify_opening(other, self.profile, self.root, self._opening(0))
        self.assertIs(result.outcome, OutcomeClass.MISSING_DEPENDENCY)
        self.assertEqual(result.code, "R2-CMT-000")

    def test_a_profile_disagreeing_with_its_construction_arity_fails(self) -> None:
        wide = _small_construction(arity_log2=self.construction.arity_log2 + 1)
        skewed = CommittedValueProfile(
            name=self.profile.name,
            construction=wide.name,
            origin=self.profile.origin,
            arity_log2=self.construction.arity_log2,
            element_sort=self.profile.element_sort,
            opens_at=self.profile.opens_at,
        )
        result = verify_opening(wide, skewed, self.root, self._opening(0))
        self.assertIs(result.outcome, OutcomeClass.MISMATCH)
        self.assertEqual(result.code, "R2-CMT-004")

    # -- formation and identity ---------------------------------------------

    def test_a_profile_must_declare_where_it_opens(self) -> None:
        with self.assertRaises(CommitmentError):
            CommittedValueProfile(
                name="p", construction=ROUTE, origin="prover_message",
                arity_log2=3, element_sort="rs", opens_at=(),
            )

    def test_a_commitment_covers_exactly_its_declared_cardinality(self) -> None:
        with self.assertRaises(CommitmentError):
            commitment_root(self.construction, self.leaves[:-1])

    def test_identities_are_deterministic_and_separated(self) -> None:
        self.assertEqual(self.construction.identity, _small_construction().identity)
        self.assertNotEqual(self.construction.identity, self.profile.identity)
        self.assertTrue(construction_table_id().startswith("sha256:"))


if __name__ == "__main__":
    unittest.main()
