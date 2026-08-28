"""Tests for salted antipodal-pair commitments and typed verification."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.commitment import (  # noqa: E402
    MerkleCap,
    PairOpening,
    build_commitment,
    verify_pair_opening,
)
from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.profile import D0, D1, D2, EvaluationDomain  # noqa: E402
from friiormodel.terms import (  # noqa: E402
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
)


def _evaluations(domain: EvaluationDomain) -> tuple[Fp2, ...]:
    return tuple(
        Fp2(Fp.reduce(7 + 3 * index + index * index), Fp.reduce(11 + 5 * index))
        for index in range(domain.order)
    )


def _salts(domain: EvaluationDomain) -> tuple[bytes, ...]:
    return tuple(index.to_bytes(16, "big") for index in range(domain.order // 2))


class CommitmentConstructionTest(unittest.TestCase):
    def test_all_supported_domains_build_two_node_caps(self) -> None:
        expected_hash_calls = {"D0": 14, "D1": 6, "D2": 2}
        expected_depths = {"D0": 2, "D1": 1, "D2": 0}
        for domain in (D0, D1, D2):
            with self.subTest(domain=domain.name):
                counter = ResourceCounter()
                tree = build_commitment(
                    domain, _evaluations(domain), _salts(domain), counter
                )
                self.assertEqual(len(tree.cap.nodes), 2)
                self.assertEqual(tree.authentication_depth, expected_depths[domain.name])
                self.assertEqual(counter.hash_calls, expected_hash_calls[domain.name])
                self.assertEqual(counter.merkle_nodes, expected_hash_calls[domain.name])

    def test_openings_carry_the_declared_antipodal_pair_order(self) -> None:
        values = _evaluations(D0)
        tree = build_commitment(D0, values, _salts(D0))
        for pair_index in range(D0.order // 2):
            opening = tree.open_pair(pair_index)
            self.assertEqual(opening.positive, values[pair_index])
            self.assertEqual(opening.negative, values[pair_index + D0.order // 2])
            self.assertEqual(len(opening.authentication_path), 2)

    def test_every_pair_opening_authenticates(self) -> None:
        tree = build_commitment(D0, _evaluations(D0), _salts(D0))
        for pair_index in range(tree.pair_count):
            with self.subTest(pair_index=pair_index):
                result = verify_pair_opening(
                    D0, tree.cap, tree.open_pair(pair_index)
                )
                self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
                self.assertEqual(result.code, "FRI-IOR-COMMITMENT-100")
                self.assertEqual(result.evidence["pair_index"], pair_index)

    def test_salt_is_committed(self) -> None:
        values = _evaluations(D0)
        first = build_commitment(D0, values, _salts(D0)).cap
        changed_salts = list(_salts(D0))
        changed_salts[0] = b"changed-salt-000"
        self.assertEqual(len(changed_salts[0]), 16)
        second = build_commitment(D0, values, tuple(changed_salts)).cap
        self.assertNotEqual(first, second)

    def test_value_order_inside_a_pair_is_committed(self) -> None:
        values = list(_evaluations(D0))
        first = build_commitment(D0, tuple(values), _salts(D0)).cap
        values[0], values[D0.order // 2] = values[D0.order // 2], values[0]
        second = build_commitment(D0, tuple(values), _salts(D0)).cap
        self.assertNotEqual(first, second)

    def test_commitment_input_shape_is_malformed(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            build_commitment(D0, _evaluations(D0)[:-1], _salts(D0))
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-COMMITMENT-014")

    def test_salt_width_is_malformed(self) -> None:
        salts = list(_salts(D0))
        salts[0] = b"too-short"
        with self.assertRaises(ModelFailure) as raised:
            build_commitment(D0, _evaluations(D0), tuple(salts))
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-COMMITMENT-017")

    def test_well_formed_but_unsupported_domain_is_unsupported(self) -> None:
        alternate = EvaluationDomain("alternate", Fp(89), 16)
        with self.assertRaises(ModelFailure) as raised:
            build_commitment(alternate, _evaluations(D0), _salts(D0))
        self.assertIs(raised.exception.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(raised.exception.code, "FRI-IOR-COMMITMENT-003")

    def test_build_respects_hash_resource_limit(self) -> None:
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=0,
                hash_calls=13,
                hash_bytes=1 << 15,
                merkle_nodes=14,
            )
        )
        with self.assertRaises(ModelFailure) as raised:
            build_commitment(D0, _evaluations(D0), _salts(D0), counter)
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(raised.exception.code, "FRI-IOR-RESOURCE-008")
        self.assertEqual(counter.hash_calls, 13)
        self.assertEqual(counter.merkle_nodes, 13)

    def test_merkle_node_limit_failure_is_an_atomic_composite_charge(self) -> None:
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=0,
                hash_calls=1,
                hash_bytes=256,
                merkle_nodes=0,
            )
        )
        with self.assertRaises(ModelFailure) as raised:
            build_commitment(D2, _evaluations(D2), _salts(D2), counter)
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(counter.hash_calls, 0)
        self.assertEqual(counter.hash_bytes, 0)
        self.assertEqual(counter.merkle_nodes, 0)


class CommitmentVerificationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tree = build_commitment(D0, _evaluations(D0), _salts(D0))
        self.opening = self.tree.open_pair(3)

    def test_wrong_value_is_refused(self) -> None:
        changed = replace(self.opening, positive=Fp2(Fp(1), Fp(2)))
        result = verify_pair_opening(D0, self.tree.cap, changed)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-025")

    def test_wrong_salt_is_refused(self) -> None:
        changed = replace(self.opening, salt=b"different-salt!!")
        self.assertEqual(len(changed.salt), 16)
        result = verify_pair_opening(D0, self.tree.cap, changed)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-025")

    def test_wrong_authentication_sibling_is_refused(self) -> None:
        path = list(self.opening.authentication_path)
        path[0] = bytes((path[0][0] ^ 1,)) + path[0][1:]
        changed = replace(self.opening, authentication_path=tuple(path))
        result = verify_pair_opening(D0, self.tree.cap, changed)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-025")

    def test_wrong_cap_is_refused(self) -> None:
        nodes = list(self.tree.cap.nodes)
        nodes[0] = bytes((nodes[0][0] ^ 1,)) + nodes[0][1:]
        result = verify_pair_opening(D0, MerkleCap(tuple(nodes)), self.opening)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-025")

    def test_wrong_domain_name_is_refused_before_hashing(self) -> None:
        changed = replace(self.opening, domain_name="D1")
        counter = ResourceCounter()
        result = verify_pair_opening(D0, self.tree.cap, changed, counter)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-021")
        self.assertEqual(counter.hash_calls, 0)

    def test_out_of_range_pair_index_is_refused(self) -> None:
        changed = replace(self.opening, pair_index=D0.order // 2)
        result = verify_pair_opening(D0, self.tree.cap, changed)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-022")

    def test_short_authentication_path_is_refused(self) -> None:
        changed = replace(
            self.opening,
            authentication_path=self.opening.authentication_path[:-1],
        )
        result = verify_pair_opening(D0, self.tree.cap, changed)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-023")

    def test_non_opening_value_is_malformed(self) -> None:
        result = verify_pair_opening(D0, self.tree.cap, {"pair_index": 3})
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-COMMITMENT-020")

    def test_verification_limit_exhaustion_is_not_a_refusal(self) -> None:
        counter = ResourceCounter(ResourceLimits(0, 0, 0, 0))
        result = verify_pair_opening(D0, self.tree.cap, self.opening, counter)
        self.assertIs(result.outcome, OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED)
        self.assertEqual(result.code, "FRI-IOR-RESOURCE-008")

    def test_unexpected_checker_fault_is_not_a_protocol_refusal(self) -> None:
        with patch(
            "friiormodel.commitment._hash_leaf",
            side_effect=RuntimeError("fault injection"),
        ):
            result = verify_pair_opening(D0, self.tree.cap, self.opening)
        self.assertIs(result.outcome, OutcomeClass.CHECKER_FAILURE)
        self.assertEqual(result.code, "FRI-IOR-CHECKER-001")

    def test_opening_formation_rejects_bad_salt_width_as_malformed(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            PairOpening(
                domain_name=self.opening.domain_name,
                pair_index=self.opening.pair_index,
                positive=self.opening.positive,
                negative=self.opening.negative,
                salt=b"short",
                authentication_path=self.opening.authentication_path,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-COMMITMENT-008")


if __name__ == "__main__":
    unittest.main()
