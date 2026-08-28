"""Tests for salted antipodal-pair commitments and typed verification."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.commitment import (  # noqa: E402
    ANTIPODAL_LEAF_HASH_LAW,
    EXACT_COMMITMENT_LAWS,
    EXACT_COMMITMENT_PROFILE,
    LEAF_HASH_DOMAIN,
    MERKLE_NODE_HASH_LAW,
    MERKLE_TREE_CAP_PATH_LAW,
    MerkleCap,
    NODE_HASH_DOMAIN,
    PairOpening,
    build_commitment,
    verify_pair_opening,
)
from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.profile import (  # noqa: E402
    D0,
    D1,
    D2,
    EXACT_ALGEBRA_PROFILE,
    EvaluationDomain,
)
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


class CommitmentProfileIdentityTest(unittest.TestCase):
    def test_exact_profile_binds_algebra_and_exact_versioned_laws(self) -> None:
        self.assertEqual(
            EXACT_COMMITMENT_PROFILE.algebra_profile_id,
            EXACT_ALGEBRA_PROFILE.identity,
        )
        self.assertEqual(
            EXACT_COMMITMENT_PROFILE.semantic_laws,
            EXACT_COMMITMENT_LAWS,
        )
        self.assertEqual(
            tuple(law.name for law in EXACT_COMMITMENT_PROFILE.semantic_laws),
            (
                "antipodal-pair-leaf-hash",
                "ordered-binary-merkle-node-hash",
                "binary-merkle-tree-cap-and-path",
            ),
        )
        self.assertEqual(
            EXACT_COMMITMENT_PROFILE.identity.subject_kind,
            "fri-commitment-profile",
        )
        self.assertEqual(
            EXACT_COMMITMENT_PROFILE.identity.domain,
            "fri-ior.commitment-profile.v1",
        )
        term = EXACT_COMMITMENT_PROFILE.to_term()
        self.assertEqual(
            term["semantic_law_ids"],
            [law.identity.to_term() for law in EXACT_COMMITMENT_LAWS],
        )
        self.assertNotIn("clauses", term)
        self.assertNotIn("source", term)
        self.assertNotIn("implementation", term)

    def test_domain_separators_match_commitment_law_descriptors(self) -> None:
        leaf_parameters = dict(ANTIPODAL_LEAF_HASH_LAW.parameters)
        node_parameters = dict(MERKLE_NODE_HASH_LAW.parameters)
        self.assertEqual(
            bytes.fromhex(str(leaf_parameters["domain-separator-hex"])),
            LEAF_HASH_DOMAIN,
        )
        self.assertEqual(
            bytes.fromhex(str(node_parameters["domain-separator-hex"])),
            NODE_HASH_DOMAIN,
        )
        self.assertIn(
            "opening-accepts-exactly-when-final-digest-equals-cap-at-running-index",
            MERKLE_TREE_CAP_PATH_LAW.clauses,
        )

    def test_commitment_law_change_rotates_only_commitment_profile(self) -> None:
        algebra_id = EXACT_ALGEBRA_PROFILE.identity
        changed_leaf = replace(
            ANTIPODAL_LEAF_HASH_LAW,
            clauses=ANTIPODAL_LEAF_HASH_LAW.clauses
            + ("hypothetical-additional-commitment-clause",),
        )
        changed_profile = replace(
            EXACT_COMMITMENT_PROFILE,
            semantic_laws=(changed_leaf,) + EXACT_COMMITMENT_LAWS[1:],
        )
        self.assertNotEqual(changed_leaf.identity, ANTIPODAL_LEAF_HASH_LAW.identity)
        self.assertNotEqual(
            changed_profile.identity,
            EXACT_COMMITMENT_PROFILE.identity,
        )
        self.assertEqual(changed_profile.algebra_profile_id, algebra_id)
        self.assertEqual(EXACT_ALGEBRA_PROFILE.identity, algebra_id)

    def test_commitment_profile_formation_fails_closed(self) -> None:
        cases = (
            ({"name": "Bad Name"}, "FRI-IOR-COMMITMENT-026"),
            (
                {
                    "algebra_profile_id": replace(
                        EXACT_ALGEBRA_PROFILE.identity,
                        subject_kind="merkle-cap",
                    )
                },
                "FRI-IOR-COMMITMENT-027",
            ),
            ({"hash_name": ""}, "FRI-IOR-COMMITMENT-028"),
            ({"salt_bytes": 0}, "FRI-IOR-COMMITMENT-029"),
            ({"cap_size": 3}, "FRI-IOR-COMMITMENT-029"),
            ({"cap_size": 4}, "FRI-IOR-COMMITMENT-030"),
            ({"semantic_laws": ()}, "FRI-IOR-COMMITMENT-031"),
            (
                {"semantic_laws": tuple(reversed(EXACT_COMMITMENT_LAWS))},
                "FRI-IOR-COMMITMENT-031",
            ),
            ({"hash_name": "sha512"}, "FRI-IOR-COMMITMENT-032"),
            ({"digest_bytes": 31}, "FRI-IOR-COMMITMENT-032"),
            ({"salt_bytes": 17}, "FRI-IOR-COMMITMENT-032"),
            ({"cap_size": 1}, "FRI-IOR-COMMITMENT-032"),
        )
        for changes, code in cases:
            with self.subTest(changes=changes), self.assertRaises(ModelFailure) as raised:
                replace(EXACT_COMMITMENT_PROFILE, **changes)
            self.assertEqual(raised.exception.code, code)


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

    def test_caps_and_openings_bind_the_commitment_profile_identity(self) -> None:
        tree = build_commitment(D0, _evaluations(D0), _salts(D0))
        expected = EXACT_COMMITMENT_PROFILE.identity.to_term()
        self.assertEqual(tree.cap.to_term()["commitment_profile_id"], expected)
        self.assertEqual(
            tree.open_pair(0).to_term()["commitment_profile_id"],
            expected,
        )

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
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
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
                transcript_frames=0,
                sampler_attempts=0,
                grinding_trials=0,
                logical_query_occurrences=0,
                unique_openings=0,
                proof_bytes=0,
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
        counter = ResourceCounter(
            ResourceLimits(
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
        )
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
