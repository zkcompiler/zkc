"""Build-free controls for the finite installed deterministic-data vocabulary."""

import copy
import unittest

from generate import validate
from tablegen import project
from test_profiles import source


# Independent finite coverage witness. A new name never enrolls by prefix.
COVERAGE = {
    "scalars": """
        index.constant index.add index.sub index.mul index.div index.mod
        index.equal index.less index.wrapping_add index.wrapping_sub
        index.bit_and index.logical_shift_right bool.and bool.not bool.or
        field.from_index field.sub field.neg field.inverse field.embed
        field.constant field.add field.mul field.equal control.require
        bool.select index.select field.select curve.select
    """,
    "containers": """
        sequence.empty sequence.append sequence.at sequence.length
        indices.empty indices.append indices.at indices.length
        field_array.at field_array.from_vector field_array.get
        fixed_vector.dot fixed_vector.from_vector fixed_vector.to_vector
        commitments.empty commitments.append commitments.at commitments.length
    """,
    "vectors": """
        vector.find_last vector.transpose vector.get vector.slice vector.length
        vector.rotate vector.interleave vector.prefix_product vector.prefix_sum
        vector.inverse vector.embed vector.fill vector.geometric vector.constant
        vector.scatter_sum vector.empty vector.append vector.splat vector.powers
        vector.add vector.sub vector.mul vector.dot vector.concat vector.kronecker
        vector.matvec vector.scale vector.sum vector.split vector.at
        vector.length_check vector.gather vector.from_point vector.from_table
        vector.to_point vector.to_table vector.equal vector.product
        vector.bit_reverse vector.bit_reverse_rows
    """,
    "polynomials": """
        multilinear.restrict_prefix poly.coset_evaluate_at
        poly.coset_evaluate_batch poly.coset_extend poly.opening_quotient_sum
        poly.table_arity poly.coefficient_count poly.coset_evaluate
        poly.coset_interpolate poly.domain_point poly.domain_root
        poly.domain_points poly.even_odd_fold poly.divide_opening
        poly.opening_quotient poly.equality_weights poly.from_coefficients
        poly.coefficients poly.degree_check poly.univariate_evaluate
        poly.univariate_boundary poly.product_sum poly.product_round
        poly.boundary poly.round_evaluate poly.fold poly.evaluate
        poly.empty_point poly.append_point
    """,
    "bytes and codecs": """
        bytes.append bytes.concat bytes.slice bytes.at bytes.length bytes.equal
        bytes.repeat bytes.join bytes.empty encoding.field_be
        encoding.field_from_be encoding.field_reduce_be encoding.group_compressed
        encoding.group_from_compressed encoding.field_le encoding.field_from_le
        encoding.field_reduce_le encoding.group_decode_cofactor
        encoding.cryptonote_map encoding.fields_be encoding.fields_le
        encoding.groups_compressed encoding.index_uleb128 encoding.fields_from_be
        encoding.fields_from_le encoding.field_montgomery_le
        encoding.field_from_montgomery_le encoding.fields_montgomery_le
        encoding.fields_from_montgomery_le
    """,
    "hashes": """
        hash.keccak256 hash.sha256 hash.poseidon2_16
        shake128.init shake128.absorb shake128.squeeze
    """,
    "verification": "oracle.check oracle.check_many",
}


def selected(value, kind):
    return {
        op["name"]
        for op in value["operations"]
        if {"kind": kind} in op["facets"]
    }


class DeterministicData(unittest.TestCase):
    def test_exact_finite_coverage(self):
        value = source()
        validate(value)
        expected = [name for rows in COVERAGE.values() for name in rows.split()]
        self.assertEqual(len(expected), len(set(expected)))
        self.assertEqual(selected(value, "DeterministicData"), set(expected))

    def test_nullary_closed_facet_and_duplicates(self):
        for facet in (
            {"kind": "DeterministicData", "total": True},
            {"kind": "DeterministicData", "stateInput": 0},
            {"kind": "UnknownDeterministicData"},
            {"kind": "deterministicData"},
        ):
            with self.subTest(facet=facet):
                value = source()
                value["operations"][0]["facets"] = [facet]
                with self.assertRaises(ValueError):
                    validate(value)
        value = source()
        value["operations"][0]["facets"] = [{"kind": "DeterministicData"}] * 2
        with self.assertRaisesRegex(ValueError, "duplicate semantic facet"):
            validate(value)

    def test_unknown_operations_never_enroll(self):
        value = source()
        enrolled = selected(value, "DeterministicData")
        for name in ("index.future", "vector.future", "oracle.future", "unknown"):
            operation = copy.deepcopy(value["operations"][0])
            operation.update(name=name, facets=[])
            value["operations"].append(operation)
        validate(value)
        self.assertEqual(selected(value, "DeterministicData"), enrolled)
        self.assertEqual(project(value)[0].count("DeterministicData"), len(enrolled))

    def test_public_replay_remains_total_restricted_vocabulary(self):
        value = source()
        replay = selected(value, "PublicReplay")
        # Deliberately partial checks and opaque snapshots do not acquire replay.
        self.assertFalse(replay & {
            "index.div", "index.sub", "field.inverse", "sequence.at",
            "vector.get", "bytes.at", "poly.domain_point", "control.require",
            "oracle.check", "oracle.check_many", "shake128.squeeze",
        })
        without = copy.deepcopy(value)
        for op in without["operations"]:
            op["facets"] = [f for f in op["facets"] if f["kind"] != "DeterministicData"]
        self.assertEqual(selected(without, "PublicReplay"), replay)
        validate(without)


if __name__ == "__main__":
    unittest.main()
