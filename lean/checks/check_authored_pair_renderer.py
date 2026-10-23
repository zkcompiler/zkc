#!/usr/bin/env python3
"""Focused shape and fixed-selection controls for the compiled-pair reader."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from bridges.construction import pair  # noqa: E402


def fixture():
    digest = "sha256:" + "0" * 64
    policy = ["zkc.native-proof-policy/0", "main", "P", "V", "0", "suite",
              ["1"], ["0"], [], "zkc.framed/0", ""]
    child = ["zkc.constructed-participant/0", digest, digest, policy, "producer",
             ["i1", "!local.capability<\"transcript:suite\">"],
             ["!local.capability<\"transcript:suite\">"], [], [1]]
    validator = deepcopy(child)
    validator[4] = "validator"
    return [pair.FORMAT, child, validator]


class PairReader(unittest.TestCase):
    def test_exact_envelope(self):
        data = fixture()
        self.assertEqual(pair.decode(data, expected=deepcopy(data)), tuple(data[1:]))
        rendered = pair.render(data, "Tests.PairReader")
        self.assertIn("def artifacts", rendered)
        self.assertIn("Tests.PairReader.Producer", rendered)

    def test_pair_mutations_refuse(self):
        for index, value in [(1, "sha256:" + "1" * 64),
                             (2, "sha256:" + "2" * 64), (4, "producer")]:
            with self.subTest(index=index):
                data = fixture()
                data[2][index] = value
                with self.assertRaises(ValueError):
                    pair.decode(data)
        data = fixture()
        data[2][3][7] = []
        with self.assertRaisesRegex(ValueError, "policy mismatch"):
            pair.decode(data)

    def test_fixed_selection_pins_body_not_labels(self):
        expected = fixture()
        data = deepcopy(expected)
        data[1][7] = [["local.guard", [["site", ["string", "stop"]]], [], [0], [], []]]
        pair.decode(data)  # Structurally readable; admission must pin the body.
        with self.assertRaisesRegex(ValueError, "fixed selection"):
            pair.decode(data, expected=expected)
        with self.assertRaisesRegex(ValueError, "fixed selection"):
            pair.decode([data[0], data[2], data[1]], expected=expected)

    def test_versions_roles_and_shapes_refuse(self):
        for mutate in [lambda d: d.append("extra"),
                       lambda d: d.__setitem__(0, "zkc.constructed-pair/1"),
                       lambda d: d[1].__setitem__(1, "sha256:bad"),
                       lambda d: d[1][3].__setitem__(2, "V"),
                       lambda d: d[1].__setitem__(8, [999]),
                       lambda d: d[1][3].append("extra")]:
            data = fixture()
            mutate(data)
            with self.assertRaises(ValueError):
                pair.decode(data)

    def test_existing_calculations_are_exact(self):
        b, i = ("boolean", None), ("index", None)
        cases = [("data.index", {"value": ("string", "0")}, [], [i], ".indexConstant 0"),
                 ("data.index_equal", {}, [i, i], [b], ".indexEqual"),
                 ("arith.constant", {"value": ("bool", True)}, [], [b], ".booleanConstant true"),
                 ("arith.cmpi", {"predicate": ("integer", "0")}, [b, b], [b], ".booleanEqual"),
                 ("arith.cmpi", {"predicate": ("integer", "1")}, [b, b], [b], ".booleanNotEqual")]
        for name, attrs, operands, results, term in cases:
            with self.subTest(name=name, term=term):
                self.assertIn(term, pair.participant.operation(name, attrs, [], operands, results))
                with self.assertRaises(ValueError):
                    pair.participant.operation(name, attrs, [], operands, [i] if results == [b] else [b])
        with self.assertRaises(ValueError):
            pair.participant.operation("arith.cmpi", {"predicate": ("integer", "2")}, [], [b, b], [b])


if __name__ == "__main__":
    unittest.main()
