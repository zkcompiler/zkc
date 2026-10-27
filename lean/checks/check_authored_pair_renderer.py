#!/usr/bin/env python3
"""Focused shape and fixed-selection controls for the compiled-pair reader."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from bridges.construction import pair  # noqa: E402
from bridges.common import lean_render  # noqa: E402


def fixture():
    digest = "sha256:" + "0" * 64
    policy = ["zkc.native-proof-policy/0", "main", "P", "V", "0", "suite",
              ["1"], ["0"], [["query", "delivery"]], "zkc.framed/0", ""]
    child = ["zkc.constructed-participant/0", digest, digest, policy, "producer",
             ["i1", "!runtime.capability<\"transcript:suite\">"],
             ["!runtime.capability<\"transcript:suite\">"], [], [1], []]
    validator = deepcopy(child)
    validator[4] = "validator"
    return [pair.FORMAT, child, validator]


class PairReader(unittest.TestCase):
    def test_transcript_type_has_one_runtime_owner(self):
        self.assertEqual(pair.participant.sort('!runtime.capability<"transcript:suite">')[1],
                         ("transcript", "suite"))
        for spelling in ['!local.capability<"transcript:suite">',
                         '!runtime.capability<"rng:suite">',
                         '!runtime.capability<"transcript:suite"> trailing']:
            with self.subTest(spelling=spelling), self.assertRaisesRegex(
                    ValueError, "unsupported constructed data type"):
                pair.participant.sort(spelling)

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

    def test_guard_has_one_protocol_owner(self):
        boolean = ("boolean", None)
        attrs = {"site": ("string", "stop"), "owner": ("string", "P")}
        self.assertEqual(pair.participant.operation(
            "protocol.guard", attrs, [], [boolean], []), '.guard "stop"')
        with self.assertRaisesRegex(ValueError, "guard owner"):
            pair.participant.operation("protocol.guard", {
                **attrs, "owner": ("string", "")}, [], [boolean], [])
        self.assertIn("unsupported", pair.participant.operation(
            "local.guard", {"site": ("string", "stop")}, [], [boolean], []))

    def test_fixed_selection_pins_body_not_labels(self):
        expected = fixture()
        data = deepcopy(expected)
        data[1][7] = [["protocol.guard", [["owner", ["string", "P"]],
                                             ["site", ["string", "stop"]]], [], [0], [], []]]
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

    def test_local_services_are_separate_and_exact(self):
        data = fixture()
        data[1][9] = [["service_1", "P", "2", "1", "random.bls12-381.fr/0"]]
        origin = lean_render.encode_tree([
            "zkc.native-origin-template/0", "main", [], [],
            ["query", "main", "nonce", "input_2", "random.bls12-381.fr/0", "draw", "P"]]).hex()
        data[1][7] = [["protocol.service_query", [["method", ["string", "draw"]],
                         ["port", ["string", "service_1"]], ["site", ["string", "nonce"]]],
                        [], [], ['!algebra.field<"bls12-381.fr">'], [], [origin, []]]]
        rendered = pair.render(data, "Services")
        self.assertIn("servicePorts :=", rendered)
        self.assertIn(".localService", rendered)
        self.assertNotIn(".challenge", rendered)
        for change in [lambda d: d[1].pop(), lambda d: d[1][7][0].pop(),
                       lambda d: d[1][7][0][1].append(["extra", ["string", "ignored"]]),
                       lambda d: d[1][7][0][1][1].__setitem__(1, ["string", "undeclared"]),
                       lambda d: d[1][7][0][2].append("binding"),
                       lambda d: d[1][7][0][5].append([]),
                       lambda d: d[1][7][0][6].append("ignored"),
                       lambda d: d[1][7][0][6][1].append(0),
                       lambda d: d[1][9][0].__setitem__(1, "unknown-owner"),
                       lambda d: d[1][9][0].__setitem__(3, "01"),
                       lambda d: d[1][9][0].__setitem__(4, "random.other/0")]:
            with self.subTest(change=change):
                changed = deepcopy(data)
                change(changed)
                with self.assertRaises(ValueError):
                    pair.decode(changed)


if __name__ == "__main__":
    unittest.main()
