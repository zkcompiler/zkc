#!/usr/bin/env python3
"""Strict-reader controls for recursive nominal construction data and profiles."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
from bridges.construction import render  # noqa: E402

FIELD = ["apply", "field", [["domain", "Field", "koala-bear"]]]
IDENTITY = ["tuple", [["atom", "example.Opening"], ["atom", "phantom.F"]]]
PRODUCT = ["variant", IDENTITY, [["opening", [FIELD, FIELD]]]]


def sequence(element):
    return ["apply", "sequence", [["type", element]]]


class PlainReader(unittest.TestCase):
    def test_recursive_nominal_data(self):
        term, kind = render.sort(sequence(PRODUCT))
        self.assertEqual(kind, ("data", ["sequence", ["product",
            '["example.Opening","phantom.F"]', "opening", [["field", "koala-bear"]] * 2]]))
        self.assertIn('.sequence (.product "[\\"example.Opening\\",\\"phantom.F\\"]" "opening"', term)

    def test_nominal_phantom_and_constructor_identity(self):
        baseline = render.sort(sequence(PRODUCT))
        mutations = [lambda p: p[1][1][0].__setitem__(1, "other.Opening"),
                     lambda p: p[1][1][1].__setitem__(1, "phantom.G"),
                     lambda p: p[1][1].reverse(),
                     lambda p: p[2][0].__setitem__(0, "other_constructor")]
        for mutate in mutations:
            changed = deepcopy(PRODUCT)
            mutate(changed)
            with self.subTest(product=changed):
                term, kind = render.sort(sequence(changed))
                self.assertNotEqual(term, baseline[0])
                self.assertNotEqual(kind, baseline[1])
        # Atoms containing JSON text cannot alias tuple identities.
        atom = ["variant", ["atom", '["example.Opening","phantom.F"]'], PRODUCT[2]]
        self.assertNotEqual(render.sort(sequence(atom)), baseline)

    def test_hidden_capabilities_refuse(self):
        handles = [["service", "random.koala-bear/0"],
                   ["oracle", "table", [["type", FIELD]]],
                   ["apply", "transcript", [["domain", "Transcript", "private"]]]]
        for handle in handles:
            hidden = ["variant", IDENTITY, [["opening", [FIELD, sequence(handle)]]]]
            with self.subTest(handle=handle), self.assertRaisesRegex(ValueError, "handle"):
                render.sort(sequence(hidden))

    def test_multiple_constructors_refuse(self):
        with self.assertRaisesRegex(ValueError, "multi-alternative"):
            render.sort(["variant", IDENTITY, [["left", []], ["right", []]]])

    def test_malformed_type_controls(self):
        malformed = [sequence(PRODUCT) + ["extra"],
                     ["apply", "sequence", [["nat", "1"]]],
                     ["variant", ["tuple", ["phantom.F"]], PRODUCT[2]],
                     ["variant", IDENTITY, [["opening", []], ["opening", []]]],
                     ["variant", IDENTITY, [["opening", [FIELD + ["extra"]]]]],
                     '!data.sequence<!data.variant<"retired">>',
                     '!local.variant<"retired">',
                     ["apply", "runtime.capability", []]]
        for value in malformed:
            with self.subTest(value=value), self.assertRaises(ValueError):
                render.sort(value)

    def test_plain_policy_refuses_challenge_replacement(self):
        plain = ["zkc.native-proof-policy/0", "entry", "P", "V", "0", "", [], ["0"], [], "zkc.framed/0", "", []]
        self.assertEqual(render.policy(plain),
                         '⟨"entry", "P", "V", 0, "", [], [0], [], "zkc.framed/0", ""⟩')
        with self.assertRaisesRegex(ValueError, "array of size 12"):
            render.policy(plain[:-1])
        for gates in [None, False, "", {}, [["query", "0"]], [["query", "1"]], [[]]]:
            with self.subTest(gates=gates), self.assertRaisesRegex(ValueError, "policy gates"):
                render.policy(plain[:-1] + [gates])
        for index, value in [(6, ["1"]), (8, [["query", "delivery"]])]:
            forged = deepcopy(plain)
            forged[index] = value
            with self.subTest(index=index), self.assertRaisesRegex(ValueError, "replacement"):
                render.policy(forged)
        fake = [render.FORMAT, "sha256:" + "0" * 64, "sha256:" + "1" * 64, plain, "V",
                [["apply", "transcript", [["domain", "Transcript", "invented"]]]],
                [["apply", "bool", []]], [], [], []]
        with self.assertRaisesRegex(ValueError, "plain-profile-abi"):
            render.render_declaration(fake, "ForgedPlain")


if __name__ == "__main__":
    unittest.main()
