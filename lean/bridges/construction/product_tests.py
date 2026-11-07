#!/usr/bin/env python3
"""Nominal construction and empty one-constructor match decoding."""
import copy
import unittest

from render import attributes, block, operation, sort

INDEX = ["apply", "index", []]
BOOL = ["apply", "bool", []]
PRODUCT = ["variant", ["tuple", [["atom", "test.record"]]], [["Record", [INDEX, INDEX]]]]


def projection():
    return ["exec.match", [["alternatives", ["array", [["string", "Record"]]]],
                            ["site", ["string", "project"]]], [], [0, 1], [INDEX, INDEX, INDEX],
            [[[INDEX, INDEX, INDEX], [], ["exec.complete", [1, 2, 0]], "Record", [INDEX, INDEX]]]]


class ProductProjection(unittest.TestCase):
    def decode(self, instruction):
        return block([instruction], [sort(PRODUCT)[1], sort(INDEX)[1]], [0, 1], "", [[], []])

    def test_ordered_projections_and_capture_alias(self):
        instructions, kinds, places = self.decode(projection())
        self.assertEqual(len(instructions), 2)
        self.assertIn("(.there (.here))", instructions[0])
        self.assertIn("(.here)", instructions[1])
        self.assertEqual(places, [0, 1, 2, 1, 3])
        self.assertEqual(kinds[2:], [("index", None)] * 2)
        # A same-typed permutation is retained as a different computation.
        swapped = projection()
        swapped[5][0][2][1] = [0, 2, 1]
        changed, _, changed_places = self.decode(swapped)
        self.assertNotEqual(instructions, changed)
        self.assertEqual(places, changed_places)

    def test_construction_keeps_nominal_identity(self):
        attrs = attributes([["alternative", ["string", "Record"]], ["site", ["string", "make"]]])
        term = operation("exec.variant", attrs, [], [("index", None)] * 2, [sort(PRODUCT)[1]], [[], []])
        other = copy.deepcopy(PRODUCT)
        other[1][1][0][1] = "other.record"
        self.assertNotEqual(term, operation("exec.variant", attrs, [], [("index", None)] * 2,
                                           [sort(other)[1]], [[], []]))
        with self.assertRaises(ValueError):
            operation("exec.variant", attrs, [], [("boolean", None), ("index", None)],
                      [sort(PRODUCT)[1]], [[], []])

    def test_projection_does_not_erase_code_or_stops(self):
        for mode in ("body", "stop", "constructor", "payload", "arguments", "yield", "results", "attribute"):
            changed = projection()
            region = changed[5][0]
            if mode == "body": region[1] = [["protocol.guard", [], [], [0], [], []]]
            if mode == "stop": region[2] = ["exec.reject", []]
            if mode == "constructor": region[3] = "Other"
            if mode == "payload": region[4][0] = BOOL
            if mode == "arguments": region[0][2] = BOOL
            if mode == "yield": region[2][1][0] = 3
            if mode == "results": changed[4][0] = BOOL
            if mode == "attribute": changed[1].append(["extra", ["bool", True]])
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.decode(changed)


if __name__ == "__main__":
    unittest.main()
