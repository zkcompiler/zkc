#!/usr/bin/env python3
"""Closed ranges preserve bounds, carried state, captures and continuation yields."""
import copy
import unittest

from render import block

INDEX = ["apply", "index", []]
BOOL = ["apply", "bool", []]
RANGE = ["exec.range", [["site", ["string", "traverse"]]], [], [0, 1, 2, 3], [INDEX],
         [[[INDEX, INDEX, BOOL], [], ["exec.complete", [2, 0]], True]]]


class LocalRanges(unittest.TestCase):
    def decode(self, instruction):
        return block([instruction], [("index", None)] * 3 + [("boolean", None)],
                     [0, 1, 2, 3], "", [[], []])

    def test_conditional_range(self):
        rendered, kinds, places = self.decode(RANGE)
        self.assertIn(".localRange true, [0, 1, 2, 3]", rendered[0])
        self.assertIn("[], [2, 0]", rendered[0])
        self.assertEqual(places, [0, 1, 2, 3, 4])
        self.assertEqual(kinds[-1], ("index", None))

    def test_unconditional_range(self):
        changed = copy.deepcopy(RANGE)
        changed[5][0][3] = False
        changed[5][0][2][1] = [0]
        self.assertIn(".localRange false", self.decode(changed)[0][0])

    def test_all_boundaries_checked(self):
        for mode in ("stop", "flag", "bounds", "initial", "inputs", "yield", "attrs", "binding"):
            changed = copy.deepcopy(RANGE)
            if mode == "stop": changed[5][0][2] = ["exec.reject", []]
            if mode == "flag": changed[5][0][3] = 1
            if mode == "bounds": changed[3][0] = 3
            if mode == "initial": changed[3][2] = 3
            if mode == "inputs": changed[5][0][0] = [INDEX, BOOL, INDEX]
            if mode == "yield": changed[5][0][2][1] = [0, 2]
            if mode == "attrs": changed[1].append(["other", ["bool", True]])
            if mode == "binding": changed[2] = ["control.require", [], "", [BOOL], []]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.decode(changed)


if __name__ == "__main__":
    unittest.main()
