#!/usr/bin/env python3
"""Closed local selection retains guards without becoming mathematical selection."""
import copy
import unittest

from render import attributes, block, operation

BOOL = ["apply", "bool", []]
GUARD = ["exec.apply", [["binding", ["symbol", ["require"]]], ["parameters", ["array", []]],
                        ["site", ["string", "guard"]]],
         ["control.require", [], "", [BOOL], []], [0], [], []]
LOCAL = ["exec.test", [["site", ["string", "choose"]]], [], [0, 1], [BOOL],
         [[[BOOL], [], ["exec.complete", [0]], "then", []],
          [[BOOL], [GUARD], ["exec.complete", [0]], "else", []]]]


class LocalBranches(unittest.TestCase):
    def decode(self, instruction):
        return block([instruction], [("boolean", None)] * 2, [0, 1], "", [[], []])

    def test_local_branch_and_guard_are_retained(self):
        rendered, kinds, places = self.decode(LOCAL)
        self.assertIn(".localBranch", rendered[0])
        self.assertIn('.require "guard"', rendered[0])
        self.assertNotIn(".mathBranch", rendered[0])
        self.assertEqual(places, [0, 1, 2])
        self.assertEqual(kinds, [("boolean", None)] * 3)

    def test_dormant_arm_and_terminals_checked(self):
        for mode in ("stop", "label", "arity", "yield", "payload", "attrs"):
            changed = copy.deepcopy(LOCAL)
            if mode == "stop": changed[5][1][2] = ["exec.reject", []]
            if mode == "label": changed[5][1][3] = "then"
            if mode == "arity": changed[5][1][0] = []
            if mode == "yield": changed[5][1][2][1] = [4]
            if mode == "payload": changed[5][1][4] = [BOOL]
            if mode == "attrs": changed[1].append(["other", ["bool", True]])
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.decode(changed)

    def test_guard_has_exact_boolean_abi(self):
        attrs = attributes(GUARD[1])
        for inputs, outputs in [([], []), ([("index", None)], []),
                                ([("boolean", None)], [("boolean", None)])]:
            with self.subTest(inputs=inputs, outputs=outputs), self.assertRaises(ValueError):
                operation("exec.apply", attrs, GUARD[2], inputs, outputs, [[], []])


if __name__ == "__main__":
    unittest.main()
