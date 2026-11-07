#!/usr/bin/env python3
"""Actual embedded bodies and named finite folds remain in the formal subject."""
import copy
import unittest

from render import attributes, block, operation

INDEX = ["apply", "index", []]
BOOL = ["apply", "bool", []]
FOLD = ["data.finite_fold", [["domain", ["symbol", ["range"]]],
                              ["step", ["symbol", ["sum"]]]], [], [0, 1, 2], [INDEX], []]
COMPUTE = ["exec.compute", [["callee", ["symbol", ["calculation"]]], ["site", ["string", "compute"]]],
           [], [0, 1, 2], [INDEX], [[[INDEX, INDEX, INDEX], [FOLD], ["func.return", [3]]]]]


class EmbeddedMath(unittest.TestCase):
    def decode(self, instruction):
        return block([instruction], [("index", None)] * 3, [0, 1, 2], "", [[], []])

    def test_body_and_fold_remain(self):
        rendered, kinds, places = self.decode(COMPUTE)
        self.assertIn(".mathCompute", rendered[0])
        self.assertIn('.finiteFold "range" "sum" ""', rendered[0])
        self.assertEqual(places, [0, 1, 2, 3])
        self.assertEqual(kinds, [("index", None)] * 4)

    def test_boundaries(self):
        for mode in ("stop", "arguments", "results", "yield", "symbol", "attrs"):
            changed = copy.deepcopy(COMPUTE)
            if mode == "stop": changed[5][0][2] = ["exec.complete", [3]]
            if mode == "arguments": changed[5][0][0][0] = BOOL
            if mode == "results": changed[4] = [BOOL]
            if mode == "yield": changed[5][0][2][1] = [4]
            if mode == "symbol": changed[1][0][1][1] = ["a", "b"]
            if mode == "attrs": changed[1].append(["other", ["bool", True]])
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.decode(changed)

    def test_selection_keeps_nominal_operand_and_result_types(self):
        self.assertEqual(operation("arith.select", {}, [], [("boolean", None), ("index", None),
                         ("index", None)], [("index", None)], [[], []]), ".calculate (.select .index)")
        for inputs, outputs in [([("boolean", None), ("field", "a"), ("field", "b")], [("field", "a")]),
                                ([("boolean", None), ("index", None), ("index", None)], [("boolean", None)])]:
            with self.subTest(inputs=inputs), self.assertRaises(ValueError):
                operation("arith.select", {}, [], inputs, outputs, [[], []])

    def test_fold_names_and_index_word_signature(self):
        changed = copy.deepcopy(FOLD)
        changed[1][0][1][1] = []
        with self.assertRaises(ValueError):
            operation(changed[0], attributes(changed[1]), changed[2],
                      [("index", None)] * 3, [("index", None)], [[], []])
        for name in ("data.index_wrapping_add", "data.index_wrapping_subtract",
                     "data.index_bit_and", "data.index_logical_shift_right"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                operation(name, {}, [], [("index", None)] * 2, [("boolean", None)], [[], []])


if __name__ == "__main__":
    unittest.main()
