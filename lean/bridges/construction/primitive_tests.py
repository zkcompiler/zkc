#!/usr/bin/env python3
"""Checked installed scalars must not acquire total mathematical meanings."""
import copy
import unittest

from render import operation

INDEX = ["apply", "index", []]
BOOL = ["apply", "bool", []]
ATTRS = {"binding": ("symbol", ["installed"]), "parameters": ("array", []),
         "site": ("string", "check")}


class CheckedPrimitives(unittest.TestCase):
    def test_checked_and_mathematical_equality_are_distinct(self):
        binding = ["index.equal", [], "", [INDEX, INDEX], [BOOL]]
        self.assertEqual(operation("exec.apply", ATTRS, binding,
                         [("index", None)] * 2, [("boolean", None)], [[], []]),
                         ".execute .indexEqual")
        self.assertEqual(operation("data.index_equal", {}, [],
                         [("index", None)] * 2, [("boolean", None)], [[], []]),
                         ".calculate .indexEqual")

    def test_installed_index_constant_retains_checked_meaning(self):
        binding = ["index.constant", [], "", [], [INDEX]]
        for value in ("0", str((1 << 64) - 1)):
            attrs = copy.deepcopy(ATTRS)
            attrs["parameters"] = ("array", [["parameter", ["natural", value]]])
            with self.subTest(value=value):
                self.assertEqual(operation("exec.apply", attrs, binding, [],
                    [("index", None)], [[], []]), f".execute (.indexConstant {value})")
        self.assertEqual(operation("data.index", {"value": ("integer", ["unsigned", "64", "7"])},
                         [], [], [("index", None)], [[], []]), ".calculate (.indexConstant 7)")
        for value in ("-1", "01", str(1 << 64)):
            attrs = copy.deepcopy(ATTRS)
            attrs["parameters"] = ("array", [["parameter", ["natural", value]]])
            with self.subTest(value=value), self.assertRaises(ValueError):
                operation("exec.apply", attrs, binding, [], [("index", None)], [[], []])

    def test_other_checked_scalars(self):
        for contract, constructor, inputs, output in [
                ("index.less", "indexLess", [INDEX, INDEX], BOOL),
                ("index.add", "indexAdd", [INDEX, INDEX], INDEX),
                ("bool.not", "booleanNot", [BOOL], BOOL)]:
            kinds = [("boolean" if ty == BOOL else "index", None) for ty in inputs]
            result = [("boolean" if output == BOOL else "index", None)]
            with self.subTest(contract=contract):
                self.assertEqual(operation("exec.apply", ATTRS,
                    [contract, [], "", inputs, [output]], kinds, result, [[], []]),
                    f".execute .{constructor}")

    def test_changed_binding_cannot_choose_a_meaning(self):
        original = ["index.equal", [], "", [INDEX, INDEX], [BOOL]]
        for index, value in [(1, [["natural", "1"]]), (2, "native/index.equal"),
                             (3, [BOOL, BOOL]), (4, [INDEX])]:
            changed = copy.deepcopy(original)
            changed[index] = value
            with self.subTest(index=index), self.assertRaises(ValueError):
                operation("exec.apply", ATTRS, changed,
                          [("index", None)] * 2, [("boolean", None)], [[], []])
        changed = copy.deepcopy(ATTRS)
        changed["parameters"] = ("array", [["parameter", ["natural", "1"]]])
        with self.assertRaises(ValueError):
            operation("exec.apply", changed, original,
                      [("index", None)] * 2, [("boolean", None)], [[], []])


if __name__ == "__main__":
    unittest.main()
