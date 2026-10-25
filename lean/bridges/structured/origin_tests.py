#!/usr/bin/env python3
"""Focused strict origin-printer controls. No captured exports are rewritten."""

import unittest

from snapshot import definition, function_origin, origin_term


class OriginTests(unittest.TestCase):
    def refuses(self, value, kind="protocol"):
        with self.assertRaises(ValueError):
            function_origin(kind, value)

    def test_closed_constructors(self):
        values = [["nat", "0"], ["field", "F"], ["group", "G"],
                  ["domain", "Field", "D"], ["asset", "Commitment", "A"],
                  ["bool"], ["index"], ["unit"], ["tuple", [["bool"], ["unit"]]],
                  ["array", ["field", "F"], "12"],
                  ["builtin", "Vector", [["field", "F"]]],
                  ["formal", "Function", [["index"], ["bool"]]]]
        values += [["nominal", kind, "test::T", []]
                   for kind in ("record", "variant", "associated", "module")]
        for value in values:
            with self.subTest(value=value):
                self.assertIn("some (.protocol", function_origin("protocol", ["test::P", [["T", value]]]))
        self.assertNotEqual(origin_term(["nominal", "record", "test::T", []]),
                            origin_term(["nominal", "variant", "test::T", []]))

    def test_kinds(self):
        self.assertEqual(function_origin("math", []), "none")
        self.assertEqual(function_origin("local", ["helper", [["n", "1"]]]),
                         'some (.local "helper" [("n", "1")])')
        self.assertEqual(function_origin("protocol", ["test::P", []]),
                         'some (.protocol ⟨"test::P", []⟩)')
        for kind in ("protocol", "local"):
            self.refuses([], kind)
        self.refuses(["test::P", []], "math")
        self.refuses(["test::P", [["T", ["unit"]]]], "local")
        self.refuses(["test::P", [["T", "unit"]]])

    def test_duplicates_and_order(self):
        self.refuses(["P", [["n", ["nat", "1"]], ["n", ["nat", "2"]]]])
        self.refuses(["helper", [["n", "1"], ["n", "2"]]], "local")
        rendered = function_origin("protocol", ["P", [["z", ["unit"]], ["a", ["index"]]]])
        self.assertLess(rendered.index('"z"'), rendered.index('"a"'))
        rendered = function_origin("protocol", ["P", [["é", ["unit"]], ["e\u0301", ["unit"]]]])
        self.assertIn('"e\u0301"', rendered)  # no normalization; NFC belongs to native admission

    def test_malformed_terms(self):
        for value in [[], ["unknown"], ["parameter", "T"], ["symbolic", "n"],
                      ["bool", "extra"], ["field"], ["nat", 1],
                      ["nominal", "invalid", "T", []], ["tuple", "no"], {"tag": "unit"}]:
            with self.subTest(value=value):
                self.refuses(["P", [["T", value]]])
        for decimal in ("", "00", "01", "-1", "+1", "1.0", "1e2", " 1", "١", "１", "1_0", "1" * 513):
            for value in (["nat", decimal], ["array", ["unit"], decimal]):
                with self.subTest(value=value):
                    self.refuses(["P", [["T", value]]])

    def test_string_limits(self):
        function_origin("protocol", ["a" * 2048, []])
        function_origin("protocol", ["é" * 1024, []])
        for path in ("a" * 2049, "é" * 1025, "", "a::", "1a", "a/b", "a.b", "a b", "a\0b"):
            self.refuses([path, []])
        for key in ("a" * 513, "", "a::b", "1a"):
            self.refuses(["P", [[key, ["unit"]]]])
        for value in (["field", "a" * 513], ["group", "a" * 513],
                      ["domain", "a" * 513, "D"], ["asset", "A", "a" * 513],
                      ["formal", "a" * 513, []], ["builtin", "a" * 513, []],
                      ["nominal", "record", "a" * 513, []], ["field", "x\0y"]):
            self.refuses(["P", [["T", value]]])
        function_origin("protocol", ["P", [["a" * 512, ["field", "F" * 512]]]])

    def test_tree_limits(self):
        value = ["unit"]
        for _ in range(63):
            value = ["array", value, "1"]
        origin_term(value)
        with self.assertRaises(ValueError):
            origin_term(["array", value, "1"])
        constructors = [lambda children: ["tuple", children],
                        lambda children: ["nominal", "record", "T", children],
                        lambda children: ["builtin", "T", children],
                        lambda children: ["formal", "T", children]]
        for constructor in constructors:
            origin_term(constructor([["unit"]] * 512))
            self.refuses(["P", [["T", constructor([["unit"]] * 513)]]])
        function_origin("protocol", ["P", [[f"n{i}", ["unit"]] for i in range(128)]])
        self.refuses(["P", [[f"n{i}", ["unit"]] for i in range(129)]])
        function_origin("protocol", ["P", [[f"n{i}", ["tuple", [["unit"]] * 511]] for i in range(8)]])
        self.refuses(["P", [[f"n{i}", ["tuple", [["unit"]] * 512]] for i in range(8)]])

    def test_definition_dispatch(self):
        header = ["function", "main", "protocol", "public", [], [],
                  ["protocol", ["P"], [], []], [], ["test::P", []], ["block", [], ["return", []]]]
        self.assertIn('some (.protocol ⟨"test::P", []⟩)', definition(header))
        header[8] = []
        with self.assertRaises(ValueError):
            definition(header)


if __name__ == "__main__":
    unittest.main()
