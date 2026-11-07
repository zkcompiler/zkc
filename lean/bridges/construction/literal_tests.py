#!/usr/bin/env python3
"""Constructed literals use the exact nominal field's admitted characteristic."""

import copy
import unittest

from render import attributes, operation


class FieldLiterals(unittest.TestCase):
    def render(self, field, value, rows, operands=()):
        attrs = attributes([["value", ["parameter", value]]])
        return operation("algebra.constant", attrs, [], list(operands), [("field", field)], rows)

    def test_natural_literals_across_prime_and_extension_fields(self):
        for field, characteristic in [
            ("bls12-381.fr", 52435875175126190479447740508185965837690552500527637822603658699938581184513),
            ("koala-bear", 2130706433),
            ("koala-bear.ext8-binomial3", 2130706433),
            ("gf2-64.pentanomial-4-3-1", 2),
        ]:
            rows = [[["nominal", field, "Field", [], [], str(characteristic)]], []]
            for value in (0, 1, characteristic - 1):
                with self.subTest(field=field, value=value):
                    self.assertEqual(self.render(field, ["field_literal", field, "natural", str(value)], rows),
                                     f'.calculate (.fieldConstant "{field}" {value})')
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.render(field, ["field_literal", field, "natural", str(characteristic)], rows)

    def test_literal_identity_encoding_and_canonical_digits(self):
        field = "koala-bear.ext8-binomial3"
        rows = [[["nominal", field, "Field", [], [], "2130706433"]], []]
        for literal in (["field_literal", "koala-bear", "natural", "1"],
                        ["field_literal", field, "natural", "01"],
                        ["field_literal", field, "bits", "0x1"],
                        ["natural", "1"]):
            with self.subTest(literal=literal), self.assertRaises(ValueError):
                self.render(field, literal, rows)
        with self.assertRaises(ValueError):
            self.render(field, ["field_literal", field, "natural", "1"], rows, [("index", None)])

    def test_characteristic_requires_one_complete_field_row(self):
        field = "koala-bear.ext8-binomial3"
        literal = ["field_literal", field, "natural", "1"]
        row = ["nominal", field, "Field", [], [], "2130706433"]
        invalid = [[[], []], [[row, row], []]]
        for index, value in [(1, "koala-bear"), (2, "Group"),
                             (5, None), (5, "01"), (5, "1")]:
            changed = copy.deepcopy(row)
            changed[index] = value
            invalid.append([[changed], []])
        for rows in invalid:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.render(field, literal, rows)


if __name__ == "__main__":
    unittest.main()
