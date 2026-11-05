#!/usr/bin/env python3
"""Exact numerical signatures and strict literal/rendering boundaries.

These controls use synthetic rows and values, never maintained subject exports
or native execution as an oracle for the independently fixed equations.
"""

import copy
import json
import unittest

from snapshot import NUMERICAL_SOURCE_PRIMITIVES, primitive_binding, render, render_parameter, ty
from bridges.common import schema

BASE = "koala-bear"
EXTENSION = "koala-bear.ext8-binomial3"
BINARY = "gf2-64.pentanomial-4-3-1"
BINARY_EXTENSION = BINARY + ".ext3-trinomial1"


def logical(name, domain=EXTENSION):
    return ["apply", name, [] if name in ("bool", "index", "indices")
            else [["domain", "Field", domain]]]


# The first twenty are the actual scalar FRI source use; the remaining twenty
# complete the STARK numerical vocabulary. Ports are fixed here independently
# of schema.resolve_signature, and every binding is then checked against it.
FRI = {
    "bool.and": (["bool", "bool"], ["bool"]),
    "bool.not": (["bool"], ["bool"]),
    "bool.or": (["bool", "bool"], ["bool"]),
    "field.constant": ([], ["field"]),
    "field.inverse": (["field"], ["field"]),
    "field.mul": (["field", "field"], ["field"]),
    "indices.append": (["indices", "index"], ["indices"]),
    "indices.at": (["indices", "index"], ["index"]),
    "indices.empty": ([], ["indices"]),
    "indices.length": (["indices"], ["index"]),
    "poly.coefficients": (["polynomial"], ["vector"]),
    "poly.coset_interpolate": (["vector", "field"], ["polynomial"]),
    "poly.domain_point": (["field", "index", "index"], ["field"]),
    "poly.domain_root": (["index"], ["field"]),
    "poly.even_odd_fold": (["vector", "field", "field"], ["vector"]),
    "poly.from_coefficients": (["vector"], ["polynomial"]),
    "poly.univariate_evaluate": (["polynomial", "field"], ["field"]),
    "vector.concat": (["vector", "vector"], ["vector"]),
    "vector.fill": (["field", "index"], ["vector"]),
    "vector.get": (["vector", "index"], ["field"]),
}
STARK = {
    "field.add": (["field", "field"], ["field"]),
    "field.sub": (["field", "field"], ["field"]),
    "poly.domain_points": (["field", "index"], ["vector"]),
    "poly.coset_evaluate_batch": (["vector", "index", "index", "field", "index"], ["vector"]),
    "poly.coset_evaluate_at": (["vector", "index", "index", "field", "field"], ["vector"]),
    "poly.coset_extend": (["vector", "index", "index", "field", "field", "index"], ["vector"]),
    "poly.opening_quotient_sum": (["vector", "index", "index", "field", "indices",
                                   "vector", "vector", "vector", "vector"], ["vector"]),
    "vector.add": (["vector", "vector"], ["vector"]),
    "vector.sub": (["vector", "vector"], ["vector"]),
    "vector.mul": (["vector", "vector"], ["vector"]),
    "vector.scale": (["vector", "field"], ["vector"]),
    "vector.inverse": (["vector"], ["vector"]),
    "vector.geometric": (["field", "index"], ["vector"]),
    "vector.slice": (["vector", "index", "index"], ["vector"]),
    "vector.transpose": (["vector", "index", "index"], ["vector"]),
    "vector.embed": (["base_vector"], ["vector"]),
    "vector.rotate": (["vector", "index"], ["vector"]),
    "vector.bit_reverse_rows": (["vector", "index"], ["vector"]),
    "vector.prefix_sum": (["vector"], ["vector"]),
    "vector.prefix_product": (["vector"], ["vector"]),
}
ROWS = [[
    ["nominal", BASE, "Field", [],
     ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], "2130706433"],
    ["nominal", EXTENSION, "Field", [["BaseField", BASE]],
     ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField",
      "IndexRandomness", "IndexBlockRandomness"], "2130706433"],
], []]


def binding(name, ports):
    def port(tag):
        return logical("vector", BASE) if tag == "base_vector" else logical(tag)
    arguments = [] if name.startswith(("bool.", "indices.")) else [["domain", "Field", EXTENSION]]
    return ["binding", name.replace(".", "_"), name, arguments, "",
            list(map(port, ports[0])), list(map(port, ports[1]))]


def unit(literal, bindings=None):
    bindings = bindings or [binding("field.constant", FRI["field.constant"])]
    field = logical("field")
    instruction = [["exec", "exec.apply", "field_constant", [literal]], [], [field], [], "literal"]
    local = ["function", "literal", "local", "private", [], [field], [], [], ["literal", []],
             ["block", [instruction], ["return", [0]]]]
    protocol = ["function", "Entry", "protocol", "public", [], [field],
                ["protocol", ["P"], [], [["P"]]], [], ["tests::Entry", []],
                ["block", [[["local_call", "literal", "P"], [], [field], [], "call"]],
                 ["return", [0]]]]
    return ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
            "Entry", [], [], bindings, [protocol, local], [["Entry", []]], copy.deepcopy(ROWS), [[], [], []]]


class NumericalTests(unittest.TestCase):
    def test_exact_fri_then_stark_inventory(self):
        self.assertEqual(len(FRI), 20)
        self.assertEqual(len(STARK), 20)
        self.assertEqual(set(FRI) | set(STARK), NUMERICAL_SOURCE_PRIMITIVES)
        for name, ports in list(FRI.items()) + list(STARK.items()):
            with self.subTest(name=name):
                primitive_binding(binding(name, ports), ROWS)

    def test_every_changed_shape_refuses(self):
        for name, ports in (FRI | STARK).items():
            changed = binding(name, ports)
            changed[-1] = [logical("index")]
            if changed[-1] == binding(name, ports)[-1]:
                changed[-1] = [logical("bool")]
            with self.subTest(name=name), self.assertRaises(ValueError):
                primitive_binding(changed, ROWS)

    def test_nominal_polynomial_and_embedding_ports(self):
        self.assertIn('.polynomial "' + EXTENSION + '"', ty(logical("polynomial")))
        self.assertNotEqual(ty(logical("polynomial")), ty(logical("vector")))
        for name in ("poly.from_coefficients", "poly.univariate_evaluate", "vector.embed"):
            changed = binding(name, (FRI | STARK)[name])
            changed[-2][0] = logical("vector", EXTENSION if name == "vector.embed" else BASE)
            with self.assertRaises(ValueError):
                primitive_binding(changed, ROWS)
        with self.assertRaises(ValueError):
            schema.interpreted_type(logical("polynomial"), payload=True)

    def test_literal_parameters_remain_typed_data(self):
        self.assertEqual(render_parameter(["natural", "7"]), '.natural "7"')
        self.assertEqual(
            render_parameter(["field_literal", EXTENSION, "natural", "0"]),
            f'.fieldLiteral "{EXTENSION}" "natural" "0"')

    def test_full_renderer_preserves_literal(self):
        literal = ["field_literal", EXTENSION, "natural", "2130706432"]
        rendered = render(unit(literal), "Tests.NumericalSynthetic")
        self.assertIn(render_parameter(literal), rendered)
        self.assertIn('"field.constant"', rendered)
        for changed in (["field_literal", BASE, "natural", "1"],
                        ["field_literal", EXTENSION, "natural", "2130706433"],
                        ["field_literal", EXTENSION, "natural", "01"],
                        ["field_literal", EXTENSION, "bits", "0x2"],
                        ["natural", "1"]):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                render(unit(changed), "Tests.NumericalSynthetic")

    def test_binary_exact_width_and_encoding(self):
        spec = {"minimum": 1, "maximum": 1, "validator": "FieldLiteral"}
        for domain, width in ((BINARY, 64), (BINARY_EXTENSION, 192)):
            for encoding, digits in (("natural", "0"), ("natural", "1"),
                                     ("bits", hex(1 << (width - 1))),
                                     ("bits", hex((1 << width) - 1))):
                value = ["field_literal", domain, encoding, digits]
                schema.validate_parameters([value], spec, domain, 2)
                self.assertIn(digits, render_parameter(value))
            for encoding, digits in (("natural", "2"), ("bits", "0x1"), ("bits", "0x0"),
                                     ("bits", "0x02"), ("bits", "0xA"),
                                     ("bits", hex(1 << width))):
                with self.subTest(domain=domain, digits=digits), self.assertRaises(ValueError):
                    schema.validate_parameters([["field_literal", domain, encoding, digits]],
                                               spec, domain, 2)

    def test_missing_capability_and_unknown_contract_refuse(self):
        rows = copy.deepcopy(ROWS)
        rows[0][1][4].remove("CharacteristicNotTwo")
        with self.assertRaises(ValueError):
            primitive_binding(binding("poly.even_odd_fold", FRI["poly.even_odd_fold"]), rows)
        for name in ("poly.coset_evaluate", "poly.opening_quotient", "vector.bit_reverse"):
            with self.assertRaises(ValueError):
                primitive_binding(binding(name, (["vector"], ["vector"])), ROWS)


if __name__ == "__main__":
    unittest.main()
