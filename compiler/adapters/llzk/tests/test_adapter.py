#!/usr/bin/env python3
"""Executable boundary tests; requires the separately built pinned LLVM20 tool."""

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

TOOL = pathlib.Path(sys.argv.pop(1)).resolve()
FIELD = '!felt.type<"bls12381">'
PRIME = "52435875175126190479447740508185965837690552500527637822603658699938581184513"


def source(extra="", equation=True, fields="", compute_extra=""):
    return f"""module attributes {{llzk.lang, {fields}llzk.main = !struct.type<@Main>}} {{
  struct.def @Main {{
    struct.member @out : {FIELD} {{llzk.pub, signal}}
    function.def @compute(%a: {FIELD} {{function.arg_name = "a", llzk.pub}}) -> !struct.type<@Main> {{
      %self = struct.new : !struct.type<@Main>
      {compute_extra}
      struct.writem %self[@out] = %a : !struct.type<@Main>, {FIELD}
      function.return %self : !struct.type<@Main>
    }}
    function.def @constrain(%self: !struct.type<@Main>, %a: {FIELD} {{function.arg_name = "a", llzk.pub}}) {{
      %out = struct.readm %self[@out] : !struct.type<@Main>, {FIELD}
      {extra}
      {f"constrain.eq %out, %a : {FIELD}, {FIELD}" if equation else ""}
      function.return
    }}
  }}
}}
"""


class Adapter(unittest.TestCase):
    def run_case(self, text, code=None, **options):
        with tempfile.TemporaryDirectory(prefix="zkc-llzk-test-") as directory:
            d = pathlib.Path(directory)
            src = d / "source.llzk"
            src.write_text(text)
            opts = dict(
                field="bls12381", entry="Main", outputs="out", public_inputs="a"
            )
            opts.update(options)
            cmd = [str(TOOL), str(src)]
            for key, value in opts.items():
                cmd += ["--" + key.replace("_", "-"), value]
            out = d / "export"
            cmd += ["--output", str(out)]
            result = subprocess.run(cmd, text=True, capture_output=True, timeout=60)
            if code:
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(code, result.stderr)
                self.assertFalse(out.exists(), "refusal must not export a relation")
                return None
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((out / "relation.r1cs").read_bytes().startswith(b"r1cs"))
            return json.loads((out / "receipt.json").read_text())

    def test_scalar(self):
        receipt = self.run_case(source())
        self.assertEqual(receipt["scalar_equations"], 1)
        self.assertTrue(receipt["source_guard_before_lowering"])

    def test_comment_is_not_operation(self):
        self.run_case(source("// constrain.in lookup.fake function.extern"))

    def test_generic_quoted_equality(self):
        self.run_case(
            source(f'"constrain.eq"(%out, %a) : ({FIELD}, {FIELD}) -> ()', False)
        )

    def containment(self, quoted=False):
        arr = f"!array.type<2 x {FIELD}>"
        operation = (
            f'"constrain.in"(%table, %a) : ({arr}, {FIELD}) -> ()'
            if quoted
            else f"constrain.in %table, %a : {arr}, {FIELD}"
        )
        return f"%zero = felt.const 0 : {FIELD}\n%one = felt.const 1 : {FIELD}\n%table = array.new %zero, %one : {arr}\n{operation}"

    def test_original_containment_pre_lowering(self):
        self.run_case(source(self.containment()), "llzk-source-constraint")

    def test_quoted_containment_pre_lowering(self):
        self.run_case(source(self.containment(True)), "llzk-source-constraint")

    def test_hidden_in_dead_branch(self):
        body = (
            "%false = arith.constant false\nscf.if %false {\n"
            + self.containment()
            + "\n}"
        )
        self.run_case(source(body), "llzk-source-constraint")

    def test_unknown_lookup(self):
        self.run_case(source('"lookup.unknown"() : () -> ()'), "llzk-parse")

    def test_unknown_constraint(self):
        self.run_case(source('"constrain.unknown"() : () -> ()'), "llzk-verify")

    def test_effectful_dialect_before_verifier(self):
        self.run_case(source('"global.unknown"() : () -> ()'), "llzk-source-operation")

    def test_external_call(self):
        self.run_case(
            source(f"function.call @external(%a) : ({FIELD}) -> ()"), "llzk-verify"
        )

    def test_external_declaration(self):
        text = source().replace(
            "  struct.def @Main {",
            "  function.def private @external()\n  struct.def @Main {",
        )
        self.run_case(text, "llzk-source-call")

    def test_false_assert(self):
        self.run_case(
            source("%false = arith.constant false\nbool.assert %false"),
            "llzk-source-assert",
        )

    def test_dynamic_assert(self):
        self.run_case(
            source(f"%b = bool.cmp eq(%out, %a) : {FIELD}, {FIELD}\nbool.assert %b"),
            "llzk-source-assert",
        )

    def test_true_assert(self):
        self.run_case(source("%true = arith.constant true\nbool.assert %true"))

    def test_compute_cannot_add_constraint(self):
        self.run_case(
            source(compute_extra=f"constrain.eq %a, %a : {FIELD}, {FIELD}"),
            "llzk-verify",
        )

    def test_declared_field(self):
        self.run_case(
            source(fields=f'llzk.fields = #felt.field<"bls12381", {PRIME}>, ')
        )

    def test_declared_wrong_field(self):
        self.run_case(
            source(fields='llzk.fields = #felt.field<"bls12381", 17>, '), "llzk-field"
        )

    def test_selected_wrong_field(self):
        self.run_case(source(), "llzk-parse", field="bn254")

    def test_wrong_public_output(self):
        self.run_case(source(), "llzk-public-outputs", outputs="other")

    def test_wrong_public_input(self):
        self.run_case(source(), "llzk-public-inputs", public_inputs="other")

    def test_wrong_entry(self):
        self.run_case(source(), "llzk-entry", entry="Other")

    def test_duplicate_binding(self):
        self.run_case(source(), "llzk-interface", outputs="out,out")

    def test_malformed(self):
        self.run_case(source()[:-7], "llzk-parse")

    def test_source_size_limit(self):
        self.run_case(" " * (2 * 1024 * 1024 + 1), "llzk-source-limit")

    def test_parser_nesting_limit(self):
        for opening, closing, value in (("[", "]", "0 : i64"), ("tuple<", ">", "i1")):
            with self.subTest(opening=opening):
                self.run_case(
                    "module attributes {test.deep = "
                    + opening * 16384
                    + value
                    + closing * 16384
                    + "} {}",
                    "llzk-depth-limit",
                )

    def test_delimiters_in_comment_and_string(self):
        self.run_case(source("// " + "[" * 10000))
        self.run_case(
            source().replace(
                "llzk.lang,", 'test.note = "' + "[" * 10000 + '", llzk.lang,'
            )
        )

    def test_operation_limit(self):
        self.run_case(
            source("// padding\n" * 4).replace(
                "      function.return\n",
                "      %c = arith.constant true\n"
                + "bool.assert %c\n" * 100001
                + "      function.return\n",
            ),
            "llzk-operation-limit",
        )

    def test_zero_equation_explicit_binding(self):
        receipt = self.run_case(source(equation=False))
        self.assertTrue(receipt["zero_equations"])
        self.assertEqual(receipt["public_outputs"], ["out"])
        self.assertEqual(receipt["public_inputs"], ["a"])


if __name__ == "__main__":
    unittest.main()
