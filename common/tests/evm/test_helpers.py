import unittest

from abi import SELECTOR, decode_verify, encode_verify, keccak256, malformed_cases, word
from foundation_controls import check_native_outcome
from hash_chain_reference import BLS_SUITE, Chain
from oracle import chain_trace, check_trace
from validate import ABI_REFUSALS, REVERT_CLASSES, check_return, check_revert


class NativeOutcomeTests(unittest.TestCase):
    def test_exact_stopped_outcome(self):
        fixture = {"decision": None, "native_error": "refused:bytes-bounds"}
        check_native_outcome(fixture, None, "refused:bytes-bounds")
        for error in (None, "refused:zero-inverse", "artifact-stopped:Decode(Header)"):
            with self.subTest(error=error), self.assertRaises(AssertionError):
                check_native_outcome(fixture | {"native_error": error}, None, "refused:bytes-bounds")
        with self.assertRaises(ValueError):
            check_native_outcome(fixture, None, None)

    def test_complete_outcome_cannot_hide_an_error(self):
        for decision in (True, False):
            fixture = {"decision": decision, "native_error": None if decision else "artifact-rejected"}
            check_native_outcome(fixture, decision, None)
            with self.assertRaises(AssertionError):
                check_native_outcome(fixture | {"native_error": "refused:bytes-bounds"}, decision, None)
            with self.assertRaises(AssertionError):
                check_native_outcome(fixture | {"decision": int(decision)}, decision, None)


class AbiTests(unittest.TestCase):
    def test_known_layout(self):
        # Two empty array elements occupy two head words and two length words.
        encoded = encode_verify([b"", b""], b"", b"")
        self.assertEqual(encoded, SELECTOR + b"".join(map(word, [
            96, 256, 288, 2, 64, 96, 0, 0, 0, 0,
        ])))

    def test_boundary_lengths(self):
        for length in [0, 1, 31, 32, 33, 255, 32768]:
            with self.subTest(length=length):
                values = [bytes(length), b"abc"]
                encoded = encode_verify(values, b"context", b"proof")
                self.assertEqual(decode_verify(encoded), (values, b"context", b"proof"))
        self.assertEqual(decode_verify(encode_verify([], b"", b"")), ([], b"", b""))

    def test_context_precedes_proof_on_wire(self):
        encoded = encode_verify([], b"c", b"p" * 33)
        # No public elements: context begins at body byte 128 and occupies 64
        # bytes; proof begins at 192 and occupies 96 bytes. Check actual payload
        # placement independently of this module's paired decoder.
        self.assertEqual(encoded[:100], SELECTOR + word(96) + word(128) + word(192))
        self.assertEqual(encoded[132:196], word(1) + b"c" + bytes(31))
        self.assertEqual(encoded[196:], word(33) + b"p" * 33 + bytes(31))

    def test_malformed(self):
        cases = malformed_cases(encode_verify([b"a", b"bc"], b"context", b"proof"))
        self.assertIn("padding", cases)
        for name, encoded in cases.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                decode_verify(encoded)

    def test_oversize(self):
        with self.assertRaises(ValueError):
            encode_verify([bytes(256 * 1024)], b"", b"")

    def test_padding_and_hole_controls_preserve_payloads(self):
        encoded = encode_verify([], b"a", b"")
        cases = malformed_cases(encoded)
        padding = cases["padding"]
        # Selector + three head words + empty array length + context length + a.
        expected_at = 4 + 96 + 32 + 32 + 1
        self.assertEqual([i for i, (a, b) in enumerate(zip(encoded, padding)) if a != b], [expected_at])
        self.assertEqual(padding[expected_at], 1)
        hole = cases["hole"]
        context_at = 4 + int.from_bytes(hole[36:68], "big")
        self.assertEqual(int.from_bytes(hole[context_at:context_at + 32], "big"), 1)
        self.assertEqual(hole[context_at + 32:context_at + 33], b"a")
        self.assertEqual(len(hole), len(encoded) + 32)


class TraceTests(unittest.TestCase):
    def test_exact_returned_boolean(self):
        for accepted in (False, True):
            output = word(accepted).hex()
            result = {"phase": "runtime", "status": "return", "output": output, "trace": []}
            check_return(result, output, [])
            for wrong in ("", output[2:], "00" + output, output + "00", word(2).hex()):
                with self.subTest(output=wrong), self.assertRaises(AssertionError):
                    check_return(result | {"output": wrong}, output, [])
            with self.assertRaises(AssertionError):
                check_return(result | {"phase": "deployment"}, output, [])

    def test_exact_refusal_and_frontier(self):
        event = {"kind": "keccak256", "input": "", "output": keccak256(b"").hex(),
                 "status": "return"}
        def result(kind, code, trace):
            return {"phase": "runtime", "status": "revert", "trace": trace,
                    "output": (REVERT_CLASSES[kind] + word(code)).hex()}
        check_revert(result("decode", 7, []), *ABI_REFUSALS["short-head"], [])
        # Reproduce the reviewed regression: ZKCR(10) must not satisfy short-head.
        for wrong in (result("resource", 10, []), result("decode", 8, []),
                      result("decode", 7, [event])):
            with self.assertRaises(AssertionError):
                check_revert(wrong, "decode", 7, [])
        with self.assertRaises(AssertionError):
            check_revert(result("source", 6, []), "source", 6, [event])
        capacity = result("resource", 2, [])
        for wrong in (result("resource", 999, []), capacity | {"output": b"ZKCR".hex()},
                      capacity | {"output": capacity["output"] + "00"},
                      capacity | {"phase": "deployment"}):
            with self.assertRaises(AssertionError):
                check_revert(wrong, "resource", 2, [])

    def test_final_observation_mutants(self):
        chain = Chain(BLS_SUITE, b"independently prepared invocation")
        chain.request(b"challenge", 64)
        chain.absorb(b"origin", b"final delivery occurrence")
        chain.absorb(b"value", b"final value")
        expected = chain_trace(chain)
        check_trace(expected, expected)
        changed = [dict(event) for event in expected]
        changed[-1]["input"] += "00"
        mutants = [expected[:-1], expected + [expected[-1]],
                   expected[:-2] + expected[-2:][::-1], changed]
        for actual in mutants:
            with self.assertRaises(AssertionError):
                check_trace(actual, expected)
        # A stopped prefix is checked against its own frontier, never the full run.
        check_trace(expected[:-2], expected[:-2])
        with self.assertRaises(AssertionError):
            check_trace(expected[:-2], expected)


if __name__ == "__main__":
    unittest.main()
