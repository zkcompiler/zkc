"""Independent admission/frontier and physical-oracle mutation controls."""

from copy import deepcopy
import hashlib
import unittest

from curve_closure import Stop, decode, replay
from curve_controls import G, P, R, affine, frame, scalar_frame, scale
from curve_physical import check_physical_execution, check_precompile_trace, mutation_controls
from foundation_controls import invocation_root
from hash_chain_reference import BLS_SUITE
from logical_tree import encode_tree


def fixture(base=G, point=G, commitment=G, response=0):
    """A compact source schedule, independent of compiler/build output.

    This is a replay unit fixture, not a native producer or SDK receipt.
    The deployed matrix separately uses actual checked source/native proofs.
    """
    events = []
    for index, (kind, direction) in enumerate((
            ("message", ["P", "V"]), ("query", ["random.bls12-381.fr/0", "draw", "V"]),
            ("message", ["V", "P"]), ("message", ["P", "V"]))):
        origin = ["zkc.native-origin-template/0", "source", [], [],
                  [kind, "source", str(index), str(index), *direction]]
        events.append([kind, encode_tree(origin).hex()])
    value = {"source": "independent replay unit fixture", "context": "",
             "public": [frame(base).hex(), frame(point).hex()],
             "descriptor": ["zkc.native-proof-descriptor/0",
                            ["zkc.native-proof-policy/0", "source", "P", "V", "0", BLS_SUITE],
                            "zkc.native-origin/0", events,
                            [["V", str(i), "group:bls12-381.g1", "zkcv.group.bls12-381.g1/0"]
                             for i in range(2)]]}
    proof = b"ZKCPRF00" + hashlib.sha256(invocation_root(value)).digest()
    for wire in (frame(commitment), scalar_frame(response)):
        proof += len(wire).to_bytes(8, "little") + wire
    value["proof"] = proof.hex()
    return value


def nonsquare_frame():
    x = next(x for x in range(1, 100) if pow((x**3 + 4) % P, (P - 1) // 2, P) == P - 1)
    return b"ZKCV\x00\x09" + bytes([0x80 | (x >> 376)]) + x.to_bytes(48, "big")[1:]


class CurveAdmissionTests(unittest.TestCase):
    def test_finite_sign_uses_candidate_before_sign_selection(self):
        positive, negative = [], []
        self.assertEqual(decode(frame(G), "group", positive, 2), G)
        negated = (G[0], P - G[1])
        self.assertEqual(decode(frame(negated), "group", negative, 2), negated)
        self.assertEqual(positive[:3], negative[:3])
        candidate = pow((pow(G[0], 3, P) + 4) % P, (P + 1) // 4, P)
        self.assertEqual(bytes.fromhex(positive[2]["input"])[96:144], candidate.to_bytes(48, "big"))
        for events, point in ((positive, G), (negative, negated)):
            self.assertEqual([e["kind"] for e in events], ["modexp"] * 3 + ["bls12_g1msm"])
            self.assertEqual(bytes.fromhex(events[0]["input"]), (48).to_bytes(32, "big") * 3
                             + G[0].to_bytes(48, "big") + (3).to_bytes(48, "big") + P.to_bytes(48, "big"))
            self.assertEqual(events[-1]["input"], (affine(point) + (1).to_bytes(32, "big")).hex())
            self.assertEqual(events[-1]["output"], affine(point).hex())
            self.assertEqual([e["hash_event_frontier"] for e in events], [2] * 4)

    def test_identity_admission_has_no_physical_calls(self):
        events = []
        self.assertIsNone(decode(frame(None), "group", events, 9))
        self.assertEqual(events, [])

    def test_early_malformed_group_has_no_physical_calls(self):
        good = frame(G)
        invalid = [good[:-1], good + b"\x00", good[:5] + b"\xff" + good[6:],
                   good[:6] + bytes([good[6] & 0x7f]) + good[7:],
                   b"ZKCV\x00\x09\xe0" + bytes(47),
                   b"ZKCV\x00\x09\xc0" + bytes(46) + b"\x01",
                   b"ZKCV\x00\x09" + bytes([0x80 | (P >> 376)]) + P.to_bytes(48, "big")[1:]]
        for wire in invalid:
            with self.subTest(wire=wire.hex()):
                events = []
                with self.assertRaises(Stop):
                    decode(wire, "group", events, 2)
                self.assertEqual(events, [])

    def test_nonsquare_stops_after_three_successful_modexp_calls(self):
        events = []
        with self.assertRaises(Stop):
            decode(nonsquare_frame(), "group", events, 2)
        self.assertEqual([e["kind"] for e in events], ["modexp"] * 3)
        self.assertTrue(all(e["status"] == "return" and e["hash_event_frontier"] == 2 for e in events))

    def test_outside_subgroup_is_a_real_empty_return_failure(self):
        events = []
        with self.assertRaises(Stop):
            decode(b"ZKCV\x00\x09\x80" + bytes(47), "group", events, 2)
        self.assertEqual(len(events), 4)
        event = events[-1]
        self.assertEqual(event["input"], (affine((0, 2)) + (1).to_bytes(32, "big")).hex())
        self.assertEqual((event["kind"], event["output"], event["status"], event["reason"],
                          event["precompile_called"], event["hash_event_frontier"]),
                         ("bls12_g1msm", "", "halt", "PrecompileError", True, 2))


class SourceFrontierTests(unittest.TestCase):
    def test_public_admission_precedes_header_checks(self):
        for base, point, calls in ((G, G, 8), (G, None, 4), (None, None, 0)):
            with self.subTest(calls=calls):
                source = fixture(base, point)
                source["proof"] = ""
                expected = replay(source)
                self.assertEqual(expected["trace"], [])
                self.assertEqual(expected["revert"], ("decode", 11))
                self.assertEqual(len(expected["precompile_trace"]), calls)
                self.assertTrue(all(e["hash_event_frontier"] == 0 for e in expected["precompile_trace"]))

    def test_bad_second_public_point_masks_header_and_binding_failure(self):
        for wire, calls in ((nonsquare_frame(), 7), (b"ZKCV\x00\x09\x80" + bytes(47), 8)):
            for proof in ("", fixture()["proof"]):
                with self.subTest(wire=wire.hex(), proof=bool(proof)):
                    source = fixture()
                    source["public"][1] = wire.hex()
                    source["proof"] = proof
                    expected = replay(source)
                    self.assertEqual(expected["frontier"], "public-1/group-admission")
                    self.assertEqual(expected["revert"], ("decode", 4))
                    self.assertEqual(expected["trace"], [])
                    self.assertEqual(len(expected["precompile_trace"]), calls)

    def test_header_magic_and_binding_have_distinct_hash_frontiers(self):
        source = fixture()
        proof = bytes.fromhex(source["proof"])
        for changed, hashes, code in ((b"X" + proof[1:], 0, 11),
                                      (proof[:8] + bytes(32) + proof[40:], 1, 12)):
            expected = replay(source | {"proof": changed.hex()})
            self.assertEqual(len(expected["trace"]), hashes)
            self.assertEqual(expected["revert"], ("decode", code))
            self.assertEqual(len(expected["precompile_trace"]), 8)

    def test_earlier_group_failure_masks_later_bad_scalar(self):
        expected = replay(fixture(commitment=(0, 2), response=R))
        self.assertEqual(expected["frontier"], "commitment/group-admission")
        self.assertEqual(len(expected["trace"]), 2)
        self.assertEqual(len(expected["precompile_trace"]), 12)
        self.assertEqual(expected["precompile_trace"][-1]["output"], "")
        scalar_stop = replay(fixture(response=R))
        self.assertEqual(scalar_stop["frontier"], "response/scalar-canonicality")
        self.assertEqual(len(scalar_stop["trace"]), 10)
        self.assertEqual(len(scalar_stop["precompile_trace"]), 12)

    def test_identity_equation_keeps_two_msm_then_add(self):
        expected = replay(fixture(None, None, None))
        self.assertIs(expected["decision"], True)
        events = expected["precompile_trace"]
        self.assertEqual([e["kind"] for e in events], ["bls12_g1msm", "bls12_g1msm", "bls12_g1add"])
        self.assertEqual([e["hash_event_frontier"] for e in events], [12] * 3)
        self.assertTrue(all(e["output"] == bytes(128).hex() for e in events))
        self.assertEqual(events[-1]["input"], bytes(256).hex())

    def test_finite_equation_and_trailing_failure_retain_all_calls(self):
        source = fixture(point=scale(G, 3))
        complete = replay(source)
        trailing = replay(source | {"proof": source["proof"] + "00"})
        self.assertIs(complete["decision"], False)
        self.assertEqual(len(complete["precompile_trace"]), 15)
        self.assertEqual([e["hash_event_frontier"] for e in complete["precompile_trace"]],
                         [0] * 8 + [2] * 4 + [12] * 3)
        self.assertEqual(trailing["precompile_trace"], complete["precompile_trace"])
        self.assertEqual(trailing["trace"], complete["trace"])
        self.assertEqual(trailing["revert"], ("decode", 13))


class PhysicalOracleTests(unittest.TestCase):
    def test_mutations_fail_with_same_boolean_and_hashes_on_either_call(self):
        expected = replay(fixture(None, None, None))
        call = {"status": "return", "output": (1).to_bytes(32, "big").hex(),
                "trace": expected["trace"], "precompile_trace": expected["precompile_trace"]}
        execution = {"phase": "runtime", **deepcopy(call), "deployment_precompile_trace": [],
                     "calls": [deepcopy(call), deepcopy(call)]}
        controls = mutation_controls(execution, expected)
        self.assertEqual(len(controls), 18)
        self.assertEqual({c["call"] for c in controls}, {1, 2})
        self.assertTrue(all(c["rejected"] and c["boolean_unchanged"] and c["hashes_unchanged"] for c in controls))

    def test_missing_or_extra_fields_and_missing_carrier_fail(self):
        events = replay(fixture(None, None, None))["precompile_trace"]
        for field in events[0]:
            changed = deepcopy(events)
            del changed[0][field]
            with self.subTest(field=field), self.assertRaises(AssertionError):
                check_precompile_trace(changed, events)
        with self.assertRaises(AssertionError):
            check_precompile_trace([events[0] | {"extra": True}, *events[1:]], events)
        with self.assertRaises(AssertionError):
            check_precompile_trace(None, [])
        with self.assertRaises(AssertionError):
            check_physical_execution({"calls": []}, [])


if __name__ == "__main__":
    unittest.main()
