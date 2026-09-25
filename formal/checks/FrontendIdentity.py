#!/usr/bin/env python3
"""Handwritten Lean identity vectors; no native compiler/Rust normalizer input.

Run after `lake build artifact-reference` from formal or any directory.
The deterministic transcript replies exercise control/framing, not Merlin.
Use --emit DIRECTORY to export the independent differential vectors for Main.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

FORMAL = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FORMAL))
from support.evidence import records  # noqa: E402

EXE = FORMAL / ".lake/build/bin/artifact-reference"
# Per-call input files go under the reports directory, never into the checkout.
SCRATCH = records("frontend-identity")
FR = "bls12-381.fr"
FIELD, RNG = f"field:{FR}", f"rng:{FR}"
SUITE = "merlin3.bls12-381.fr64be/1"
CONFIG = ["zkc.public-configuration/1", [], [], []]
INPUTS = ["zkc.artifact-inputs/1", "", [], [], CONFIG]
ROLES = [["P", "P"], ["V", "V"]]


def ordinary():
    return ["zkc.protocol/1", [
        ["coin", "random.draw", [FR], ""],
        ["eq", "field.equal", [FR], ""],
        ["guard", "control.require", [], ""],
    ], [
        ["function", "Draw", [["rng", RNG]], [FIELD, RNG], [
            ["op", "sample", "coin", [], ["rng"], ["x", "next"]],
            ["return", ["x", "next"]]], ["Draw", []]],
        ["function", "Check", [["value", FIELD]], ["bool"], [
            ["op", "equal", "eq", [], ["value", "value"], ["ok"]],
            ["op", "require", "guard", [], ["ok"], []],
            ["return", ["ok"]]], ["Check", []]],
    ], [["protocol", "Main", ["P", "V"], [], [["coins", "V", RNG]],
         [["V", "bool"], ["V", RNG]], [], [
             ["local", "draw", "V", "Draw", ["coins"], ["challenge", "after"]],
             ["local", "check", "V", "Check", ["challenge"], ["accepted"]],
             ["return", ["accepted", "after"]]]]],
        [["instance", "root", "Main", [], [], ROLES]], [["entry", "main", "root"]]]


def descriptor(callee="Draw", identity="normalized"):
    return ["zkc.construction/1", "main", "P", "V", [],
            ["coins", [[callee, "sample"]]], "0", SUITE, identity]


def expected_ordinary():
    # Independently specified complete seven-field expected tree.
    return ["zkc.protocol-identity/1", ["entry", "main", "root"],
        [["instance", "root", "Main", [], [], ROLES]],
        [["protocol", "Main", ["P", "V"], [], [["coins", "V", RNG]],
          [["V", "bool"], ["V", RNG]], [], [
              ["local", "site0", "V", "Draw", ["v0"], ["v1", "v2"]],
              ["local", "site1", "V", "Check", ["v1"], ["v3"]],
              ["return", ["v3", "v2"]]]]],
        [["function", "Check", [["v0", FIELD]], ["bool"], [
            ["op", "site0", ["operation", "field.equal", [FR]], [], ["v0", "v0"], ["v1"]],
            ["op", "site1", ["operation", "control.require", []], [], ["v1"], []],
            ["return", ["v1"]]], ["Check", []]],
         ["function", "Draw", [["v0", RNG]], [FIELD, RNG], [
            ["op", "site0", ["operation", "random.draw", [FR]], [], ["v0"], ["v1", "v2"]],
            ["return", ["v1", "v2"]]], ["Draw", []]]], [], []]


def generic():
    common = ordinary()
    common[2] = common[2][1:]
    common[3][0][7][0][3] = "Full"
    return ["zkc.library/1", [
        ["generic_function", "GenDraw", [["F", "Field"]], [["Field", ["F"]]],
         [["rng", "rng:F"]], ["field:F", "rng:F"], [
             ["op", "sample", "random.draw", ["F"], [], ["rng"], ["x", "next"]],
             ["return", ["x", "next"]]]]], [
        ["configure", "Full", "Partial", [["F", FR]], []],
        ["configure", "Partial", "GenDraw", [], [["sample", "arkworks/random.draw"]]],
    ], common]


def expected_generic():
    value = expected_ordinary()
    value[3][0][7][0][3] = "Full"
    value[4] = value[4][:1]
    value[5] = [["generic_function", "GenDraw", [["F", "Field"]], [["Field", ["F"]]],
        [["v0", "rng:F"]], ["field:F", "rng:F"], [
            ["op", "site0", "random.draw", ["F"], [], ["v0"], ["v1", "v2"]],
            ["return", ["v1", "v2"]]]]]
    value[6] = [["configure", "Full", "GenDraw", [["F", FR]], []]]
    return value


def nested():
    source = ordinary()
    source[2].append(["function", "Keep", [["x", "bool"]], ["bool"], [["return", ["x"]]], ["Keep", []]])
    protocol = source[3][0]
    protocol[4] += [["public_flag", "V", "bool"], ["extra", "V", "bool"]]
    protocol[7].insert(0, ["loop", "outer", ["constant", "0"], [["flag", "public_flag"]], ["extra"], [
        ["loop", "inner", ["constant", "2"], [["again", "flag"]], ["extra"], [
            ["local", "hidden", "V", "Keep", ["extra"], ["ignored"]],
            ["yield", ["again"]]], ["inner_result"]],
        ["yield", ["inner_result"]]], ["outer_result"]])
    desc = descriptor()
    desc[4] = [["flag", [["V", "public_flag"]]], ["extra", [["V", "extra"]]]]
    return source, desc


def expected_nested_body():
    return [
        ["loop", "site0", ["constant", "0"], [["v0", "v1"]], [["v1", "v2"]], [
            ["loop", "site1", ["constant", "2"], [["v0", "v0"]], [["v1", "v1"]], [
                ["local", "site2", "V", "Keep", ["v1"], ["v2"]],
                ["yield", ["v0"]]], ["v2"]],
            ["yield", ["v2"]]], ["v3"]],
        ["local", "site3", "V", "Draw", ["v0"], ["v4", "v5"]],
        ["local", "site4", "V", "Check", ["v4"], ["v6"]],
        ["return", ["v6", "v5"]]]


def expected_nested():
    value = expected_ordinary()
    value[3][0][4] += [["public_flag", "V", "bool"], ["extra", "V", "bool"]]
    value[3][0][7] = expected_nested_body()
    value[4].append(["function", "Keep", [["v0", "bool"]], ["bool"], [["return", ["v0"]]], ["Keep", []]])
    return value


def receives():
    source = ordinary()
    scheme = "multilinear.kzg.bls12-381/1"
    source[3][0][4] += [["payload", "P", f"commitment:{scheme}"], ["key", "V", f"verifier_key:{scheme}"]]
    source[3][0][7].insert(0, ["message", "receive_alias", "commitment", "P", "V", "payload", "received"])
    # Structural fixture only. No claim that these bytes are valid curve points.
    wire = b"ZKCAR006\1" + (1).to_bytes(8, "little") + b"\7" * 64 + b"\0" * 192
    config = ["zkc.public-configuration/1", [["key", f"verifier_key:{scheme}", wire.hex()]],
              [["P", "payload", "key"]], [["root", "V", "receive_alias", "key"]]]
    return source, config


def expected_receives():
    value = expected_ordinary()
    scheme = "multilinear.kzg.bls12-381/1"
    value[3][0][4] += [["payload", "P", f"commitment:{scheme}"], ["key", "V", f"verifier_key:{scheme}"]]
    value[3][0][7] = [
        ["message", "site0", "commitment", "P", "V", "v1", "v3"],
        ["local", "site1", "V", "Draw", ["v0"], ["v4", "v5"]],
        ["local", "site2", "V", "Check", ["v4"], ["v6"]],
        ["return", ["v6", "v5"]]]
    return value


def encode(value):
    if isinstance(value, str):
        data = value.encode("utf-8")
        return b"\0" + len(data).to_bytes(8, "little") + data
    assert isinstance(value, list)
    return b"\1" + len(value).to_bytes(8, "little") + b"".join(map(encode, value))


def decode(data):
    def read(offset):
        tag = data[offset]
        count = int.from_bytes(data[offset+1:offset+9], "little")
        offset += 9
        if tag == 0:
            return data[offset:offset+count].decode(), offset + count
        assert tag == 1
        result = []
        for _ in range(count):
            value, offset = read(offset)
            result.append(value)
        return result, offset
    value, end = read(0)
    assert end == len(data)
    return value


def command(mode, *values, exe=EXE):
    with tempfile.TemporaryDirectory(dir=SCRATCH) as directory:
        paths = []
        for index, value in enumerate(values):
            path = Path(directory) / str(index)
            path.write_bytes(value if isinstance(value, bytes) else json.dumps(value).encode())
            paths.append(str(path))
        process = subprocess.run([str(exe), mode, *paths], capture_output=True, text=True, timeout=30)
        result = json.loads(process.stdout)
        assert process.returncode in (0, 1), (process.returncode, process.stderr)
        return result


def inspect(source, desc=None, config=None):
    return command("identity", source, desc or descriptor(), *([] if config is None else [config]))


def replay(source, desc, inputs=INPUTS, *, exe=EXE, tail=b""):
    replies = ["zkc.primitive-replies/1", []]
    proof = b""
    for _ in range(32):
        result = command("reference", source, desc, inputs, proof, replies, exe=exe)
        if result[0] == "refused" or result[1][0] != "pending-primitive":
            return result, proof, replies
        request = result[1][2]
        if request[0] == "zkc.hash/1":
            digest = hashlib.sha256(bytes.fromhex(request[2])).hexdigest()
            proof = b"ZKCPRF01" + bytes.fromhex(digest) + tail
            response = digest
        elif request[0] == "zkc.transcript-request/3":
            response = ["ok", "00" * 63 + "07"]
        elif request[0] == "zkc.transcript-request/1":
            response = ["field", (b"ZKCV\1\1" + (7).to_bytes(32, "little")).hex()]
        else:
            raise AssertionError(("unplanned primitive", request))
        replies[1].append([request, response])
    raise AssertionError("reference did not finish")


def replays():
    """The source the replay tests use, with what the current build made of it."""
    source, inputs = ordinary(), copy.deepcopy(INPUTS)
    desc = descriptor(identity="exact")
    actual, proof, replies = replay(source, desc, inputs)
    yield source, desc, inputs, actual, proof, replies


def snapshot_tests(baseline):
    """The comparison with an executable kept from an earlier build.

    The snapshot is not a build output and nothing here can make one: copy the
    executable aside before rebuilding and name it with --baseline. A run that
    names none has nothing to compare, so it contains no such test rather than
    a skipped one.
    """
    class PreservedSnapshotTests(unittest.TestCase):
        def test_a_preserved_snapshot_replays_the_same(self):
            for source, desc, inputs, actual, proof, replies in replays():
                self.assertEqual(
                    command("reference", source, desc, inputs, proof, replies, exe=baseline),
                    actual)
    return PreservedSnapshotTests


class IdentityTests(unittest.TestCase):
    def assertInspection(self, result):
        self.assertEqual(result[0], "zkc.identity-inspection/1", result)
        self.assertEqual(len(result[3]), 7)

    def test_exact_ordinary(self):
        result = inspect(ordinary(), config=CONFIG)
        self.assertInspection(result)
        self.assertEqual(result[3], expected_ordinary())
        self.assertEqual(result[4], CONFIG)
        resolved = ordinary()
        resolved[2][0][4][0][1] = "site0"
        resolved[2][1][4][0][1] = "site0"
        resolved[2][1][4][1][1] = "site1"
        resolved[3][0][7][0][1] = "site0"
        resolved[3][0][7][1][1] = "site1"
        self.assertEqual(result[1], resolved)
        resolved_desc = descriptor()
        resolved_desc[5][1][0][1] = "site0"
        self.assertEqual(result[2], resolved_desc)

    def test_exact_generic_chain(self):
        source = generic()
        result = inspect(source, descriptor("Full"))
        self.assertInspection(result)
        self.assertEqual(result[3], expected_generic())
        self.assertEqual(result[1][2][1][4], [["site0", "arkworks/random.draw"]])
        self.assertEqual(result[1][2][0], source[2][0])
        self.assertEqual(result[2][5], ["coins", [["Full", "site0"]]])

    def test_aliases_choices_permutation_unrelated(self):
        source = ordinary()
        source[1][0] = ["renamed", "random.draw", [FR], "arkworks/random.draw"]
        source[2][0][2][0][0] = "fresh_input"
        source[2][0][4] = [["op", "site1", "renamed", [], ["fresh_input"], ["a", "b"]],
                            ["return", ["a", "b"]]]
        source[3][0][7] = [
            ["local", "site1", "V", "Draw", ["coins"], ["u", "w"]],
            ["local", "site0", "V", "Check", ["u"], ["z"]], ["return", ["z", "w"]]]
        source[2].append(["function", "Unused", [], [], [["return", []]], ["Unused", []]])
        for group in source[1:]:
            group.reverse()
        desc = descriptor()
        desc[5][1][0][1] = "site1"
        result = inspect(source, desc)
        self.assertInspection(result)
        self.assertEqual(result[3], expected_ordinary())
        self.assertEqual(result[2], inspect(ordinary())[2])
        base, proof, replies = replay(ordinary(), descriptor())
        self.assertEqual(base[1][0], "accepted", base)
        self.assertEqual(command("reference", source, desc, INPUTS, proof, replies), base)

    def test_root_and_resolved_runtime(self):
        result, _, _ = replay(ordinary(), descriptor())
        self.assertEqual(result[1][0], "accepted", result)
        resolved_desc = descriptor()
        resolved_desc[5][1][0][1] = "site0"
        root = ["zkc.artifact-binding/1", expected_ordinary(), resolved_desc, "", [], CONFIG]
        self.assertEqual(result[7], encode(root).hex())
        challenge = next(event for event in result[2] if event[0] == "challenge")
        self.assertEqual(decode(bytes.fromhex(challenge[1])), ["zkc.logical-origin/1", "main", "root", [],
            ["challenge", "Main", "site0", "Draw", "site0", "V"]])
        request = next(r for r in result[3] if r[0] == "zkc.transcript-request/3")
        self.assertEqual(request[1:3], [SUITE, "zkc.artifact/1".encode().hex()])
        self.assertEqual(request[3][0], ["append", "binding".encode().hex(), result[7]])

    def retired(self):
        """The current source, inputs and configuration under retired tags.

        Every carrier now holds explicit bindings under one tag; a document
        written under a retired tag is refused rather than read as the old form.
        """
        source = ordinary()
        source[0] = "zkc.protocol/2"
        inputs = copy.deepcopy(INPUTS)
        inputs[0] = "zkc.artifact-inputs/2"
        return source, descriptor(identity="exact"), inputs

    def test_roots_and_replays(self):
        for source, desc, inputs, actual, _, _ in replays():
            self.assertEqual(actual[1][0], "accepted", actual)
            self.assertEqual(decode(bytes.fromhex(actual[7])), [
                "zkc.artifact-binding/1", source, desc, "", [], inputs[4]])

    def test_a_retired_source_tag_is_refused(self):
        # The identity path refuses the tag it reads; the reference cannot
        # load the source as a library or an explicit module, before it reads
        # the inputs.
        source, desc, inputs = self.retired()
        self.assertEqual(inspect(source, desc), ["refused", "identity-source-version"])
        actual, _, _ = replay(source, desc, inputs)
        self.assertEqual(actual, ["refused", "generic-library"])

    def test_guards_origins_static_literals_retained(self):
        source = ordinary()
        source[2][1][4].pop(1)
        changed = inspect(source)
        self.assertInspection(changed)
        self.assertNotEqual(changed[3], expected_ordinary())
        source = ordinary()
        source[2][0][5] = ["Authority", [["F", FR]]]
        changed = inspect(source)
        self.assertInspection(changed)
        self.assertEqual(changed[3][4][1][5], ["Authority", [["F", FR]]])
        source = generic()
        literal = str(52435875175126190479447740508185965837690552500527637822603658699938581184514)
        source[1][0][6].insert(0, ["op", "dead", "field.constant", ["F"], [literal], [], ["unused"]])
        changed = inspect(source, descriptor("Full"))
        self.assertInspection(changed)
        self.assertEqual(changed[3][5][0][6][0][4], [literal])
        source[1][0][6][0][4] = ["1"]
        self.assertNotEqual(inspect(source, descriptor("Full"))[3], changed[3])

    def test_unused_declarations_still_admitted(self):
        source = generic()
        source[1].append(["generic_function", "Unused", [], [], [], [], [["return", []]]])
        result = inspect(source, descriptor("Full"))
        self.assertInspection(result)
        self.assertEqual(result[3], expected_generic())
        source[1][-1][6] = [["op", "bad", "field.add", ["Missing"], [], [], []], ["return", []]]
        self.assertEqual(inspect(source, descriptor("Full"))[0], "refused")
        source = ordinary()
        source[2].append(["function", "Bad", [], ["bool"], [["return", ["missing"]]], ["Bad", []]])
        self.assertEqual(inspect(source)[0], "refused")
        source = generic()
        source[2].append(["configure", "Bad", "GenDraw", [], [["missing", "arkworks/random.draw"]]])
        self.assertEqual(inspect(source, descriptor("Full"))[0], "refused")

    def test_versions_and_bad_references(self):
        source = ordinary()
        source[2][0][5] = []
        self.assertEqual(inspect(source), ["refused", "function-origin"])
        source = ordinary()
        source[3][0][1] = "Draw"
        source[4][0][2] = "Draw"
        # Preparation checks every declared name — bindings, functions,
        # protocols, instances, entries, configurations — and runs before
        # explicit admission, so a protocol that takes a function's name is
        # refused there and never reaches `duplicate-symbol`.
        self.assertEqual(inspect(source), ["refused", "generic-common-name-conflict"])
        source = generic()
        source[3][5][0][0:2] = ["entry", "Full"]
        self.assertEqual(inspect(source, descriptor("Full")),
                         ["refused", "generic-common-name-conflict"])
        for desc in [descriptor() + [[]], descriptor()[:-1], ["zkc.construction/2", *descriptor()[1:]],
                     descriptor(identity="exact"), descriptor(identity="other")]:
            self.assertEqual(inspect(ordinary(), desc)[0], "refused")
        desc = descriptor()
        desc[5][1][0][1] = "missing"
        self.assertEqual(inspect(ordinary(), desc)[0], "refused")
        source = ordinary()
        source[0] = "zkc.protocol/2"
        self.assertEqual(inspect(source), ["refused", "identity-source-version"])
        source = generic()
        source[2][0][3] = []
        self.assertEqual(inspect(source, descriptor("Full")), ["refused", "generic-open-instance"])

    def test_nested_zero_loop_scopes_and_full_body(self):
        source, desc = nested()
        result = inspect(source, desc)
        self.assertInspection(result)
        self.assertEqual(result[3], expected_nested())
        self.assertEqual([f[1] for f in result[3][4]], ["Check", "Draw", "Keep"])
        self.assertEqual(result[1][3][0][7][0][4], ["extra"])
        self.assertEqual(result[1][3][0][7][0][3], [["flag", "public_flag"]])
        source[3][0][7][0][2][1] = "1"
        self.assertNotEqual(inspect(source, desc)[3], result[3])
        source[3][0][7][0][5][0][5][0][4] = ["missing"]
        self.assertEqual(inspect(source, desc)[0], "refused")

    def test_nested_runtime_public_context_and_order(self):
        source, desc = nested()
        inputs = copy.deepcopy(INPUTS)
        inputs[2] = [["flag", "bool", "5a4b4356010501"], ["extra", "bool", "5a4b4356010500"]]
        result, proof, replies = replay(source, desc, inputs)
        self.assertEqual(result[1][0], "accepted", result)
        root = decode(bytes.fromhex(result[7]))
        self.assertEqual(root[4], inputs[2])
        origin = decode(bytes.fromhex(next(e for e in result[2] if e[0] == "challenge")[1]))
        self.assertEqual(origin[4][2], "site3")
        # Root changes include public values, context, and descriptor declaration order.
        for changed_inputs, changed_desc in [
            ([INPUTS[0], "abcd", *copy.deepcopy(inputs[2:])], desc),
            (copy.deepcopy(inputs), desc), (inputs, copy.deepcopy(desc)),
        ]:
            if changed_inputs == inputs and changed_desc is desc:
                changed_inputs[2][0][2] = "5a4b4356010500"
            if changed_desc is not desc:
                changed_desc[4].reverse()
            observation = command("reference", source, changed_desc, changed_inputs, proof, replies)
            self.assertNotEqual(observation[7], result[7])
            self.assertEqual(observation[1][0], "pending-primitive")

    def test_receive_aliases_and_zero_coverage(self):
        source, config = receives()
        result = inspect(source, config=config)
        self.assertInspection(result)
        self.assertEqual(result[3], expected_receives())
        expected = copy.deepcopy(config)
        expected[3][0][2] = "site0"
        self.assertEqual(result[4], expected)
        renamed = copy.deepcopy(source)
        renamed[3][0][7][0][1] = "site8"
        config[3][0][2] = "site8"
        self.assertEqual(inspect(renamed, config=config)[2:], result[2:])
        config[3][0][2] = "missing"
        self.assertEqual(inspect(source, config=config), ["refused", "identity-site-reference"])
        source, config = receives()
        message = source[3][0][7].pop(0)
        source[3][0][7].insert(0, ["loop", "visits", ["constant", "0"], [], ["payload"],
                                      [message, ["yield", []]], []])
        self.assertEqual(inspect(source, config=config), ["refused", "artifact-receive-site-or-duplicate"])
        config[3] = []
        result = inspect(source, config=config)
        self.assertInspection(result)
        self.assertEqual(result[1][3][0][7][0][5][0][1], "site1")

    def test_resolved_setup_configuration_in_root(self):
        source, config = receives()
        inputs = copy.deepcopy(INPUTS)
        inputs[4] = config
        result = command("reference", source, descriptor(), inputs, b"", ["zkc.primitive-replies/1", []])
        self.assertEqual(result[1][0], "pending-primitive", result)
        self.assertEqual(result[1][2][0], "zkc.public-primitive/1")
        root = decode(bytes.fromhex(result[7]))
        expected = copy.deepcopy(config)
        expected[3][0][2] = "site0"
        self.assertEqual(root[5], expected)
        config[1][0][2] = config[1][0][2][:-2] + "01"
        changed = command("reference", source, descriptor(), inputs, b"", ["zkc.primitive-replies/1", []])
        self.assertEqual(changed[1][0], "pending-primitive", changed)
        self.assertNotEqual(changed[7], result[7])

    def test_declared_dependency_closure(self):
        source = ordinary()
        source[2].append(["function", "HiddenLocal", [], [], [["return", []]], ["Unused", []]])
        source[3][0][6] = [["a", "Hidden", []], ["b", "Hidden", []]]
        source[3] += [
            ["protocol", "Hidden", ["P", "V"], [], [], [], [["leaf", "Leaf", []]],
             [["local", "unused_call", "V", "HiddenLocal", [], []], ["return", []]]],
            ["protocol", "Leaf", ["P", "V"], [], [], [], [], [["return", []]]],
            ["protocol", "Excluded", ["P", "V"], [], [], [], [], [["return", []]]],
        ]
        source[4][0][4] = [["a", "shared"], ["b", "shared"]]
        source[4] += [["instance", "shared", "Hidden", [], [["leaf", "leaf"]], ROLES],
                      ["instance", "leaf", "Leaf", [], [], ROLES],
                      ["instance", "excluded", "Excluded", [], [], ROLES]]
        result = inspect(source)
        self.assertInspection(result)
        self.assertEqual([p[1] for p in result[3][2]], ["leaf", "root", "shared"])
        self.assertEqual([p[1] for p in result[3][3]], ["Hidden", "Leaf", "Main"])
        self.assertEqual([f[1] for f in result[3][4]], ["Check", "Draw", "HiddenLocal"])
        for group in source[1:]:
            group.reverse()
        self.assertEqual(inspect(source)[3], result[3])

    def test_repeated_shared_instance_runtime(self):
        source = ordinary()
        source[3][0][1] = "Child"
        source[3].append(["protocol", "Parent", ["P", "V"], [], [["coins", "V", RNG]],
            [["V", "bool"], ["V", RNG]], [["step", "Child", []]], [
                ["call", "first", "step", ["coins"], ["one", "after_one"]],
                ["call", "second", "step", ["after_one"], ["two", "after_two"]],
                ["return", ["two", "after_two"]]]])
        source[4] = [["instance", "root", "Parent", [], [["step", "shared"]], ROLES],
                     ["instance", "shared", "Child", [], [], ROLES]]
        result, _, _ = replay(source, descriptor())
        self.assertEqual(result[1][0], "accepted", result)
        origins = [decode(bytes.fromhex(e[1])) for e in result[2] if e[0] == "challenge"]
        self.assertEqual([o[2] for o in origins], ["shared", "shared"])
        self.assertEqual([o[3] for o in origins], [[["call", "site0", "shared"]], [["call", "site1", "shared"]]])
        self.assertEqual(result[5:7], ["2", "2"])

    def test_polynomial_and_group_clients(self):
        source = generic()
        common = source[3]
        source[1] += [
            ["generic_function", "Fold", [["F", "Field"]], [["CommRing", ["F"]]],
             [["table", "table:F"], ["point", "field:F"]], ["table:F"], [
                 ["op", "fold", "poly.fold", ["F"], [], ["table", "point"], ["result"]],
                 ["return", ["result"]]]],
            ["generic_function", "Group", [["G", "Group"]], [["ScalarAction", ["G"]]], [], ["group:G"], [
                ["op", "gen", "curve.generator", ["G"], [], [], ["generator"]],
                ["return", ["generator"]]]],
        ]
        source[2] += [["configure", "Folded", "Fold", [["F", FR]], [["fold", "arkworks/poly.fold"]]],
                      ["configure", "Generated", "Group", [["G", "bls12-381.g1"]], []]]
        common[3][0][4] += [["table", "P", f"table:{FR}"], ["point", "P", FIELD]]
        common[3][0][7].insert(0, ["loop", "never", ["constant", "0"], [], ["table", "point"], [
            ["local", "fold", "P", "Folded", ["table", "point"], ["unused"]],
            ["local", "group", "P", "Generated", [], ["unused_group"]], ["yield", []]], []])
        result = inspect(source, descriptor("Full"))
        self.assertInspection(result)
        self.assertEqual([d[1] for d in result[3][5]], ["Fold", "GenDraw", "Group"])
        source[2][-2][4][0][1] = "arkworks-msb/poly.fold"
        self.assertEqual(inspect(source, descriptor("Full"))[3], result[3])

    def test_message_framing_and_relabelled_replay(self):
        source = ordinary()
        source[3][0][4].append(["secret", "P", FIELD])
        source[3][0][7].insert(0, ["message", "wire_alias", "field_schema", "P", "V", "secret", "received"])
        wire = b"ZKCV\1\1" + (11).to_bytes(32, "little")
        tail = len(wire).to_bytes(8, "little") + wire
        result, proof, replies = replay(source, descriptor(), tail=tail)
        self.assertEqual(result[1][0], "accepted", result)
        message = next(e for e in result[2] if e[0] == "message")
        self.assertEqual(decode(bytes.fromhex(message[1])), ["zkc.logical-origin/1", "main", "root", [],
            ["message", "Main", "site0", "field_schema", "P", "V"]])
        self.assertEqual(message[2:], [FIELD, wire.hex()])
        self.assertEqual(result[4], str(len(proof)))
        source[3][0][7][0][1] = "other_alias"
        self.assertEqual(command("reference", source, descriptor(), INPUTS, proof, replies), result)

    def test_parameter_order_and_generic_alias_replay(self):
        source = generic()
        source[1][0][2].insert(0, ["K", "Field"])
        source[2][0][3].append(["K", FR])
        result = inspect(source, descriptor("Full"))
        self.assertInspection(result)
        self.assertEqual(result[3][6][0][3], [["K", FR], ["F", FR]])
        before, proof, replies = replay(source, descriptor("Full"))
        self.assertEqual(before[1][0], "accepted", before)
        source[1][0][6][0][1] = "renamed"
        source[2][1][4][0][0] = "renamed"
        desc = descriptor("Full")
        desc[5][1][0][1] = "renamed"
        self.assertEqual(command("reference", source, desc, INPUTS, proof, replies), before)

    def test_carrier_limits_and_native_source_rejection(self):
        for raw, code in [(b"[1e999999]", "non-array-json-token"),
                          (b"[{}]", "non-array-json-token"),
                          (b"[" * 65 + b"]" * 65, "json-depth-limit"),
                          (b" " * 1048577, "byte-limit")]:
            self.assertEqual(command("identity", raw, descriptor()), ["refused", code])
        source = ordinary()
        source[2][1][4][1][1] = "equal"
        self.assertEqual(inspect(source), ["refused", "duplicate-site"])
        source = generic()
        source[2][1][2] = "Full"
        self.assertEqual(inspect(source, descriptor("Full")), ["refused", "generic-configuration-cycle"])


def emit(directory):
    """Write the source, descriptor and expected identity corpus consumed by tests."""
    directory.mkdir(parents=True, exist_ok=True)
    for name, source, desc, expected in [
        ("ordinary", ordinary(), descriptor(), expected_ordinary()),
        ("generic", generic(), descriptor("Full"), expected_generic()),
        ("nested", *nested(), expected_nested()),
        ("receives", receives()[0], descriptor(), expected_receives()),
    ]:
        for suffix, value in [("source", source), ("descriptor", desc), ("normalized", expected)]:
            (directory / f"{name}.{suffix}.json").write_text(json.dumps(value, indent=2) + "\n")
    (directory / "receives.configuration.json").write_text(json.dumps(receives()[1], indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", type=Path)
    parser.add_argument("--baseline", type=Path)
    args, rest = parser.parse_known_args()
    if args.baseline is not None:
        baseline = args.baseline.resolve()
        if not baseline.is_file() or not os.access(baseline, os.X_OK):
            parser.error(f"explicit baseline is not an executable file: {baseline}")
        PreservedSnapshotTests = snapshot_tests(baseline)
    SCRATCH.mkdir(parents=True, exist_ok=True)
    if args.emit:
        emit(args.emit)
    unittest.main(argv=[__file__, *rest])
