#!/usr/bin/env python3
"""The local vocabulary executed by the native runtime and by the Lean consumer.

The compiler's own test states which operations the source admits and which
bindings it refuses. This one runs the admitted source: for every stored
sequence, index, guard and equality outcome, the runtime and the independently
implemented reference must return the same value, refuse in the same place, and
ask the same provider for the same things in the same order.

Curve points enter only as the two canonical constants named below; that a
supplied point is on the curve remains an explicit premise of Lean's group
reference rather than something either side re-derives here.
"""
import itertools
import json
from pathlib import Path

from journal import Journal
from toolchain import Toolchain, records

# The Lean reference this source is executed by and compared against.
CHECKER = "interactive-protocol"

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/local-vocabulary.pir"

# Each group the fixture is configured for, with the portable tags of one of its
# points and of a sequence of them, and the canonical identity and generator.
GROUPS = [
    ("bls12-381.g1", 9, 10, b"\xc0" + bytes(47),
     bytes.fromhex("97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac58"
                   "6c55e83ff97a1aeffb3af00adb22c6bb")),
    ("ristretto255.group", 16, 17, bytes(32),
     bytes.fromhex("e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76")),
]


def main():
    tools = Toolchain()
    compiler, runtime, checker = tools.compiler, tools.runtime, tools.checker(CHECKER)
    journal = Journal(records())

    base = FIXTURE.read_text()
    for group, point_tag, sequence_tag, identity, generator in GROUPS:
        source = base.replace("bls12-381.g1", group)
        admitted = json.loads(journal.run([compiler, "protocol-source", "-"], source))
        candidate = json.loads(journal.run([compiler, "protocol-compile", "-"], source))

        sp = journal.write("source.json", admitted)
        pp = journal.write("candidate.json", candidate)
        journal.run([checker, "--check-generic", sp, pp])

        def point(value):
            return (b"ZKCV\x01" + bytes([point_tag]) + value).hex()

        def sequence(xs):
            return (b"ZKCV\x01" + bytes([sequence_tag])
                    + len(xs).to_bytes(4, "little") + b"".join(xs)).hex()

        for xs, query, enabled, equal in itertools.product(
                ([], [generator], [generator, identity, generator]),
                (0, 1, 2, 2**64 - 1), (False, True), (False, True)):
            target = xs[query] if query < len(xs) else identity
            if not equal:
                target = identity if target == generator else generator
            public = [("batch", "groups:" + group, sequence(xs)),
                      ("query", "index", str(query)),
                      ("expected", "group:" + group, point(target)),
                      ("enabled", "bool", str(enabled).lower())]
            reference = ["zkc.reference-inputs/1", "main", "local-vocabulary",
                         [["V", [[n, [ty, value]] for n, ty, value in public]]], [], [], []]

            def reference_run():
                return json.loads(journal.run([checker, "--generic-reference", sp,
                                       journal.write("reference.json", reference)]))

            ref = reference_run()
            while ref[3][0] == "pending-primitive":
                request = ref[4][-1][1]
                assert request[2] in ("validate", "curve.equal"), request
                if request[2] == "validate":
                    # Only the two canonical points named above enter.
                    reply = []
                else:
                    assert query < len(xs)
                    reply = [["bool", str(equal).lower()]]
                reference[5].append([request, ["ok", reply]])
                ref = reference_run()
            wire_index = (b"ZKCV\x01\x1f" + query.to_bytes(8, "little")).hex()
            wire_bool = (b"ZKCV\x01\x05" + bytes([enabled])).hex()
            native = ["zkc.run/2", "main", "local-vocabulary", [], [["V", [], [
                ["batch", ["wire", sequence(xs)]], ["query", ["wire", wire_index]],
                ["expected", ["wire", point(target)]], ["enabled", ["wire", wire_bool]]],
                []]], []]
            actual = json.loads(journal.run([runtime, "run-protocol", sp, pp,
                                     journal.write("inputs.json", native), checker]))
            requests = [e[1][2] for e in ref[4] if e[0] == "request"]
            if query >= len(xs):
                assert ref[3][:2] == ["refused", "group-index"], ref
                assert actual["outcome"][0] == "stopped", actual
                assert "group-index" in json.dumps(actual), actual
                assert requests == ["curve.length", "curve.get"], requests
            else:
                assert ref[3] == ["returned", [["bool", str(not enabled or equal).lower()],
                                               ["index", str(len(xs))]]], ref
                assert actual["outcome"] == ["returned", {"V": [
                    ["bool", not enabled or equal], ["index", len(xs)]]}], actual
                assert requests == ["curve.length", "curve.get", "curve.equal",
                                    "bool.not", "bool.or"], requests
    print(json.dumps({"status": "pass", "checks": journal.save()}))



def test_local_vocabulary_reference():
    main()

if __name__ == "__main__":
    main()
