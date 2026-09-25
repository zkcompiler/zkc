#!/usr/bin/env python3
"""Structured local control, run by the native runtime and by the Lean consumer.

The compiler's own test states how loops and branches are represented and what
is refused. This one states that two further implementations agree about what
the same source computes: the Lean consumer accepts each candidate the compiler
produced and refuses a candidate whose loop bound or dormant branch was changed,
and the runtime and the reference return the same values for every input.

The maintained polynomial-fold example is included because its loop length comes
from an input rather than from a constant, so a fixed-size expansion would pass
the fixture and fail here.
"""
import copy
import json
from pathlib import Path
import random

from journal import Journal
from toolchain import Toolchain, records

# The Lean reference this source is executed by and compared against.
CHECKER = "interactive-protocol"

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests/fixtures"
EXAMPLE = ROOT / "examples/protocols/polynomial-fold.pir"

# Each field the fixture is configured for: its modulus, the portable tag of one
# of its scalars, the tag of a vector of them, and the width one scalar occupies.
FIELDS = [
    ("koala-bear", 2130706433, 19, 20, 4),
    ("bls12-381.fr",
     52435875175126190479447740508185965837690552500527637822603658699938581184513,
     1, 11, 32),
    ("ristretto255.scalar", 2**252 + 27742317777372353535851937790883648493, 13, 14, 32),
]


def wire(tag, payload):
    return ["wire", (b"ZKCV\x01" + bytes([tag]) + payload).hex()]


def walk(body):
    for instruction in body:
        yield instruction
        if instruction[0] == "if":
            yield from walk(instruction[4])
            yield from walk(instruction[5])
        if instruction[0] == "for":
            yield from walk(instruction[7])


def main():
    tools = Toolchain()
    compiler, runtime, checker = tools.compiler, tools.runtime, tools.checker(CHECKER)
    journal = Journal(records())

    def native(mode, value, *flags):
        text = value if isinstance(value, str) else json.dumps(value)
        return json.loads(journal.run([compiler, mode, "-", *flags], text))


    text = (FIXTURES / "local-control.pir").read_text()
    source = native("protocol-source", text)
    plans = [native("protocol-compile", source, *flags)
             for flags in ([], ["--release-storage"])]

    # A constructed protocol keeps its regions; the consumer checks the
    # construction's own source against the candidate compiled from it.
    construction = FIXTURES / "local-control-construction.json"
    descriptor = FIXTURES / "local-control-construction.descriptor.json"
    constructed = json.loads(journal.run([compiler, "protocol-construct", construction, descriptor]))
    constructed_plan = native("protocol-compile", constructed[2])
    journal.run([checker, "--check-generic", journal.write("constructed-source.json", constructed[2]),
         journal.write("constructed-plan.json", constructed_plan)])

    sp = journal.write("source.json", source)
    for plan in plans:
        journal.run([checker, "--check-generic", sp, journal.write("candidate.json", plan)])
    # A well-typed alternate bound changes the computation and must not pass
    # source/candidate correspondence. A dormant branch is checked as well.
    for kind in ("bound", "branch"):
        changed = copy.deepcopy(plans[0])
        body = next(f[4] for f in changed[3] if any(i[0] == "for" for i in f[4]))
        loop = next(i for i in body if i[0] == "for")
        if kind == "bound":
            loop[4] = loop[3]
        else:
            branch = next(i for i in walk(body) if i[0] == "if")
            branch[4], branch[5] = branch[5], branch[4]
        journal.run([checker, "--check-generic", sp, journal.write("bad.json", changed)],
                    refuses="source-local-unmatched")

    rng = random.Random(50117)
    cases = [(0, 0, True), (4, 2, False), (0, 1, True), (2, 7, False)]
    cases += [(rng.randrange(4), rng.randrange(9), bool(rng.randrange(2))) for _ in range(8)]
    for field, modulus, scalar_tag, vector_tag, width in FIELDS:
        variant = text.replace("koala-bear", field)
        sp = journal.write("source.json", native("protocol-source", variant))
        pp = journal.write("candidate.json", native("protocol-compile", variant))
        journal.run([checker, "--check-generic", sp, pp])
        for start, end, enabled in cases:
            x = rng.randrange(modulus)
            expected = x * (pow(2, max(0, end - start), modulus) if enabled
                            else 1 + max(0, end - start)) % modulus
            inputs = [("x", "field:" + field, str(x)), ("enabled", "bool", str(enabled).lower()),
                      ("start", "index", str(start)), ("end", "index", str(end))]
            ref_inputs = ["zkc.reference-inputs/1", "main", "local-control",
                          [["P", [[n, [t, v]] for n, t, v in inputs]]], [], [], []]
            ref = json.loads(journal.run([checker, "--generic-reference", sp,
                                  journal.write("reference.json", ref_inputs)]))
            assert ref[3] == ["returned", [["vector:" + field, [str(expected), str(x)]],
                                           ["index", "2"]]], ref
            supplied = [["x", wire(scalar_tag, x.to_bytes(width, "little"))],
                        ["enabled", wire(5, bytes([enabled]))],
                        ["start", wire(31, start.to_bytes(8, "little"))],
                        ["end", wire(31, end.to_bytes(8, "little"))]]
            actual = json.loads(journal.run([runtime, "run-protocol", sp, pp, journal.write("inputs.json",
                ["zkc.run/2", "main", "local-control", [], [["P", [], supplied, []]], []]),
                checker]))
            assert actual["outcome"][0] == "returned", actual
            values = actual["outcome"][1]["P"]
            payload = bytes.fromhex(values[0][2])
            assert payload[:10] == b"ZKCV\x01" + bytes([vector_tag]) + b"\x02\x00\x00\x00"
            assert [int.from_bytes(payload[i:i + width], "little")
                    for i in range(10, len(payload), width)] == [expected, x]
            assert values[1] == ["index", 2], values

    # The maintained example exercises an input-selected length, not a
    # fixed-size expansion. Compare to integer Horner evaluation.
    example = EXAMPLE.read_text()
    sp = journal.write("source.json", native("protocol-source", example))
    pp = journal.write("candidate.json", native("protocol-compile", example))
    for coefficients, point, negate in [([], 3, False), ([7], 9, True),
                                        ([3, 5, 8, 2], 4, False), (list(range(33)), 7, True)]:
        expected = 0
        for coefficient in coefficients:
            expected = (expected * point + coefficient) % 2130706433
        if negate:
            expected = -expected % 2130706433
        supplied = [["coefficients", wire(20, len(coefficients).to_bytes(4, "little")
                     + b"".join(n.to_bytes(4, "little") for n in coefficients))],
                    ["point", wire(19, point.to_bytes(4, "little"))],
                    ["negate", wire(5, bytes([negate]))]]
        reference_inputs = ["zkc.reference-inputs/1", "main", "local-control", [["P", [
            ["coefficients", ["vector:koala-bear", list(map(str, coefficients))]],
            ["point", ["field:koala-bear", str(point)]],
            ["negate", ["bool", str(negate).lower()]]]]], [], [], []]
        ref = json.loads(journal.run([checker, "--generic-reference", sp,
                              journal.write("reference.json", reference_inputs)]))
        actual = json.loads(journal.run([runtime, "run-protocol", sp, pp, journal.write("inputs.json",
            ["zkc.run/2", "main", "local-control", [], [["P", [], supplied, []]], []]),
            checker]))
        assert ref[3] == ["returned", [["field:koala-bear", str(expected)]]], ref
        assert actual["outcome"] == ["returned", {"P": [["wire", "field",
            wire(19, expected.to_bytes(4, "little"))[1]]]}], actual

    print(json.dumps({"status": "pass", "checks": journal.save()}))



def test_local_control_reference():
    main()

if __name__ == "__main__":
    main()
