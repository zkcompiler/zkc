#!/usr/bin/env python3
"""Actual artifact admission, descriptor roles, correspondence and semantic observations.

The compiler's own public-MSB test states what the compiler alone decides. This
one carries the same subject through the artifact path, where the native runtime
and the independent checker have to agree with it. No mock checker.
"""

import copy
import json
import struct

from construction import compiled, constructed
from journal import Journal
from toolchain import Toolchain, records

# The Lean reference this artifact path is checked against.
def main():
    CHECKER = "interactive-protocol"

    tools = Toolchain()
    compiler, runtime = tools.compiler, tools.runtime
    lean = tools.checker(CHECKER)
    journal = Journal(records())




    def source(producer, validator, shared=False):
        f, g = "ristretto255.scalar", "ristretto255.group"
        vector, groups, point, rng = "vector:" + f, "groups:" + g, "group:" + g, "rng:" + f
        ports = [
            ["w", validator, vector],
            ["p", validator, groups],
            ["expected", validator, point],
            ["coins", validator, rng],
        ]
        body = []
        if shared:
            ports += [["secret", producer, vector], ["bases", producer, groups]]
            body += [
                ["local", "private", producer, "Fold", ["secret", "bases"], ["unused"]]
            ]
        body += [
            ["local", "public", validator, "Fold", ["w", "p"], ["result"]],
            ["local", "check", validator, "Equal", ["result", "expected"], ["ok"]],
            ["return", ["ok", "coins"]],
        ]
        return [
            "zkc.protocol/1",
            [["msm", "curve.msm", [g], ""], ["equal", "curve.equal", [g], ""]],
            [
                [
                    "function",
                    "Fold",
                    [["w", vector], ["p", groups]],
                    [point],
                    [["op", "msm", "msm", [], ["w", "p"], ["q"]], ["return", ["q"]]],
                    ["Fold", []],
                ],
                [
                    "function",
                    "Equal",
                    [["p", point], ["q", point]],
                    ["bool"],
                    [["op", "equal", "equal", [], ["p", "q"], ["ok"]], ["return", ["ok"]]],
                    ["Equal", []],
                ],
            ],
            [
                [
                    "protocol",
                    "Check",
                    [producer, validator],
                    [],
                    ports,
                    [[validator, "bool"], [validator, rng]],
                    [],
                    body,
                ]
            ],
            [
                [
                    "instance",
                    "root",
                    "Check",
                    [],
                    [],
                    [[producer, producer], [validator, validator]],
                ]
            ],
            [["entry", "main", "root"]],
        ]


    def semantic(events):
        # Observed already exports logical source origins, operation contracts and
        # canonical values. Select this semantic event stream, not physical plan
        # bytes or raw implementation-identifying runner traces. Nothing is erased.
        assert "dalek-vartime/curve.msm" not in json.dumps(events)
        assert "dalek/curve.msm" not in json.dumps(events)
        return events


    d = journal.directory
    for producer, validator in [("P", "V"), ("V", "Audit")]:
        original = source(producer, validator)
        desc = [
            "zkc.construction/1",
            "main",
            producer,
            validator,
            [[p, [[validator, p]]] for p in ["w", "p", "expected"]],
            ["coins", []],
            "0",
            "merlin3.ristretto255.scalar64le/1",
            "exact",
        ]
        s = journal.write(d / "source", original)
        descriptor = journal.write(d / "descriptor", desc)
        con, common = constructed(journal, compiler, s, descriptor, f"{d}/")
        baseline = compiled(journal, compiler, common, f"{d}/", name="default")
        selection = journal.write(d / "selections", [["msm", "dalek-vartime/curve.msm"]])
        selected = compiled(journal, compiler, common, f"{d}/", selection, "selected")
        public = [
            [
                "w",
                "vector:ristretto255.scalar",
                (
                    b"ZKCV\1\x0e" + struct.pack("<I", 1) + (2).to_bytes(32, "little")
                ).hex(),
            ],
            [
                "p",
                "groups:ristretto255.group",
                (b"ZKCV\1\x11" + struct.pack("<I", 1) + bytes(32)).hex(),
            ],
            ["expected", "group:ristretto255.group", (b"ZKCV\1\x10" + bytes(32)).hex()],
        ]
        inputs = journal.write(
            d / "inputs",
            [
                "zkc.artifact-inputs/1",
                "00",
                public,
                [],
                ["zkc.public-configuration/1", [], [], []],
            ],
        )
        proof = d / "proof"

        def run(mode, physical, *, error=None, trace="full"):
            return journal.json(
                [
                    runtime,
                    mode + "-artifact",
                    s,
                    descriptor,
                    con,
                    physical,
                    inputs,
                    compiler,
                    lean,
                    proof,
                    "100",
                    "--trace=" + trace,
                ],
                refuses=error,
            )

        run("produce", baseline)
        a = run("validate", baseline)
        b = run("validate", selected)
        assert a["status"] == b["status"] == "accepted"
        assert semantic(a["events"]) == semantic(b["events"])
        for key in ["binding_sha256", "proof_bytes", "messages"]:
            assert a[key] == b[key]
        run("produce", selected)
        run("validate", baseline)
        # Concrete candidate substitution must fail independent correspondence.
        changed = json.loads(selected.read_text())
        changed[3][0][4][0][2] = "equal"
        bad = journal.write(d / "bad", changed)
        run("validate", bad, error="refused")
        # Shared use by a private producer is rejected before input/proof access.
        s = journal.write(d / "source", source(producer, validator, True))
        con, common = constructed(journal, compiler, s, descriptor, f"{d}/")
        selected = compiled(journal, compiler, common, f"{d}/", selection, "selected")
        proof.unlink()
        inputs.unlink()
        report = run("produce", selected, error="artifact-public-implementation-role")
        assert report["phase"] == "admission"
        report = run("validate", selected, error="artifact-public-implementation-role")
        assert report["phase"] == "admission"
        # A missing public binding is never repaired by a role spelling.
        s = journal.write(d / "source", original)
        private_desc = copy.deepcopy(desc)
        private_desc[4] = private_desc[4][1:]
        descriptor = journal.write(d / "descriptor", private_desc)
        con, common = constructed(journal, compiler, s, descriptor, f"{d}/")
        selected = compiled(journal, compiler, common, f"{d}/", selection, "selected")
        report = run("validate", selected, error="artifact-unbound-verifier-input")
        assert report["phase"] == "admission"
    print(f"public MSM artifact controls passed: {journal.save()} commands")



def test_public_msm_artifact():
    main()


if __name__ == "__main__":
    main()
