#!/usr/bin/env python3
"""Execute frozen R1CS/AIR views and protocol composition in native and Lean.

The native relation generator is tested, not proved. Lean independently runs
its materialized arithmetic; only SHA256 requests use a public hash service.
No Groth16 or relation soundness claim follows from this diagnostic example.
"""
import copy
import hashlib
import json
from pathlib import Path
import shutil

from journal import Journal
from toolchain import Toolchain, records

ROOT = Path(__file__).resolve().parents[2]
F = "bn254.fr"
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def wire(kind, value):
    def le(n, size=32):
        return int(n).to_bytes(size, "little")
    if kind == "vector":
        payload = le(len(value), 4) + b"".join(le(x) for x in value)
        tag = 41
    else:
        rows, cols, entries = value
        payload = le(rows, 4) + le(cols, 4) + le(len(entries), 4)
        payload += b"".join(le(r, 4) + le(c, 4) + le(v) for r, c, v in entries)
        tag = 45
    return (b"ZKCV\x01" + bytes([tag]) + payload).hex()


def strings(value):
    return [strings(x) for x in value] if isinstance(value, list) else str(value)


# The Lean reference these authored relations are compared against.
CHECKER = "interactive-protocol"


def main():
    tools = Toolchain()
    compiler, runtime = tools.compiler, tools.runtime
    checker = tools.checker(CHECKER)
    output = records()
    cases = []
    journal = Journal(output)

    for coefficient in (1, 2):
        directory = output / f"coefficient-{coefficient}"
        directory.mkdir(exist_ok=True)
        for path in (ROOT / "examples/relations").iterdir():
            if path.suffix in (".pir", ".json"):
                shutil.copyfile(path, directory / path.name)
        relation = directory / "multiply.r1cs.json"
        value = json.loads(relation.read_text())
        value[5][0][0][0][1] = str(coefficient)
        journal.write(relation, value)
        snapshot = journal.write(directory / "snapshot.json", journal.json([compiler, "protocol-resolve", directory / "composition.pir"]))
        original = snapshot.read_bytes()
        # Frozen dependencies have no subsequent filesystem dependency.
        relation.unlink()
        source = journal.write(directory / "source.json", journal.json([compiler, "protocol-materialize", snapshot]))
        plan = journal.write(directory / "plan.json", journal.json([compiler, "protocol-compile", source]))
        journal.json([checker, "--check-generic", source, plan])
        data = journal.json([compiler, "protocol-relation-data", snapshot, "Rows"])
        assert data[:3] == ["zkc.relation-matrices/1", "Rows", "Circuit"]
        matrices = data[4]
        base = {name: ("matrix", m) for name, m in zip(("a", "b", "c"), matrices, strict=True)}
        base.update({"first": ("vector", [15 * coefficient]), "second": ("vector", [30]),
                     "witness": ("vector", [3, 5]), "initial": ("vector", [2]),
                     "trace": ("vector", [2, 4, 16])})
        for label in ("valid", "wrong-public", "wrong-witness", "wrong-trace", "short-witness", "crossed-matrix"):
            inputs = copy.deepcopy(base)
            if label == "wrong-public":
                inputs["first"][1][0] += 1
            elif label == "wrong-witness":
                inputs["witness"][1][0] += 1
            elif label == "wrong-trace":
                inputs["trace"][1][1] += 1
            elif label == "short-witness":
                inputs["witness"][1].pop()
            elif label == "crossed-matrix":
                inputs["a"][1][2][0][2] = str(3 - coefficient)
            native = [[name, ["wire", wire(kind, value)]] for name, (kind, value) in inputs.items()]
            logical = [[name, [kind + ":" + F, strings(value)]] for name, (kind, value) in inputs.items()]
            np = journal.write(directory / (label + "-native-inputs.json"), ["zkc.run/2", "main", "relation-views", [], [["P", [], native, []]], []])
            reference_input = ["zkc.reference-inputs/1", "main", "relation-views", [["P", logical]], [], [], []]
            rp = directory / (label + "-lean-inputs.json")
            for _ in range(4):
                journal.write(rp, reference_input)
                ref = journal.json([checker, "--generic-reference", source, rp])
                if ref[3][0] != "pending-primitive":
                    break
                request = ref[4][-1][1]
                assert request[:2] == ["zkc.hash/1", "sha256"], request
                reference_input[5].append([request, ["ok", hashlib.sha256(bytes.fromhex(request[2])).hexdigest()]])
            else:
                raise AssertionError("unexpected extra primitive requests")
            actual = journal.json([runtime, "run-protocol", source, plan, np, checker])
            journal.write(directory / (label + "-lean.json"), ref)
            journal.write(directory / (label + "-native.json"), actual)
            if label in ("short-witness", "crossed-matrix"):
                assert ref[3][:2] == ["reject", "require"] and actual["outcome"][0] == "stopped", (label, ref, actual)
                outcome = "refused"
            else:
                x, y = inputs["witness"][1]
                t0, t1, t2 = inputs["trace"][1]
                expected = [[(coefficient*x*y - inputs["first"][1][0]) % P],
                            [(2*x*y - 30) % P],
                            [(t1-t0*t0) % P, (t2-t1*t1) % P, 0]]
                assert ref[3] == ["returned", [["vector:"+F, strings(v)] for v in expected]], (label, ref[3], expected)
                assert actual["outcome"] == ["returned", {"P": [["wire", "vector", wire("vector", v)] for v in expected]}], (label, actual)
                outcome = "returned"
            cases.append({"coefficient": coefficient, "case": label, "outcome": outcome})
        assert snapshot.read_bytes() == original
    report = {"status": "passed", "checks": journal.save(), "cases": cases,
              "scope": "native generated-view composition vs independent Lean arithmetic and explicit integer expectations",
              "trusted": ["SHA256", "native relation materialization tested, not proved"],
              "no_claims": ["cryptographic security", "external source compiler adequacy"]}
    journal.write(output / "report.json", report)
    print(json.dumps(report, indent=2))



def test_relation_authoring():
    main()

if __name__ == "__main__":
    main()
