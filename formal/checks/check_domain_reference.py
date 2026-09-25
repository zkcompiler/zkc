#!/usr/bin/env python3
"""Full logical snapshots and physical formation through a selected Lean binary.

Handwritten sources and expected observations are independent of the compiler.
No cryptographic primitive answers or native allocator claims are supplied.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

FORMAL = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FORMAL))
import support.evidence  # noqa: E402

INTERACTIVE = FORMAL / ".lake/build/bin/interactive-protocol"
REPORTS = support.evidence.records("domain-reference")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interactive", type=Path, default=INTERACTIVE)
    parser.add_argument("--output", type=Path, default=REPORTS)
    args = parser.parse_args()
    binary = args.interactive.resolve()
    binary_sha256 = hashlib.sha256(binary.read_bytes()).hexdigest()
    args.output.mkdir(parents=True, exist_ok=True)
    cases = []

    def write(name, value):
        path = args.output / (name + ".json")
        path.write_text(json.dumps(value, indent=2) + "\n")
        return str(path)

    def check(name, mode, source, argument, expected, code=0):
        command = [str(binary), mode, write(name + ".source", source),
                   write(name + ".argument", argument)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=60)
        observed = json.loads(result.stdout)
        write(name + ".observed", observed)
        write(name + ".expected", expected)
        assert (result.returncode, result.stderr, observed) == (code, "", expected), name
        cases.append({"case": name, "command": command, "status": "pass"})

    scope = ["scope", "source-control-and-typed-locals", "tools-joint-schedule/1",
             "external-group-contract", "logical-resources", "external-pcs-contract",
             "external-hash-contract", "no-physical-resource-correspondence",
             "no-elaboration-adequacy-proof"]
    origin = ["source-origin/2", "vector-test", "main", "root",
              [["local", "mask", "Mask"]], "draw", "P", ["Mask", []]]
    for domain in ("bls12-381.fr", "ristretto255.scalar"):
        def ty(kind):
            return kind + ":" + domain
        for name, count, budget, tape in (
            ("empty", 0, 4, [2, 3]), ("one", 1, 4, [2, 3]),
            ("many", 3, 4, [2, 3, 4, 5]), ("empty_zero", 0, 0, []),
            ("budget_short", 3, 2, [2, 3, 4]), ("budget_zero", 1, 0, [2]),
            ("tape_empty", 3, 4, []), ("tape_short", 3, 4, [2]),
        ):
            source = ["zkc.protocol/1", [["draw", "random.vector", [domain], ""]],
                      [["function", "Mask", [["rng", ty("rng")]], [ty("vector"), ty("rng")],
                        [["op", "draw", "draw", [str(count)], ["rng"], ["v", "next"]],
                         ["return", ["v", "next"]]], ["Mask", []]]],
                      [["protocol", "Main", ["P"], [], [["rng", "P", ty("rng")]],
                        [["P", ty("vector")], ["P", ty("rng")]], [],
                        [["local", "mask", "P", "Mask", ["rng"], ["v", "next"]],
                         ["return", ["v", "next"]]]]],
                      [["instance", "root", "Main", [], [], [["P", "P"]]]],
                      [["entry", "main", "root"]]]
            handle = [ty("rng"), ["rng", "0"]]
            initializer = "rng" if domain == "bls12-381.fr" else ty("rng")
            inputs = ["zkc.reference-inputs/1", "main", "vector-test",
                      [["P", [["rng", handle]]]],
                      [["rng", "P", [], str(budget), [initializer, list(map(str, tape))]],
                       ["untouched", "P", [], "11", ["rng", ["19"]]]], [], []]
            request = ["zkc.reference-primitive/2", origin, "random.vector",
                       [domain], [str(count)], [handle]]
            transitioned = budget >= count
            events = [["request", request]]
            if not transitioned:
                outcome = ["exhausted", "resource-budget", origin]
            elif len(tape) < count:
                outcome = ["exhausted", "test-tape", origin]
            else:
                values = [[ty("vector"), list(map(str, tape[:count]))], [ty("rng"), ["rng", "1"]]]
                outcome = ["returned", values]
                events.append(["response", request, values])
            resources = [["rng", "P", [], "1" if transitioned else "0",
                          str(count if transitioned else 0), str(budget - count if transitioned else budget), "rng"],
                         ["untouched", "P", [], "0", "0", "11", "rng"]]
            expected = ["zkc.reference-observation/1", "main", "joint", outcome, events, resources, "0", scope]
            check(domain + "." + name, "--generic-reference", source, inputs, expected)

    checked = ["checked", "generic-structural-correspondence", "no-elaboration-adequacy-proof"]
    for group in (False, True):
        field = "ristretto255.scalar" if group else "bls12-381.fr"
        value = "groups:ristretto255.group" if group else "vector:" + field
        scalar = "group:ristretto255.group" if group else "field:" + field
        vector = "vector:" + field
        domain = "ristretto255.group" if group else field
        contracts = ["curve.scale_each", "curve.msm"] if group else ["vector.mul", "vector.dot"]
        prefix = "dalek" if group else "arkworks"
        reps = {vector: "dalek.scalar-vector/1" if group else "arkworks.fr-vector/1",
                value: "dalek.ristretto-vector/1" if group else "arkworks.fr-vector/1",
                scalar: "dalek.ristretto/1" if group else "arkworks.fr/1"}
        ports = [["f", vector], ["v", value], ["w", vector]]
        body = [["op", "multiply", "mul", [], ["f", "v"], ["d"]],
                ["op", "contract", "dot", [], ["w", "d"], ["z"]],
                ["op", "contract2", "dot", [], ["f", "d"], ["z2"]], ["return", ["z", "z2"]]]
        bindings = [[name, contract, [domain], ""] for name, contract in zip(("mul", "dot"), contracts)]
        source = ["zkc.protocol/1", bindings, [["function", "Pair", ports, [scalar, scalar], body, ["Pair", []]]],
                  [["protocol", "Main", ["P"], [], [[n, "P", t] for n, t in ports],
                    [["P", scalar], ["P", scalar]], [],
                    [["local", "pair", "P", "Pair", ["f", "v", "w"], ["z", "z2"]], ["return", ["z", "z2"]]]]],
                  [["instance", "root", "Main", [], [], [["P", "P"]]]], [["entry", "main", "root"]]]
        def physical(ty):
            return ty + "@" + reps[ty]
        candidate = ["zkc.participants/1",
                     [[n, c, a, prefix + "-diagonal/" + c] for n, c, a, _ in bindings], "physical",
                     [["function", "Pair", [[n, physical(t)] for n, t in ports],
                       [physical(scalar)] * 2, body, ["Pair", []]]],
                     [["participant", "p", "root", "P", [], [[n, physical(t)] for n, t in ports],
                       [physical(scalar)] * 2, [["local", "pair", "Pair", ["f", "v", "w"], ["z", "z2"]],
                                                ["return", ["z", "z2"]]]]], [["entry", "main", [["P", "p"]]]]]
        check(domain + ".shared", "--check", source, candidate, checked)
        for name in ("bad_second_use", "nested", "escape", "domain"):
            bad = copy.deepcopy(candidate)
            if name == "bad_second_use":
                bad[3][0][4][2][4] = ["d", "f"]
                error = "binding-operation-signature"
            elif name == "nested":
                bad[3][0][4].insert(1, ["op", "nested", "mul", [], ["f", "d"], ["e"]])
                error = "binding-operation-signature"
            elif name == "escape":
                diagonal = value + "@" + ("dalek.ristretto-diagonal/1" if group else "arkworks.fr-diagonal/1")
                bad[3][0][3] = [diagonal]
                bad[3][0][4][-1] = ["return", ["d"]]
                error = "diagonal-boundary"
            else:
                bad[3][0][2][0][1] = "vector:bls12-381.fr@arkworks.fr-vector/1" if group else "vector:ristretto255.scalar@dalek.scalar-vector/1"
                error = "binding-operation-signature"
            check(domain + "." + name, "--check", source, bad, ["refused", error], 1)

    assert hashlib.sha256(binary.read_bytes()).hexdigest() == binary_sha256, "binary changed during controls"
    report = {"binary": str(binary), "sha256": binary_sha256,
              "cases": cases, "count": len(cases), "status": "pass",
              "scope": "complete logical observation snapshots and independent local physical formation; no native execution/accounting theorem"}
    write("results", report)
    print(json.dumps({k: report[k] for k in ("binary", "sha256", "count", "status")}))


if __name__ == "__main__":
    main()
