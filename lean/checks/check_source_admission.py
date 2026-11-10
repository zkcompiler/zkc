#!/usr/bin/env python3
"""Compare admitted source execution with the independent native SSA reader.

This checks the maintained interpreter profile, including failures and ordered
service replies. It does not generate source proofs or certify native lowering.
Budgets are intentionally generous: the two interpreters count different steps.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
from support import lake  # noqa: E402
from support.packages import package_directory  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--reference", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    rows = []
    fixtures = ROOT / "compiler/test/fixtures/structured-source"
    ir = package_directory("ir")
    executable = ir / ".lake/build/bin/structured-source"
    summary = {"coverage": "admission-and-scripted-source-execution", "cases": rows,
               "source_proof": False, "native_lowering_proof": False}

    def run(command, *, label, cwd=ROOT, refused=False):
        # A signal, timeout or missing tool is never a successful refusal.
        process = subprocess.run(list(map(str, command)), cwd=cwd, capture_output=True,
                                 text=True, timeout=180)
        (output / f"{label}.stdout").write_text(process.stdout)
        (output / f"{label}.stderr").write_text(process.stderr)
        valid_exit = process.returncode == 1 if refused else process.returncode == 0
        if not valid_exit:
            raise ValueError(f"{label}: unexpected exit {process.returncode}; see {output}")
        if refused:
            diagnostic = json.loads(process.stdout)
            if (diagnostic.get("status") != "refused" or
                    not isinstance(diagnostic.get("code"), str) or
                    diagnostic["code"].endswith("-io")):
                raise ValueError(f"{label}: not a semantic admission refusal")
        return process.stdout

    def write(name, value):
        path = output / name
        path.write_text(json.dumps(value, separators=(",", ":")) + "\n")
        return path

    def prepare(name, path, symbol):
        text = run([args.compiler, "protocol-structured", path, f"--symbol={symbol}"], label=name + "-export")
        snapshot = json.loads(text)
        snapshot_path = write(name + "-source.json", snapshot)
        result = json.loads(run([executable, "check", snapshot_path], label=name + "-admission"))
        if result != ["checked", snapshot[2], symbol]:
            raise ValueError(f"{name}: admission selected a different source")
        rows.append({"name": name + "-admission", "status": "pass",
                     "source_sha256": hashlib.sha256(text.encode()).hexdigest()})
        return snapshot, snapshot_path

    def check_quoted(entry, data):
        quoted = ROOT / "lean/verification/Zkc/Tests/Verification/Construction" / f"{entry}Source.lean"
        literals = [line.removeprefix("import_source actual from ")
                    for line in quoted.read_text().splitlines()
                    if line.startswith("import_source actual from ")]
        if len(literals) != 1 or json.loads(json.loads(literals[0])) != data:
            raise ValueError(f"{entry}: maintained Lean source differs from actual frontend export")
        rows.append({"name": entry + "-proof-source", "status": "pass"})

    def compare(name, source, symbol, snapshot, role, inputs, replies=()):
        request = write(name + "-request.json", ["zkc.structured-open-request/0", role, inputs, list(replies), 1000000])
        native = json.loads(run([args.reference, "open", source, symbol, request], label=name + "-native"))
        formal = json.loads(run([executable, "open", snapshot, request], label=name + "-formal"))
        if native != formal:
            raise ValueError(f"{name}: execution, stop, layout or trace differs; see {output}")
        rows.append({"name": name, "status": "pass", "outcome": formal[1]})

    try:
        for tool in (args.compiler, args.reference):
            if not tool.is_file():
                raise ValueError(f"missing prepared native tool: {tool}")
        run([lake.resolve(args.lake), "build", "structured-source"], cwd=ir, label="build")
        # Actual frontend lowering: helper calls, branches, stops and finite loops.
        source = fixtures / "scoped-control.zkc"
        cases = {
            "Choose": [["7", "11", True], ["7", "11", False]],
            "Replace": [["7", "11", "0"], ["7", "11", "3"]],
            "Require": [["7", True], ["7", False]],
            "Compute": [["7", "11"]],
            "Last": [[["7", "11"], "3", True], [[], "3", True], [["7"], "3", False]],
        }
        for entry, inputs in cases.items():
            flags = ["--source-format=zkc", f"--subject=scoped_control::{entry}",
                     f"--module=scoped_control={source}"]
            original = run([args.compiler, "language-emit", *flags], label=entry + "-lower")
            interface = json.loads(run([args.compiler, "language-interface", *flags], label=entry + "-interface"))
            path = output / f"{entry}.mlir"
            path.write_text(original)
            symbol = interface.get("protocol")
            if not isinstance(symbol, str) or not symbol:
                raise ValueError(f"{entry}: subject interface has no protocol identity")
            data, snapshot = prepare(entry, path, symbol)
            if entry == "Replace":
                check_quoted(entry, data)
            definition = next(row for row in data[7] if row[0] == "function" and row[1] == symbol)
            role = definition[6][1][0]
            for index, values in enumerate(inputs):
                compare(f"{entry}-{index}", path, symbol, snapshot, role, values)
            # A syntactically valid transport cannot name an absent definition.
            changed = deepcopy(data)
            changed[3] = "missing"
            run([executable, "check", write(entry + "-bad-entry.json", changed)],
                label=entry + "-bad-entry", refused=True)
            rows.append({"name": entry + "-bad-entry", "status": "pass", "outcome": "refused"})
        # Current frontend source: repeated calls and actual effectful selected regions.
        source = fixtures / "actual-calls.zkc"
        actual_cases = {
            "Twice": [["7", "11"]],
            "DrawPair": [[False, "17", "17"], [True, "17", "17"]],
            "Nested": [[True, True, "7", "11"], [True, False, "7", "11"],
                       [False, True, "7", "11"], [None, True, "7", "11"]],
            "Select": [[True, "7", "17"], [False, "7", "17"]],
        }
        for entry, inputs in actual_cases.items():
            flags = ["--source-format=zkc", f"--subject=actual_calls::{entry}",
                     f"--module=actual_calls={source}"]
            original = run([args.compiler, "language-emit", *flags], label=entry + "-lower")
            interface = json.loads(run([args.compiler, "language-interface", *flags],
                                       label=entry + "-interface"))
            path = output / f"{entry}.mlir"
            path.write_text(original)
            symbol = interface["protocol"]
            data, snapshot = prepare(entry, path, symbol)
            definition = next(row for row in data[7] if row[0] == "function" and row[1] == symbol)
            role = definition[6][1][0]
            if entry in {"Twice", "DrawPair"}:
                check_quoted(entry, data)
            for index, values in enumerate(inputs):
                compare(f"{entry}-{index}", path, symbol, snapshot, role, values)
            if entry == "DrawPair":
                first = definition[9][1][0][3][0][2][1][0]
                second = definition[9][1][1]
                for right in ["17", "23"]:
                    scripts = [["reply", ["draw", instruction[4], role,
                        "random.bls12-381.fr/0", handle, "bls12-381.fr"], ["value", value]]
                        for instruction, handle, value in [(first, "17", "3"), (second, right, "8")]]
                    compare(f"draw-pair-{right}", path, symbol, snapshot, role,
                            [True, "17", right], scripts)
                    compare(f"draw-pair-wrong-order-{right}", path, symbol, snapshot, role,
                            [True, "17", right], list(reversed(scripts)))
            if entry == "Select":
                selected = definition[9][1][0]
                draw = selected[3][0][2][1][0]
                request = ["draw", draw[4], role, "random.bls12-381.fr/0", "17", "bls12-381.fr"]
                for answer in [["value", "13"], ["stop", "reject"], ["stop", "exhausted"]]:
                    compare(f"selected-service-{answer[1]}", path, symbol, snapshot, role,
                            [True, "7", "17"], [["reply", request, answer]])
                receiver = definition[6][1][1]
                compare("selected-receiver", path, symbol, snapshot, receiver, [True, None, None])
                # Both arms are checked, including one that a concrete input would not select.
                mutations = {
                    "missing-arm": lambda branch: branch[3].pop(),
                    "reordered-labels": lambda branch: branch[0].__setitem__(2, ["else", "then"]),
                    "wrong-selector": lambda branch: branch[1].__setitem__(0, 1),
                    "unknown-output-role": lambda branch: branch[0].__setitem__(3, [["unknown"]]),
                    "bad-unselected-capture": lambda branch: branch[3][1][2].__setitem__(2, ["yield", [99]]),
                    "bad-service-capture": lambda branch: branch[3][0][2][1][0][1].__setitem__(0, 0),
                }
                for name, mutate in mutations.items():
                    changed = deepcopy(data)
                    owner = next(row for row in changed[7] if row[0] == "function" and row[1] == symbol)
                    mutate(owner[9][1][0])
                    run([executable, "check", write(name + ".json", changed)], label=name, refused=True)
                    rows.append({"name": name, "status": "pass", "outcome": "refused"})
        # Ordered requests, aliasing, pending answers and reached service stops.
        source = fixtures / "open-services.mlir"
        _, snapshot = prepare("services", source, "main")
        domain = "bls12-381.fr"
        contract = "random.bls12-381.fr/0"
        first = ["draw", "first", "P", contract, "17", domain]
        second = ["draw", "second", "P", contract, "17", domain]
        scripts = [[], [["reply", first, ["value", "3"]]],
                   [["reply", first, ["value", "3"]], ["reply", second, ["value", "8"]]],
                   [["reply", second, ["value", "8"]]],
                   *[[["reply", first, ["stop", reason]]] for reason in
                     ("abort", "reject", "incomplete", "exhausted", "refused")]]
        for index, script in enumerate(scripts):
            compare(f"services-{index}", source, "main", snapshot, "P", ["17", "17", True], script)
        compare("services-other-role", source, "main", snapshot, "V", [None, None, False])
        summary["status"] = "pass"
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        summary.update(status="fail", error=str(error))
    (output / "result.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key != "cases"} |
                     {"passed": len(rows), "report": str(output / "result.json")}, indent=2))
    raise SystemExit(summary["status"] != "pass")


if __name__ == "__main__":
    main()
