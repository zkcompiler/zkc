#!/usr/bin/env python3
"""Bounded structural mutation comparison of independent source admission."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import random

from journal import Journal
from toolchain import Toolchain, records


# The four admitted sources this compares the two implementations on. Two are
# maintained examples and two are the compiler's own fixtures, so each says
# where it lives rather than a single directory standing for both. Every one of
# them is a source both implementations admit: the mutations are interesting
# because a neighbour of an admitted source can stop being one, and a
# neighbourhood of something already refused mostly stays refused.
FAMILIES = (
    ("two-factor", "examples/protocols"),
    ("group-exchange", "examples/protocols"),
    ("construction-derived", "tests/fixtures"),
    ("construction-nested", "tests/fixtures"),
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def locations(value, prefix=()):
    yield prefix
    if isinstance(value, list):
        for index, child in enumerate(value):
            yield from locations(child, (*prefix, index))


def get(value, path):
    for index in path:
        value = value[index]
    return value


def mutated(source, path, mode):
    source = deepcopy(source)
    old = get(source, path)
    if mode == "replace":
        new = "unknown" if isinstance(old, str) else []
    elif mode == "kind":
        new = [] if isinstance(old, str) else "invalid"
    elif isinstance(old, list) and mode == "duplicate" and old:
        new = old + [deepcopy(old[0])]
    elif isinstance(old, list) and mode == "delete" and old:
        new = old[:-1]
    else:
        new = None  # JSON null must be refused by the portable grammar.
    if not path:
        return new
    get(source, path[:-1])[path[-1]] = new
    return source


# The Lean reference whose admission decision is compared against the compiler's.
CHECKER = "interactive-protocol"


def main():
    resolver = Toolchain()
    root = Path(__file__).resolve().parents[2]
    compiler = resolver.compiler
    checker = resolver.checker(CHECKER)
    journal = Journal(records())
    out = journal.directory
    tools = {"compiler": compiler, "lean": checker}
    pins = {name: digest(path) for name, path in tools.items()}
    rows = []
    random_source = random.Random(20260914)
    for name, directory in FAMILIES:
        source = json.loads((root / directory / (name + ".json")).read_text())
        paths = list(locations(source))
        # Retain valid controls, then a fixed finite mutation budget per family.
        cases = [("original", (), source)]
        for index in range(64):
            path = random_source.choice(paths)
            mode = ("replace", "kind", "duplicate", "delete")[index % 4]
            cases.append((f"{index}-{mode}", path, mutated(source, path, mode)))
        for label, path, candidate in cases:
            stem = name + "-" + label
            fixture = out / (stem + ".json")
            fixture.write_text(json.dumps(candidate, separators=(",", ":")) + "\n")
            results = {}
            for tool, mode in (("compiler", "protocol-admit"), ("lean", "--declarations")):
                command = [str(tools[tool]), mode, str(fixture)]
                proc = journal.attempt(command)
                results[tool] = {"command": command, "exit": proc.returncode,
                                 "stdout": proc.stdout, "stderr": proc.stderr}
            accepted = {k: v["exit"] == 0 for k, v in results.items()}
            passed = accepted["compiler"] == accepted["lean"] and all(
                r["exit"] in (0, 1) for r in results.values())
            if label == "original":
                passed = passed and all(accepted.values())
            rows.append({"case": stem, "path": path, "sha256": digest(fixture),
                         "passed": passed, "results": results})
    unchanged = all(digest(tools[name]) == pin for name, pin in pins.items())
    failures = sum(not row["passed"] for row in rows)
    report = {"scope": "260 bounded declaration admission controls; no execution, exhaustive grammar coverage or checker soundness claim",
              "seed": 20260914, "pins": pins, "unchanged_tools": unchanged,
              "checks": rows, "failures": failures, "passed": unchanged and failures == 0}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"checks": len(rows), "failures": failures, "unchanged_tools": unchanged}))
    return int(not report["passed"])



def test_admission_differential():
    assert main() == 0

if __name__ == "__main__":
    raise SystemExit(main())
