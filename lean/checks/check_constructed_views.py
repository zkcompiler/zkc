#!/usr/bin/env python3
"""Check generated constructed views and kernel refusal of stale structural proofs.

Run through ``lake env python3``. This driver only schedules Lean, compares its
printed syntax and mutates syntax; it does not interpret program instructions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROLES = (
    "SmallSumcheckProducer",
    "SmallSumcheckValidator",
    "TwoSumsProducer",
    "TwoSumsValidator",
)


def change_action(text: str, action: str, transform) -> str:
    lines = text.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if f"(View.{action} " not in line:
            continue
        changed = transform(line)
        if changed != line:
            lines[index] = changed
            return "".join(lines)
    raise AssertionError(f"mutation did not select {action}")


def change_return(text: str) -> str:
    pattern = r"(def returned : List Nat := \(\[)([0-9, ]+)(\]\))"

    def replacement(match: re.Match[str]) -> str:
        values = [int(value) for value in match[2].split(",")]
        changed = list(reversed(values)) if len(values) > 1 else [values[0] + 1]
        return match[1] + ", ".join(map(str, changed)) + match[3]

    changed, count = re.subn(pattern, replacement, text, count=1)
    assert count == 1 and changed != text
    return changed


def change_yields(line: str) -> str:
    pattern = r"(View.loop [0-9]+ \(\[)([0-9, ]+)(\]\))"
    return re.sub(pattern, lambda m: m[1] + ", ".join(reversed(m[2].split(", "))) + m[3], line, count=1)


def change_slot_frame(text: str) -> str:
    lines = text.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if "SlotInputs : List ValueSort :=" in line:
            before, after = line.rsplit('Ty.vector "bls12-381.fr"', 1)
            lines[index] = before + 'Ty.field "bls12-381.fr"' + after
            return "".join(lines)
    raise AssertionError("mutation did not select loop slot frame")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", type=Path)
    parser.add_argument("--records", type=Path)
    options = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    if options.overlay:
        env["LEAN_PATH"] = str(options.overlay.resolve()) + os.pathsep + env.get("LEAN_PATH", "")
    directory = options.records or Path(tempfile.mkdtemp(prefix="zkc-constructed-views-"))
    directory.mkdir(parents=True, exist_ok=True)
    regenerated = directory / "regenerated"
    regenerated.mkdir(exist_ok=True)
    result = subprocess.run(
        ["lean", "--run", "checks/RunGenerators.lean", "constructed", str(regenerated)],
        cwd=root, env=env, text=True, capture_output=True, timeout=120,
    )
    (directory / "regenerate.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, "Lean syntax generation failed; see regenerate.log"
    originals: dict[str, str] = {}
    receipts = []
    for role in ROLES:
        path = root / "ZkcExamples/Structured/Generated/Constructed" / f"{role}.lean"
        text = path.read_text()
        assert text == (regenerated / path.name).read_text(), f"stale generated view: {role}"
        imports = re.findall(r"^public import (.+)$", text, re.MULTILINE)
        assert len(imports) == 2 and imports[1] == "Zkc.Construction.DomainBinding"
        assert imports[0] in {
            "ZkcExamples.Construction.Generated.SmallSumcheckPair",
            "ZkcExamples.Construction.Generated.TwoSumsPair",
        }
        assert not re.search(r"\bDomain\.(?:evaluate|step)\b", text)
        assert not re.search(r":=\s*(?:\([^\n]*\s)?Domain\.participant\b", text)
        assert "sourceImported" not in text and "protocol1Role" not in text
        originals[role] = text
        receipts.append({"role": role, "sha256": hashlib.sha256(text.encode()).hexdigest()})

    cases = [
        ("producer-same-typed-operands", "SmallSumcheckProducer", lambda s: change_action(
            s, "helper", lambda line: line.replace("([0, 1, 3])", "([0, 3, 1])", 1))),
        ("producer-helper-name", "SmallSumcheckProducer", lambda s: change_action(
            s, "helper", lambda line: line.replace('("zkl_', '("changed_zkl_', 1))),
        ("producer-deleted-send", "TwoSumsProducer", lambda s: change_action(
            s, "send", lambda _: "  View.empty\n")),
        ("producer-deleted-guard", "TwoSumsProducer", lambda s: change_action(
            s, "guard", lambda _: "  View.empty\n")),
        ("validator-message-origin", "SmallSumcheckValidator", lambda s: change_action(
            s, "observe", lambda line: line.replace('["message",', '["changed-message",', 1))),
        ("validator-query-site", "TwoSumsValidator", lambda s: change_action(
            s, "challenge", lambda line: line.replace('"label_6368616c6c656e6765"', '"changed-query-site"', 1))),
        ("validator-reply-domain", "TwoSumsValidator", lambda s: change_action(
            s, "receive", lambda line: line.replace('"bls12-381.fr"', '"other-field"', 1))),
        ("validator-deleted-guard", "SmallSumcheckValidator", lambda s: change_action(
            s, "guard", lambda _: "  View.empty\n")),
        ("producer-loop-bound", "TwoSumsProducer", lambda s: change_action(
            s, "loop", lambda line: line.replace("View.loop 4 ", "View.loop 3 ", 1))),
        ("validator-loop-yields", "TwoSumsValidator", lambda s: change_action(s, "loop", change_yields)),
        ("producer-private-return", "SmallSumcheckProducer", change_return),
        ("validator-output-order", "TwoSumsValidator", change_return),
        ("validator-loop-slot-frame", "SmallSumcheckValidator", change_slot_frame),
        ("validator-checkpoint-erasure", "SmallSumcheckValidator", lambda s: change_action(
            s, "sequence", lambda line: line.replace(
                "(View.sequence ", "((fun first rest env => (first env).bind rest) ", 1))),
    ]
    mutations = []
    for name, role, transform in cases:
        mutated = transform(originals[role])
        assert mutated != originals[role], name
        path = directory / f"{name}.lean"
        path.write_text(mutated)
        result = subprocess.run(
            ["lean", "-DwarningAsError=true", str(path)],
            cwd=root, env=env, text=True, capture_output=True, timeout=120,
        )
        log = result.stdout + result.stderr
        (directory / f"{name}.log").write_text(log)
        assert result.returncode != 0, f"stale proof accepted mutation: {name}"
        refused = "Type mismatch" in log or (name == "validator-loop-slot-frame" and
                                            "declaration type mismatch" in log)
        assert refused, f"mutation did not fail at its proof equation: {name}"
        assert "unexpected token" not in log and "object file" not in log, name
        mutations.append({"name": name, "role": role, "status": "kernel-equation-refused"})
        print(f"PASS {name}", flush=True)
    report = {"format": "zkc.constructed-view-controls/0", "generated": receipts, "mutations": mutations}
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS {len(receipts)} regenerated views; {len(mutations)} stale structural proofs refused")


if __name__ == "__main__":
    main()
