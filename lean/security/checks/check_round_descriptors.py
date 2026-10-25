#!/usr/bin/env python3
"""Check Lean-owned round regeneration and kernel refusal of stale descriptors.

Run with ``lake env python3 checks/check_round_descriptors.py --overlay PATH``.
The overlay supplies privately compiled dependencies. This driver only schedules
Lean, compares emitted bytes, and mutates Lean syntax; it never parses an AST.
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


ROOTS = ("SmallSumcheck", "TwoSums")


def replace_once(text: str, before: str, after: str) -> str:
    assert before in text and before != after, before
    return text.replace(before, after, 1)


def body_instruction(text: str, role: str, action: int, fields: str) -> str:
    prefix = f"abbrev {role}Loop := "
    line = next(line for line in text.splitlines() if line.startswith(prefix))
    replacement = (
        f"def {role}Loop : Zkc.Construction.Instruction :=\n"
        f"  let retained := {line[len(prefix):]}\n"
        f"  {{ retained with body := retained.body.modify {action} "
        f"(fun instruction => {{ instruction with {fields} }}) }}"
    )
    return replace_once(text, line, replacement)


def through_theorem(text: str, theorem: str) -> str:
    """Retain the exact selected equation and its preceding definitions.

    Later theorems cannot add evidence to a rejected equation. Omitting them
    keeps negative checks focused and avoids cascading elaboration failures.
    """
    namespace = re.search(r"^namespace (.+)$", text, re.MULTILINE)[1]
    start = text.index(f"\ntheorem {theorem}")
    end = text.index("\n\n", start)
    return text[:end] + f"\n\nend round0\n\nend {namespace}\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", type=Path)
    parser.add_argument("--records", type=Path)
    options = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    records = options.records or Path(tempfile.mkdtemp(prefix="zkc-round-descriptors-"))
    records.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, LEAN_NUM_THREADS="2")
    if options.overlay:
        environment["LEAN_PATH"] = str(options.overlay.resolve()) + os.pathsep + environment.get("LEAN_PATH", "")

    def run(name: str, arguments: list[str]) -> subprocess.CompletedProcess[str]:
        result = subprocess.run(
            ["lean", "-DwarningAsError=true", *arguments], cwd=root, env=environment,
            text=True, capture_output=True, timeout=180,
        )
        (records / f"{name}.log").write_text(result.stdout + result.stderr)
        return result

    regenerated = records / "regenerated"
    result = run("regenerate", ["--run", "checks/RunRoundDescriptors.lean", str(regenerated)])
    assert result.returncode == 0, "Lean regeneration failed; see regenerate.log"
    texts = {}
    outputs = []
    for name in ROOTS:
        relative = Path("ZkcSecurity/Examples/Generated/Components") / f"{name}Rounds.lean"
        original = (root / relative).read_text()
        assert original == (regenerated / relative).read_text(), f"stale output: {name}"
        texts[name] = original
        result = run(f"strict-{name}", ["-R", str(regenerated), str(regenerated / relative)])
        assert result.returncode == 0, f"strict generated module failed: {name}"
        outputs.append({"root": name, "sha256": hashlib.sha256(original.encode()).hexdigest(),
                        "bytes": len(original.encode()), "lines": len(original.splitlines())})

    controls = [
        ("capture-prefix", "SmallSumcheck", lambda text: replace_once(text, "capture := 13", "capture := 14")),
        ("producer-same-typed-yields", "SmallSumcheck", lambda text: replace_once(
            text, "yielded := [34, 35, 36, 37, 33]", "yielded := [34, 36, 35, 37, 33]")),
        ("validator-yields", "TwoSums", lambda text: replace_once(
            text, "yielded := [28, 33, 27]", "yielded := [33, 28, 27]")),
        ("loop-source-site", "SmallSumcheck", lambda text: replace_once(
            text, 'site := "apply_18_label_726564756365_s15"', 'site := "wrong-source-repeat"')),
        ("loop-maximum", "TwoSums", lambda text: replace_once(text, "maximum := 4", "maximum := 3")),
        ("loop-same-typed-inputs", "SmallSumcheck", lambda text: replace_once(
            text, "operands := [1, 4, 5, 6, 12, 2]", "operands := [1, 4, 6, 5, 12, 2]")),
        ("same-typed-body-operands", "SmallSumcheck", lambda text: body_instruction(
            text, "producer", 0, "operands := [14, 16, 15]")),
        ("validator-body-source-site", "TwoSums", lambda text: body_instruction(
            text, "validator", 0,
            'operation := .receive "wrong-site" "wrong-site" "role00000000" (.field "bls12-381.fr")')),
        ("wrong-call-occurrence", "TwoSums", lambda text: replace_once(text, "index := 10", "index := 21")),
        ("helper-name", "SmallSumcheck", lambda text: replace_once(
            text, "abbrev plan := pattern.plan", 'abbrev plan := { pattern.plan with sumsHelper := "wrong-helper" }')),
        ("query-template", "TwoSums", lambda text: replace_once(
            text, "abbrev plan := pattern.plan",
            'abbrev plan := { pattern.plan with queryTemplate := { pattern.plan.queryTemplate with entry := "wrong-entry" } }')),
    ]
    mutations = []
    for name, selected, transform in controls:
        path = records / f"{name}.lean"
        theorem = {
            "same-typed-body-operands": "producer_actual_block",
            "validator-body-source-site": "validator_actual_block",
            "helper-name": "producer_block",
            "query-template": "occurrences",
        }.get(name, "checked")
        path.write_text(through_theorem(transform(texts[selected]), theorem))
        result = run(name, ["-R", str(records), str(path)])
        log = result.stdout + result.stderr
        assert result.returncode != 0, f"kernel accepted stale descriptor: {name}"
        assert "error:" in log or "error(" in log, name
        assert re.search(r"Type mismatch|Tactic .*failed|Tactic .*proved|not definitionally equal", log), name
        assert not re.search(r"unexpected token|object file|unknownIdentifier|Unknown identifier|declaration uses `sorry`", log), name
        mutations.append({"name": name, "root": selected, "status": "kernel-equation-refused"})
        print(f"PASS {name}", flush=True)

    result = run("lean-controls", ["TestsSecurity/RoundDescriptors.lean"])
    assert result.returncode == 0, "Lean discovery controls failed; see lean-controls.log"
    axiom_lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.DOTALL)
    assert len(axiom_lists) == 8, "missing generated obligation axiom audits"
    axioms = {name.strip() for group in axiom_lists for name in group.split(",")}
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, sorted(axioms)
    for relative in ["ZkcSecurity/Tools/RoundDescriptors.lean", "ZkcSecurity/Families/Sumcheck/RoundDescriptor.lean"]:
        imports = re.findall(r"^public import (.+)$", (root / relative).read_text(), re.MULTILINE)
        assert not any("Examples" in module or "Tests" in module for module in imports), relative
    report = {"scope": "actual retained-pair structural descriptor generation",
              "threads": 2, "outputs": outputs, "mutations": mutations,
              "exact_regeneration": True, "strict_modules": True, "lean_controls": True,
              "audited_axioms": sorted(axioms)}
    (records / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS exact regeneration, two strict modules, {len(mutations)} kernel refusals, Lean controls", flush=True)


if __name__ == "__main__":
    main()
