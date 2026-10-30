#!/usr/bin/env python3
"""Schedule Lean-owned source presentation generation and compare exact bytes.

Python selects a named catalogue entry and gathers output. It never reads a
participant body or derives an operation, role mask, helper law or return.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"
GENERATOR = "checks/GenerateScalarPresentations.lean"
SELECTIONS = ("ChaumPedersen", "Okamoto", "SchnorrAnd", "SchnorrInteractive",
              "SumcheckSource", "SumcheckReduction", "SumcheckRepacked", "Gkr")


def modules(selection: str) -> tuple[str, ...]:
    """Physical output names only; generation and body selection belong to Lean."""
    if selection == "Gkr":
        binding = "ZkcExamples.Structured.Generated.Bindings.GkrRounds"
        return ("Zkc.Protocols.Gkr.Source.RoundHelpers", binding, binding + "Callbacks", binding + "Gate", binding + "Caller",
                "ZkcExamples.Structured.Generated.Presentations.Gkr")
    if selection not in SELECTIONS:
        raise ValueError(f"unknown source selection: {selection}")
    name = f"ZkcExamples.Structured.Generated.Scalar.{selection}"
    return (name + "Bindings", name + "BindingsCallbacks", name,
            *((name + "Library",) if selection.startswith("Sumcheck") else ()))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("selections", nargs="*", choices=SELECTIONS)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    env = {**os.environ, "ELAN_TOOLCHAIN": "leanprover/lean4:v4.35.0", "LEAN_NUM_THREADS": "2"}
    selected = args.selections or SELECTIONS
    generators = []
    if "Gkr" in selected:
        generators += ["Tests.StructuredBindingsGenerator", "Tests.Generators.GkrPresentations"]
    if any(selection != "Gkr" for selection in selected):
        generators.append("Tests.Generators.ScalarViews")
    # The generators can import freshly rewritten source data. Refresh those
    # imports before executing them; an old olean is not a source snapshot.
    subprocess.run(["lake", "build", *generators], cwd=LEAN, env=env, check=True)
    with tempfile.TemporaryDirectory(prefix="zkc-scalar-source-views-") as directory:
        for selection in selected:
            if selection == "Gkr":
                with tempfile.TemporaryDirectory(prefix="zkc-source-bindings-") as bindings:
                    subprocess.run(["lake", "env", "lean", "-j2", "-M16384", "--run",
                                    "checks/GenerateStructuredBindings.lean", bindings,
                                    "--only", "GkrRounds"], cwd=LEAN, env=env, check=True)
                    stem = Path("ZkcExamples/Structured/Generated/Bindings/GkrRounds")
                    suffixes = {".lean": ".lean", ".callbacks.lean": "Callbacks.lean",
                                ".template.lean": "Gate.lean", ".caller.lean": "Caller.lean"}
                    template_path = Path("Zkc/Protocols/Gkr/Source/RoundHelpers.lean")
                    expected_bindings = {Path(str(stem) + suffix) for suffix in suffixes} | {template_path}
                    actual_bindings = {p.relative_to(bindings) for p in Path(bindings).rglob("*.lean")}
                    if actual_bindings != expected_bindings:
                        raise SystemExit("source-views: unexpected GKR binding output inventory")
                    target = Path(directory) / template_path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes((Path(bindings) / template_path).read_bytes())
                    for printed, shipped in suffixes.items():
                        target = Path(directory) / (str(stem) + shipped)
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_bytes((Path(bindings) / (str(stem) + printed)).read_bytes())
                presentation = Path(directory) / "ZkcExamples/Structured/Generated/Presentations/Gkr.lean"
                subprocess.run(["lake", "env", "lean", "-j2", "-M16384", "--run",
                                "checks/GenerateGkrPresentations.lean", str(presentation)],
                               cwd=LEAN, env=env, check=True)
            else:
                subprocess.run(["lake", "env", "lean", "-j2", "-M16384", "--run", GENERATOR,
                                directory, selection], cwd=LEAN, env=env, check=True)
        expected = {Path(module.replace(".", "/") + ".lean")
                    for selection in args.selections or SELECTIONS for module in modules(selection)}
        actual = {path.relative_to(directory) for path in Path(directory).rglob("*.lean")}
        if actual != expected:
            raise SystemExit(f"source-views: output inventory differs: {actual ^ expected}")
        for generated in sorted(Path(directory).rglob("*.lean")):
            target = LEAN / generated.relative_to(directory)
            if args.check:
                if not target.is_file() or target.read_bytes() != generated.read_bytes():
                    raise SystemExit(f"source-views: regenerate {target.relative_to(ROOT)}")
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(generated.read_bytes())
        print(f"{'checked' if args.check else 'generated'} source presentations")


if __name__ == "__main__":
    main()
