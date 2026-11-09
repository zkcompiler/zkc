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
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"
from support.invocation import command as lean_command  # noqa: E402
from support.packages import module_package, module_path  # noqa: E402

GENERATOR = str(module_path("Zkc.Tools.Verification.Commands.GenerateScalarPresentations"))
SELECTIONS = ("ChaumPedersen", "Okamoto", "SchnorrAnd", "SchnorrInteractive",
              "SumcheckSource", "SumcheckReduction", "SumcheckRepacked", "Gkr")


def modules(selection: str) -> tuple[str, ...]:
    """Physical output names only; generation and body selection belong to Lean."""
    if selection == "Gkr":
        binding = "Zkc.Applications.IR.Structured.Generated.Bindings.GkrRounds"
        return ("Zkc.Verification.Installations.Gkr.Source.RoundHelpers", binding, binding + "Callbacks", binding + "Gate", binding + "Caller",
                "Zkc.Applications.IR.Structured.Generated.Presentations.Gkr")
    if selection not in SELECTIONS:
        raise ValueError(f"unknown source selection: {selection}")
    name = f"Zkc.Applications.IR.Structured.Generated.Scalar.{selection}"
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
        generators += ["Zkc.Tests.Applications.IR.StructuredBindingsGenerator", "Zkc.Tests.Applications.IR.Generators.GkrPresentations"]
    if any(selection != "Gkr" for selection in selected):
        generators.append("Zkc.Tests.Verification.IR.Generators.ScalarViews")
    # The generators can import freshly rewritten source data. Refresh those
    # imports before executing them; an old olean is not a source snapshot.
    for module in generators:
        subprocess.run(["lake", "build", "+" + module], cwd=module_package(module), env=env, check=True)
    with tempfile.TemporaryDirectory(prefix="zkc-scalar-source-views-") as directory:
        for selection in selected:
            if selection == "Gkr":
                with tempfile.TemporaryDirectory(prefix="zkc-source-bindings-") as bindings:
                    subprocess.run([*lean_command(module_package("Zkc.Applications")), "-j2", "-M16384", "--run",
                                    str(module_path("Zkc.Tools.Applications.Commands.GenerateStructuredBindings")), bindings,
                                    "--only", "GkrRounds"], cwd=module_package("Zkc.Applications"), env=env, check=True)
                    stem = Path("Zkc/Applications/IR/Structured/Generated/Bindings/GkrRounds")
                    suffixes = {".lean": ".lean", ".callbacks.lean": "Callbacks.lean",
                                ".template.lean": "Gate.lean", ".caller.lean": "Caller.lean"}
                    template_path = Path("Zkc/Verification/Installations/Gkr/Source/RoundHelpers.lean")
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
                presentation = Path(directory) / "Zkc/Applications/IR/Structured/Generated/Presentations/Gkr.lean"
                subprocess.run([*lean_command(module_package("Zkc.Applications")), "-j2", "-M16384", "--run",
                                str(module_path("Zkc.Tools.Applications.Commands.GenerateGkrPresentations")), str(presentation)],
                               cwd=module_package("Zkc.Applications"), env=env, check=True)
            else:
                subprocess.run([*lean_command(module_package("Zkc.Applications")), "-j2", "-M16384", "--run", GENERATOR,
                                directory, selection], cwd=module_package("Zkc.Applications"), env=env, check=True)
        expected = {Path(module.replace(".", "/") + ".lean")
                    for selection in args.selections or SELECTIONS for module in modules(selection)}
        actual = {path.relative_to(directory) for path in Path(directory).rglob("*.lean")}
        if actual != expected:
            raise SystemExit(f"source-views: output inventory differs: {actual ^ expected}")
        for generated in sorted(Path(directory).rglob("*.lean")):
            module = ".".join(generated.relative_to(directory).with_suffix("").parts)
            target = module_path(module)
            if args.check:
                if not target.is_file() or target.read_bytes() != generated.read_bytes():
                    raise SystemExit(f"source-views: regenerate {target.relative_to(ROOT)}")
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(generated.read_bytes())
        print(f"{'checked' if args.check else 'generated'} source presentations")


if __name__ == "__main__":
    main()
