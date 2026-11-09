#!/usr/bin/env python3
"""Regenerate source selections and kernel-check every emitted equation.

Semantic controls live in Lean. This script only schedules commands and records
their diagnostics; failure to compile is never reported as semantic refusal.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.invocation import command as lean_command  # noqa: E402
from support.packages import module_package, module_path  # noqa: E402
from bridges.structured.source_views import SELECTIONS, modules  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--records", type=Path)
    args = parser.parse_args()
    lean = Path(__file__).resolve().parents[1]
    records = (args.records or Path(tempfile.mkdtemp(prefix="zkc-source-view-checks-"))).resolve()
    records.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "ELAN_TOOLCHAIN": "leanprover/lean4:v4.35.0", "LEAN_NUM_THREADS": "2"}
    results = []

    def run(name: str, command: list[str], cwd=module_package("Zkc.Applications")) -> None:
        result = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
        log = records / (name + ".log")
        log.write_text(result.stdout + result.stderr)
        results.append(dict(name=name, command=command, exit_code=result.returncode, log=str(log)))
        (records / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        if result.returncode:
            raise SystemExit(f"source-views: command failed; see {log}")

    run("regeneration", [sys.executable, str(lean / "bridges/structured/source_views.py"), "--check"])
    # Lake checks source freshness and rebuilds the complete import closure.
    # A preceding package build can therefore be reused without elaborating
    # every generated proof a second time in the same validation run.
    proofs = [*(module for selection in SELECTIONS for module in modules(selection)),
              "Zkc.Tests.IR.StructuredNormalFormComponents", "Zkc.Tests.Applications.IR.StructuredNormalForms",
              "Zkc.Tests.Applications.IR.ScalarSourcePresentations", "Zkc.Tests.IR.RoleViewGeneration",
              "Zkc.Tests.IR.RepeatOccurrences", "Zkc.Tests.IR.SourceConfigurationSelection"]
    for module in proofs:
        run("proof-" + module, ["lake", "build", "+" + module], cwd=module_package(module))
    # Imported fixture definitions do not execute their scratch compilation or
    # refusal checks. Keep those checks in this maintained source-view lane.
    for name, driver in (("repeat-occurrences", "CheckRepeatOccurrences"),
                         ("source-configurations", "CheckSourceConfigurationSelection")):
        run(name, [*lean_command(module_package("Zkc.Applications")), "--run", module_path(f"Zkc.Tools.IR.Commands.{driver}"), str(records / name)])
    print(f"source-views: exact regeneration and kernel controls passed; {records}")


if __name__ == "__main__":
    main()
