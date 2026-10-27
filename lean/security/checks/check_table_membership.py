#!/usr/bin/env python3
"""Regenerate and check the actual plain aggregate canonical claim path.

Supply prechecked core/security dependencies in LEAN_PATH (or run under lake
env). Only this private output directory is written; no Lake build, dependency
update, native export, or sealed fixture is run. LEAN_NUM_THREADS is fixed at 2.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


PACKAGE = Path(__file__).resolve().parents[1]
PREFIX = "ZkcSecurity.Examples.TableMembership."


def inherit_objects(source: Path, target: Path) -> None:
    """Merge immutable dependency namespaces; Lean picks one root per namespace."""
    if not source.is_dir() or source.resolve() == target.resolve():
        return
    for item in source.iterdir():
        destination = target / item.name
        if item.is_dir():
            destination.mkdir(parents=True, exist_ok=True)
            inherit_objects(item, destination)
        elif item.is_file() and not destination.exists():
            destination.symlink_to(item.resolve())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    sources, objects, logs = (output / name for name in ("generated", "objects", "logs"))
    for directory in (sources, objects, logs):
        directory.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="2")
    for inherited in env.get("LEAN_PATH", "").split(os.pathsep):
        if inherited:
            inherit_objects(Path(inherited), objects)
    env["LEAN_PATH"] = str(objects) + os.pathsep + env.get("LEAN_PATH", "")
    commands = []
    modules = []

    def record() -> None:
        (output / "manifest.json").write_text(json.dumps({
            "schema": "zkc.plain-table-claims/0", "threads": 2,
            "commands": commands, "modules": modules,
        }, indent=2) + "\n")

    def run(name: str, command: list[str]) -> None:
        start = time.monotonic()
        result = subprocess.run(command, cwd=PACKAGE, env=env, text=True, capture_output=True, check=False)
        log = result.stdout + result.stderr
        (logs / (name + ".log")).write_text(log)
        passed = result.returncode == 0 and "sorryAx" not in log
        commands.append({"name": name, "command": command, "exit_code": result.returncode,
                         "seconds": time.monotonic() - start, "passed": passed})
        record()
        print(f"{'PASS' if passed else 'FAIL'} {name}", flush=True)
        if not passed:
            raise SystemExit(log)

    def compile_module(module: str, *, generated: bool = False) -> None:
        root = sources if generated else PACKAGE
        relative = Path(*module.split("."))
        source = root / relative.with_suffix(".lean")
        target = objects / relative.with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        for artifact in target.parent.glob(target.stem + ".*"):
            if artifact.is_symlink():
                artifact.unlink()
        target.unlink(missing_ok=True)
        run(module, ["lean", "-DwarningAsError=true", "--root=" + str(root),
                     "-o", str(target), str(source)])
        data = source.read_bytes()
        modules.append({"module": module, "generated": generated,
                        "bytes": len(data), "lines": len(data.splitlines()),
                        "sha256": hashlib.sha256(data).hexdigest()})
        record()

    compile_module(PREFIX + "Subject")
    compile_module("ZkcSecurity.Generation.TableMembership")
    run("generate", ["lean", "--run", "checks/RunTableMembershipABI.lean", str(sources)])
    emitted = [PREFIX + suffix for suffix in ("ABI", "Endpoint")]
    before = {module: (sources / Path(*module.split("."))).with_suffix(".lean").read_bytes()
              for module in emitted}
    run("regenerate", ["lean", "--run", "checks/RunTableMembershipABI.lean", str(sources)])
    for module, data in before.items():
        relative = Path(*module.split(".")).with_suffix(".lean")
        if (sources / relative).read_bytes() != data:
            raise SystemExit("non-reproducible generated source: " + module)
        if (PACKAGE / relative).read_bytes() != data:
            raise SystemExit("tracked generated source is stale: " + module)
    compile_module(PREFIX + "ABI", generated=True)
    compile_module(PREFIX + "Method")
    compile_module(PREFIX + "Endpoint", generated=True)
    compile_module(PREFIX + "Claims")
    compile_module("TestsSecurity.TableMembershipClaims")


if __name__ == "__main__":
    main()
