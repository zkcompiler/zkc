#!/usr/bin/env python3
"""Check fresh generic root connections after shifting callback SSA coordinates.

The existing Lean printers propose both constructed views and the connection.
Lean checks the whole generated certificates, full returns and axiom closures.
This driver only schedules those checks and retains their diagnostics.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--records", type=Path)
    options = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    records = (options.records or Path(tempfile.mkdtemp(prefix="zkc-connection-layout-"))).resolve()
    records.mkdir(parents=True, exist_ok=True)
    generated = records / "generated"
    generated.mkdir(exist_ok=True)
    environment = dict(os.environ, LEAN_NUM_THREADS="2")
    if not environment.get("LEAN_PATH"):
        environment["LEAN_PATH"] = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=package,
            env=environment, text=True).strip()
    environment["LEAN_PATH"] = str(generated) + os.pathsep + environment["LEAN_PATH"]
    commands = []

    def run(label: str, arguments: list[str]) -> None:
        command = ["lean", "-j2", "-M16384", "-DwarningAsError=true", *arguments]
        started = time.monotonic()
        result = subprocess.run(command, cwd=package, env=environment,
                                text=True, capture_output=True, timeout=600)
        output = result.stdout + result.stderr
        (records / (label + ".log")).write_text(output)
        commands.append({"label": label, "command": command, "cwd": str(package),
                         "returncode": result.returncode,
                         "seconds": time.monotonic() - started})
        (records / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode or "sorryAx" in output:
            raise AssertionError(f"{label}: checking failed; see {records / (label + '.log')}")
        print("PASS " + label, flush=True)

    run("generate", ["--run", "Tests/ConnectionLayoutGeneration.lean", str(generated)])

    def compile_module(module: str) -> None:
        source = generated / (module.replace(".", "/") + ".lean")
        run(module.replace(".", "-"), ["--root=" + str(generated),
            "-o", str(source.with_suffix(".olean")), str(source)])

    for role in ("Producer", "Validator", "Connection"):
        compile_module("ConnectionLayoutControl." + role)
    audit = generated / "ConnectionLayoutControl/Audit.lean"
    audit.write_text('''import ConnectionLayoutControl.Connection
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [
  `Tests.ConnectionLayout, `ConnectionLayoutControl.Producer,
  `ConnectionLayoutControl.Validator, `ConnectionLayoutControl.Connection] "CONNECTION-LAYOUT-AXIOMS-PASS" true

#print axioms ConnectionLayoutControl.Connection.producerConnected
#print axioms ConnectionLayoutControl.Connection.validatorConnected
''')
    compile_module("ConnectionLayoutControl.Audit")
    manifest = [{"path": str(path.relative_to(generated)),
                 "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in sorted(generated.rglob("*.lean"))]
    (records / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
