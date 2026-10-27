#!/usr/bin/env python3
"""Print full retained looped artifact views using the existing Lean printer.

The Lean driver writes only into the explicit scratch directory. Each printed
module is kernel checked there before --write installs generated data. Authored
connection proofs are outside this generator's output set.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

LEAN = Path(__file__).resolve().parents[2]
SELECTIONS = (
    ("GkrValidator", "ZkcExamples.Construction.GkrProofParticipant"),
    ("ComposedSumcheckValidator", "ZkcExamples.Construction.ComposedSumcheckProofParticipant"),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="private scratch directory")
    parser.add_argument("--lake", default="lake", help="owning Lake executable")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    directory = args.output.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "2"))
    commands = []

    def execute(command):
        result = subprocess.run(command, cwd=LEAN, env=environment, text=True, capture_output=True)
        log = directory / f"command-{len(commands):02}.log"
        log.write_text(result.stdout + result.stderr)
        commands.append({"command": command, "returncode": result.returncode, "log": str(log)})
        (directory / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"command failed; see {log}")
        return result.stdout.strip()

    lean = execute([args.lake, "env", "which", "lean"])
    environment["LEAN_PATH"] = execute([args.lake, "env", "printenv", "LEAN_PATH"])
    records = []
    for name, artifact_module in SELECTIONS:
        module = f"ZkcExamples.Structured.Generated.Constructed.{name}"
        relative = Path(*module.split(".")).with_suffix(".lean")
        target = LEAN / relative
        printed = directory / relative
        printed.parent.mkdir(parents=True, exist_ok=True)
        driver = directory / f"Print{name}.lean"
        driver.write_text(f'''import ZkcTools.StructuredSource.Constructed
import {artifact_module}
open ZkcTools.StructuredSource
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
def main : IO Unit :=
  match Constructed.source {artifact_module}.participant {{
    moduleName := {json.dumps(module)},
    artifactModule := {json.dumps(artifact_module)},
    artifactExpression := {json.dumps(artifact_module + '.participant')} }} with
  | .error reason => throw (IO.userError reason)
  | .ok source => IO.FS.writeFile {json.dumps(str(printed))} source
''')
        execute([lean, "--run", str(driver)])
        execute([lean, f"--root={directory}", "-o", str(printed.with_suffix(".olean")), str(printed)])
        data = printed.read_bytes()
        if args.write:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        elif not target.is_file() or target.read_bytes() != data:
            raise RuntimeError(f"generated module differs: {target}")
        records.append({"module": module, "artifact": artifact_module + ".participant",
                        "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)})
    (directory / "manifest.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
