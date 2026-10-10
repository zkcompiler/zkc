#!/usr/bin/env python3
"""Compare the two table models in a freshly built composition consumer."""

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import support.evidence  # noqa: E402
import re
import shutil
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=support.evidence.records("comparison", ""))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("Lake is unavailable")
    before = {str(path): digest(path) for path in
              [HERE / "check.py", HERE / "Comparison.lean", HERE / "Audit.lean"]}
    composition = output / "composition"
    with (output / "composition.log").open("w") as log:
        subprocess.run([sys.executable, "-B", str(HERE.parent / "composition/check.py"),
                        "--output", str(composition)], stdout=log, stderr=subprocess.STDOUT, check=True)
    before.update(json.loads((composition / "inputs.json").read_text()))
    client = composition / "client"
    sources = client / "OpeningComparison"
    sources.mkdir()
    for name in ("Comparison", "Audit"):
        shutil.copy2(HERE / f"{name}.lean", sources / f"{name}.lean")
    with (client / "lakefile.toml").open("a") as config:
        config.write('\n[[lean_lib]]\nname = "OpeningComparison"\nglobs = ["OpeningComparison.+"]\n')
    command = [lake, "--no-cache", "build", "OpeningComparison"]
    log_path = output / "comparison.log"
    with log_path.open("w") as log:
        run = subprocess.run(command, cwd=client, stdout=log, stderr=subprocess.STDOUT, check=False)
    audit = re.search(r"OPENING-REDUCTION-AUDIT-PASS declarations=(\d+) theorems=(\d+)", log_path.read_text())
    drift = [path for path, expected in before.items()
             if not Path(path).exists() or digest(Path(path)) != expected]
    copied_drift = [name for name in ("Comparison", "Audit")
                    if digest(sources / f"{name}.lean") != before[str(HERE / f"{name}.lean")]]
    (output / "inputs.json").write_text(json.dumps(before, indent=2) + "\n")
    passed = (run.returncode == 0 and audit is not None and int(audit[1]) > 0
              and int(audit[2]) >= 4 and not drift and not copied_drift)
    record = {
        "status": "pass" if passed else "fail", "command": command, "exit_code": run.returncode,
        "input_files": len(before), "source_drift": drift, "copied_source_drift": copied_drift,
        "audit": None if audit is None else {"declarations": int(audit[1]), "theorems": int(audit[2])},
        "log_sha256": digest(log_path), "inputs_sha256": digest(output / "inputs.json"),
        "scope": "fresh comparison/Composition objects; existing main/dependency objects may be reused; no native or PCS proof",
    }
    (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
