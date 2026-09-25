#!/usr/bin/env python3
"""Rebuild and audit the actual public foundation without external packages.

Copies its local import closure unchanged to a fresh Lake package. This checks
import independence, not the complete root package or optional integrations.
"""

import argparse
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import support.evidence  # noqa: E402

import support.lake
import re
import shutil
import subprocess
import time

from support.lean_headers import HeaderParser


ROOT = Path(__file__).resolve().parents[1]




def foundation_inputs(root, headers):
    pending = ["Tests.FoundationAudit"]
    inputs = {}
    while pending:
        module = pending.pop()
        path = Path(*module.split(".")).with_suffix(".lean")
        if str(path) in inputs:
            continue
        source = root / path
        for dependency in headers.imports(source.read_text(), source):
            family = dependency.split(".")[0]
            if family in {"Zkc", "Tests", "Tools"}:
                pending.append(dependency)
            elif family not in {"Std", "Lean", "Init"}:
                raise ValueError(f"external foundation import: {module}: {dependency}")
        if "Compat" in path.parts:
            raise ValueError(f"historical foundation import: {module}")
        inputs[str(path)] = support.lake.sha(source)
    return inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=support.evidence.records("foundation", ""))
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    try:
        lake = support.lake.resolve(args.lake)
    except support.lake.Unavailable as absent:
        parser.error(str(absent))
    lake = str(Path(lake).absolute())
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error("output must be a fresh directory outside formal/")
    output.mkdir(parents=True, exist_ok=False)
    with HeaderParser(lake=lake) as headers:
        inputs = foundation_inputs(ROOT, headers)
    for name in inputs:
        path = Path(name)
        (output / path).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / path, output / path)
    shutil.copy2(ROOT / "lean-toolchain", output / "lean-toolchain")
    test_roots = sorted(
        ".".join(Path(path).with_suffix("").parts)
        for path in inputs if Path(path).parts[0] == "Tests"
    )
    (output / "lakefile.toml").write_text('''name = "zkc-foundation-check"
version = "0.1.0"
defaultTargets = ["FoundationTests"]
[leanOptions]
autoImplicit = false
warningAsError = true
[[lean_lib]]
name = "Zkc"
[[lean_lib]]
name = "Tools"
globs = ["Tools.*"]
[[lean_lib]]
name = "FoundationTests"
roots = ''' + json.dumps(test_roots) + "\n")
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_HOME"):
        env.pop(name, None)
    version = subprocess.check_output([lake, "env", "lean", "--version"],
                                      cwd=output, env=env, text=True).strip()
    expected = (output / "lean-toolchain").read_text().strip().split(":v")[-1]
    found = re.search(r"version (\d+\.\d+\.\d+)", version)
    if found is None or found[1] != expected:
        raise ValueError(f"wrong Lean toolchain: {version}; expected {expected}")
    start = time.monotonic()
    with (output / "build.log").open("w") as log:
        result = subprocess.run([lake, "--no-cache", "build"], cwd=output, env=env,
                                stdout=log, stderr=subprocess.STDOUT)
    log = (output / "build.log").read_text()
    match = re.search(r"FOUNDATION-AUDIT-PASS declarations=(\d+) theorems=(\d+)", log)
    drift = any(support.lake.sha(ROOT / p) != h or support.lake.sha(output / p) != h for p, h in inputs.items())
    passed = result.returncode == 0 and match is not None and not drift
    record = {
        "format": "zkc.foundation-check.v1", "status": "pass" if passed else "fail",
        "exit_code": result.returncode, "lean_version": version, "lake_executable": lake,
        "toolchain": (output / "lean-toolchain").read_text().strip(),
        "source_drift": drift, "source_inputs": inputs,
        "harness_sha256": support.lake.sha(Path(__file__).resolve()),
        "header_parser_inputs": {name: support.lake.sha(ROOT / name) for name in
                                 ("support/lean_headers.py", "Tools/ImportHeaders.lean")},
        "lakefile_sha256": support.lake.sha(output / "lakefile.toml"),
        "build_log_sha256": support.lake.sha(output / "build.log"),
        "elapsed_seconds": round(time.monotonic() - start, 2),
        "declarations": int(match[1]) if match else None,
        "theorems": int(match[2]) if match else None,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "external_packages": [], "prior_build_objects": False,
        "scope": "public foundation plus complete-execution representation laws and controls; not the full library or native execution",
    }
    (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: v for k, v in record.items() if k != "source_inputs"}, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
