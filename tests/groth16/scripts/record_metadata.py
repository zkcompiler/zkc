#!/usr/bin/env python3
"""Compare compact preserved evidence and record this run's actual environment."""

import platform
import subprocess

from common import ROOT, check_files, read_json, require_workspace, sha256, write_json


def compact_intermediates(value):
    value.pop("elapsedMs", None)
    for vector in value["vectors"].values():
        vector.pop("first8", None)
        vector.pop("last2", None)
    return value


def compact_controls(value):
    for control in value["results"]:
        control.pop("error", None)
    return value


def compare(root, evidence_root=None):
    evidence_root = evidence_root or root / "evidence"
    check_files(root, read_json(evidence_root / "artifact-manifest.json")["files"])
    vector_count = 0
    controls = 0
    for depth in (2, 16):
        artifact = root / f"artifacts/depth{depth}"
        expected = evidence_root / f"depth{depth}"
        actual = compact_intermediates(read_json(artifact / "intermediates.json"))
        if actual != read_json(expected / "intermediates.json"):
            raise ValueError(
                f"Intermediate value or vector digest mismatch at depth {depth}"
            )
        for vector in actual["vectors"].values():
            check_files(
                artifact,
                {
                    vector["path"]: {
                        "sha256": vector["sha256"],
                        "bytes": 32 * vector["length"],
                    }
                },
            )
            vector_count += 1
        actual_controls = compact_controls(
            read_json(artifact / "controls/results.json")
        )
        if actual_controls != read_json(expected / "controls.json"):
            raise ValueError(f"Named fixture controls differ at depth {depth}")
        controls += actual_controls["passed"]
    return {
        "fixtureControls": controls,
        "vectorHashes": vector_count,
        "exactFixedProofs": 4,
    }


def main():
    require_workspace()
    checks = compare(ROOT)
    config = read_json(ROOT / ".groth16-workdir.json")
    versions = {
        "node": subprocess.check_output(["node", "--version"], text=True).strip(),
        "npm": subprocess.check_output(["npm", "--version"], text=True).strip(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "workerLimit": config["workers"],
        "circom": config["circom"],
        "circomlib": config["circomlib"],
        "dependencyLockSha256": sha256(ROOT / "package-lock.json"),
        "scope": "Circom/snarkjs fixture and independent algebra only; no zkc PIR result",
        "checks": checks,
    }
    write_json(ROOT / "VERSIONS.json", versions)
    files = {}
    for path in sorted((ROOT / "artifacts").rglob("*")):
        if path.is_file():
            files[str(path.relative_to(ROOT))] = {
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
    write_json(ROOT / "artifact-manifest.json", {"files": files})
    write_json(
        ROOT / "RESULTS.json",
        {"status": "passed", "scope": versions["scope"], **checks},
    )
    print(f"PASS: {checks}")


if __name__ == "__main__":
    main()
