#!/usr/bin/env python3
"""Check upstream source identities and change exactly two randomizer lines."""

import difflib
from pathlib import Path
import shutil

from common import ROOT, read_json, require_workspace, sha256, write_json


def prepare(root, evidence_root=None):
    root = Path(root)
    evidence_root = Path(evidence_root) if evidence_root else root / "evidence"
    source = root / "node_modules/snarkjs"
    target = root / "reference/snarkjs-controlled"
    expected = read_json(evidence_root / "source-integrity.json")
    if read_json(source / "package.json")["version"] != expected["version"]:
        raise ValueError("Unexpected snarkjs version")
    checked = {
        "originalProverSha256": "src/groth16_prove.js",
        "unmodifiedVerifierSha256": "src/groth16_verify.js",
        "compiledCliSha256": "build/cli.cjs",
    }
    for key, relative in checked.items():
        if sha256(source / relative) != expected[key]:
            raise ValueError(f"Upstream source hash mismatch: {relative}")
    original = (source / "src/groth16_prove.js").read_text()
    changed = original
    for name in ("r", "s"):
        old = f"    const {name} = curve.Fr.random();"
        new = f"    const {name} = curve.Fr.e(options.fixture{name.upper()});"
        if changed.count(old) != 1:
            raise ValueError(f"Expected exactly one randomizer line for {name}")
        changed = changed.replace(old, new)
    if target.exists():
        shutil.rmtree(target)
    shutil.copytree(source / "src", target / "src")
    for name in ("package.json", "COPYING"):
        shutil.copy2(source / name, target / name)
    (target / "src/groth16_prove.js").write_text(changed)
    differences = [
        str(path.relative_to(source))
        for path in sorted((source / "src").rglob("*"))
        if path.is_file()
        and path.read_bytes() != (target / path.relative_to(source)).read_bytes()
    ]
    if differences != expected["changedFiles"]:
        raise ValueError(f"Unexpected controlled-source changes: {differences}")
    if sha256(target / "src/groth16_prove.js") != expected["controlledProverSha256"]:
        raise ValueError("Controlled prover source hash mismatch")
    diff = "".join(
        difflib.unified_diff(
            original.splitlines(True),
            changed.splitlines(True),
            fromfile="snarkjs-0.7.5/src/groth16_prove.js",
            tofile="snarkjs-controlled/src/groth16_prove.js",
        )
    )
    if diff != (evidence_root / "prover-rng-only.diff").read_text():
        raise ValueError(
            "Controlled prover patch differs from the reviewed two-line patch"
        )
    (root / "reference/prover-rng-only.diff").write_text(diff)
    write_json(root / "reference/source-integrity.json", expected)
    print(
        "Verified original prover, unchanged verifier/CLI, and exact two-line RNG patch"
    )


if __name__ == "__main__":
    require_workspace()
    prepare(ROOT)
