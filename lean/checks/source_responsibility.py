#!/usr/bin/env python3
"""Emit source ownership and unresolved edit candidates from tracked paths.

This is an input to evaluation and migration review, not a semantic edit
classifier. It never classifies an arbitrary new provider or law as D merely
because the file lives in a domain directory.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.dependencies import POLICY_SOURCE
from support.responsibility import classify


def inventory(root):
    root = root.resolve()
    raw = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "lean", "compiler", "crates", "libraries", "examples", "scripts", "nix", "common/tests"],
        cwd=root,
    )
    rows = []
    for value in sorted(set(raw.decode().split("\0")) - {""}):
        responsibility = classify(value)
        path = root / value
        if path.is_symlink():
            contents, kind = str(path.readlink()).encode(), "symlink"
        elif path.is_file():
            contents, kind = path.read_bytes(), "file"
        else:
            contents, kind = None, "deleted"
        rows.append({"path": value, "kind": kind,
                     "sha256": hashlib.sha256(contents).hexdigest() if contents is not None else None,
                     **responsibility.record()})
    counts = Counter(row["responsibility"] or "unclassified" for row in rows)
    return {
        "format": "zkc.source-responsibility/0",
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "policy_sha256": hashlib.sha256(POLICY_SOURCE.read_bytes()).hexdigest(),
        "classifier_sha256": hashlib.sha256((Path(__file__).resolve().parents[1] / "support/responsibility.py").read_bytes()).hexdigest(),
        "policy_source": "policy and classifier shipped with this inventory tool; identified by content hashes",
        "scope": "tracked selected source paths in the current working tree, including deletions; untracked paths require staging or a separate inventory",
        "meaning": "ownership and candidate categories, not final semantic edit counts or proof-discharge responsibility",
        "counts": dict(sorted(counts.items())),
        "paths": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(inventory(args.root), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
