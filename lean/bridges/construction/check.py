#!/usr/bin/env python3
"""Check compiled proof Entries' transcript construction and projection in Lean.

A compatibility entry point for the subject driver, `lean/bridges/subject.py`:
it checks (or, with `--write`, regenerates) every subject whose manifest selects
the construction profile. For each, the driver compiles the Entry, requires the
committed original, participant, Bodies and glue modules to be the exact
renderings of the fresh exports, runs the composed Lean check on the fresh
export and the manifest's generic mutations, and confirms that the native
checker refuses mutated candidates before export.
"""

import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.append(str(ROOT / "lean"))
from bridges.pipeline import manifest  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, required=True, help="new or empty evidence directory")
    parser.add_argument("--write", action="store_true", help="rewrite the generated modules from the fresh exports")
    args = parser.parse_args()
    subjects = [subject.name for subject in manifest.load_all() if subject.profile("construction")]
    command = [sys.executable, ROOT / "lean/bridges/subject.py", "--write" if args.write else "--check",
               "--compiler", args.compiler, "--lake", args.lake, "--output", args.output,
               *[f"--subject={name}" for name in subjects]]
    sys.exit(subprocess.run([str(part) for part in command]).returncode)


if __name__ == "__main__":
    main()
