#!/usr/bin/env python3
"""Check the executable proof validators against Lean and the runtime.

A compatibility entry point for the subject driver, `lean/bridges/subject.py`
with `--runtime`: it checks (or, with `--write`, regenerates) every subject whose
manifest selects the executable profile. For each, the driver requires the
committed program data and executable facts to be the exact renderings of the
fresh program, runs the Lean lowering rule on it and on the manifest's generic
program mutations, compares the runtime verifier with the Lean executable
meaning at every budget up to one past the threshold the Lean charge derives
and on generic proof edits, checks the axiom closures and proof dependencies
the manifest's receipt names, and checks that the runtime executes exactly the
program the record names.
"""

import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.append(str(ROOT / "lean"))
from bridges.pipeline import manifest  # noqa: E402


def main():
    executable = [subject.name for subject in manifest.load_all() if subject.profile("executable")]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--native", type=Path, default=ROOT / "target/release/zkc", help="the runtime CLI")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, required=True, help="new or empty evidence directory")
    parser.add_argument("--subject", action="append", choices=executable,
                        help="check only the named subjects (default: all)")
    parser.add_argument("--write", action="store_true",
                        help="rewrite the generated modules from the fresh programs and exports")
    args = parser.parse_args()
    command = [sys.executable, ROOT / "lean/bridges/subject.py", "--write" if args.write else "--check", "--runtime",
               "--compiler", args.compiler, "--native", args.native, "--lake", args.lake, "--output", args.output,
               *[f"--subject={name}" for name in args.subject or executable]]
    sys.exit(subprocess.run([str(part) for part in command]).returncode)


if __name__ == "__main__":
    main()
