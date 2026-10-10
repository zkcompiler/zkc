#!/usr/bin/env python3
"""Prepare development dependencies and mutable checkout builds.

CMake, Cargo and Lake own build settings. Nix supplies tools. Validation and
installed-consumer workflows live in common/tests/run.py.
"""

import argparse
from functools import partial
import os
from pathlib import Path
import subprocess
import sys

from workspace import ROOT, clear_report_directory, compiler_directory, native_configuration, reports_root, validate_environment
from processes import Interrupted, checked
from reporting import run_report

run = partial(checked, cwd=ROOT)


def configure(profile):
    compiler_directory(profile)
    selected = native_configuration()
    run(["cmake", "--preset", profile, *[f"-D{key}={value}" for key, value in selected.items()]],
        cwd=ROOT / "compiler")


def execute(args):
    if args.operation == "setup":
        run(["uv", "sync", "--locked"])
        run(["cargo", "fetch", "--locked"])
    elif args.operation == "fetch-lean":
        run([sys.executable, ROOT / "lean/cache_dependencies.py",
             *([f"--with-{args.deps}"] if args.deps != "main" else []),
             "--output", reports_root() / f"lean/cache-{args.deps}.json"], cwd=ROOT / "lean")
    elif args.operation == "lean-fresh":
        run([sys.executable, ROOT / "lean/reproduce.py", "--with-arklib", "--with-clean",
             "--output", reports_root() / "lean/fresh"], cwd=ROOT / "lean")
    elif args.operation == "configure":
        configure(args.profile)
    elif args.operation == "compiler":
        configure(args.profile)
        run(["cmake", "--build", "--preset", args.profile], cwd=ROOT / "compiler")
    elif args.operation == "lean":
        directory = ROOT / "lean"
        if args.deps != "main":
            directory /= f"integrations/{args.deps}"
        run(["lake", "build"], cwd=directory)
    elif args.operation == "rust":
        run(["cargo", "build", "--release", "--locked", "-p", "zkc-tools", "--bin", "zkc"])
    elif args.operation == "test-drivers":
        run(["cargo", "build", "--release", "--locked", "-p", "zkc-test-drivers", "--bins"])
    elif args.operation == "clean-reports":
        clear_report_directory(ROOT / os.environ.get("ZKC_REPORTS_DIR", "build/reports"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    operations = parser.add_subparsers(dest="operation", required=True)
    for operation in ["setup", "configure", "compiler", "rust", "test-drivers", "lean",
                      "fetch-lean", "lean-fresh", "clean-reports"]:
        command = operations.add_parser(operation)
        if operation in {"configure", "compiler"}:
            command.add_argument("--profile", default="release", help="CMake build profile (default: release)")
        if operation in {"fetch-lean", "lean"}:
            command.add_argument("--deps", choices=["main", "arklib", "clean"], default="main")
    args = parser.parse_args()
    validate_environment()
    if os.environ.get("CARGO_TARGET_DIR"):
        os.environ["CARGO_TARGET_DIR"] = str(Path(os.environ["CARGO_TARGET_DIR"]).resolve())
    if args.operation in {"setup", "fetch-lean", "lean-fresh"}:
        with run_report(reports_root(), args.operation, sys.argv):
            execute(args)
    else:
        execute(args)


if __name__ == "__main__":
    try:
        main()
    except Interrupted as error:
        sys.exit(128 + error.signum)
    except subprocess.CalledProcessError as error:
        print(error, file=sys.stderr)
        sys.exit(error.returncode if error.returncode >= 0 else 128 - error.returncode)
    except (ValueError, OSError) as error:
        sys.exit(str(error))
