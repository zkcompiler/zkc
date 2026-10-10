#!/usr/bin/env python3
"""Explicit workspace preparation and native build operations.

The compiler profile is owned by CMakePresets.json. Nix supplies tools; these
operations only manage mutable checkout outputs. Tests live in common/tests/run.py.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

from workspace import ROOT, clear_report_directory, compiler_directory, native_configuration, reports_root, validate_environment
from processes import Interrupted, run as run_process
from reporting import new_directory
from install_domain import install_domain


def run(arguments, *, cwd=ROOT, stdout=None):
    arguments = list(map(str, arguments))
    print(f"+ {shlex.join(arguments)}", flush=True)
    run_process(arguments, cwd=cwd, stdout=stdout, check=True, cleanup_grace=5)


def configure(profile):
    compiler_directory(profile)  # Validate before changing the workspace.
    selected = native_configuration()
    run(["cmake", "--preset", profile, *[f"-D{key}={value}" for key, value in selected.items()]],
        cwd=ROOT / "compiler")


def fetch_lean(deps):
    run([sys.executable, ROOT / "lean/cache_dependencies.py",
         *([f"--with-{deps}"] if deps != "main" else []),
         "--output", reports_root() / f"lean/cache-{deps}.json"], cwd=ROOT / "lean")


CLEAN = ROOT / "lean/integrations/clean"
CLEAN_CONTROL = ROOT / "common/tests/fixtures/clean/air-control.json"


def clean_integration():
    """Build and audit the Clean package, then require the committed native
    control to be exactly what its producer prints now."""
    run(["lake", "build"], cwd=CLEAN)
    output = reports_root() / "lean/clean-air-control.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w") as stream:
        run(["lake", "env", "lean", "--run", "TestsClean/Control.lean"], cwd=CLEAN, stdout=stream)
    if output.read_bytes() != CLEAN_CONTROL.read_bytes():
        raise ValueError(f"{CLEAN_CONTROL.relative_to(ROOT)} is not the current Clean export; "
                         f"review {output} and replace the fixture with it")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    operations = parser.add_subparsers(dest="operation", required=True)
    for operation in ["setup", "configure", "compiler", "rust", "test-drivers", "lean",
                      "fetch-lean", "lean-integration", "lean-clean", "lean-fresh", "install",
                      "install-domain", "clean-reports"]:
        command = operations.add_parser(operation)
        if operation in {"configure", "compiler", "install", "install-domain"}:
            command.add_argument("--profile", default="release", help="CMake build profile (default: release)")
        if operation == "fetch-lean":
            command.add_argument("--deps", choices=["main", "arklib", "clean"], default="main")
        if operation in {"install", "install-domain"}:
            command.add_argument("--output", help="fresh installation output directory")
        if operation == "install-domain":
            command.add_argument("--base-build", help="explicit base CMake build directory")
            command.add_argument("--domain-build", help="explicit envelope CMake build directory")
            command.add_argument("--skip-build", action="store_true",
                                 help="install already built, cache-checked directories without rebuilding")
    args = parser.parse_args()
    validate_environment()
    # Native Cargo paths keep Cargo's cwd-relative meaning even though the
    # commands below consistently run at the repository root.
    if os.environ.get("CARGO_TARGET_DIR"):
        os.environ["CARGO_TARGET_DIR"] = str(Path(os.environ["CARGO_TARGET_DIR"]).resolve())
    if args.operation not in {"setup", "fetch-lean", "lean-integration", "lean-clean", "lean-fresh",
                              "install", "install-domain"}:
        execute(args)
        return
    # Each operation owns a new root; children that require an absent target
    # receive a path below it. Restore the caller's selection for repeated calls.
    output = new_directory(reports_root() / "runs", args.operation)
    previous = os.environ.get("ZKC_REPORTS_DIR")
    os.environ["ZKC_REPORTS_DIR"] = str(output)
    print(f"Reports: {output}", flush=True)
    record = {"operation": args.operation, "status": "running",
              "started_utc": datetime.now(timezone.utc).isoformat()}
    try:
        execute(args)
        record["status"] = "pass"
    except BaseException as error:
        record["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        record["error"] = str(error)
        raise
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (output / "run.json").write_text(json.dumps(record, indent=2) + "\n")
        if previous is None:
            os.environ.pop("ZKC_REPORTS_DIR", None)
        else:
            os.environ["ZKC_REPORTS_DIR"] = previous


def execute(args):
    if args.operation == "setup":
        run(["uv", "sync", "--locked"])
        run(["cargo", "fetch", "--locked"])
    elif args.operation == "fetch-lean":
        fetch_lean(args.deps)
    elif args.operation == "lean-integration":
        run(["lake", "build"], cwd=ROOT / "lean/integrations/arklib")
        run([sys.executable, ROOT / "lean/checks/check_clients.py", "--with-arklib",
             "--output", reports_root() / "lean/clients-arklib"], cwd=ROOT / "lean")
    elif args.operation == "lean-clean":
        clean_integration()
    elif args.operation == "lean-fresh":
        run([sys.executable, ROOT / "lean/reproduce.py", "--with-arklib", "--with-clean",
             "--output", reports_root() / "lean/fresh"], cwd=ROOT / "lean")
    elif args.operation == "configure":
        configure(args.profile)
    elif args.operation == "compiler":
        configure(args.profile)
        run(["cmake", "--build", "--preset", args.profile], cwd=ROOT / "compiler")
    elif args.operation == "lean":
        run(["lake", "build"], cwd=ROOT / "lean")
    elif args.operation == "rust":
        run(["cargo", "build", "--release", "--locked", "-p", "zkc-tools", "--bin", "zkc"])
    elif args.operation == "test-drivers":
        run(["cargo", "build", "--release", "--locked", "-p", "zkc-test-drivers", "--bins"])
    elif args.operation == "install-domain":
        install_domain(args, run)
    elif args.operation == "install":
        selected = native_configuration()
        prefix = Path(args.output).resolve() if args.output else reports_root() / "installed"
        # Refuse an existing prefix, including a dangling symlink, before running
        # install. Reserve it exclusively so simultaneous callers cannot share it.
        if args.output and os.path.lexists(Path(args.output).absolute()):
            raise ValueError(f"refusing existing install prefix: {args.output}")
        prefix.mkdir(parents=True, exist_ok=False)
        consumer = reports_root() / "consumer"
        run(["cmake", "--install", compiler_directory(args.profile), "--prefix", prefix])
        package = prefix / "lib/cmake/ZkcCompiler"
        if not (package / "ZkcCompilerConfig.cmake").is_file():
            # Otherwise find_package can ignore the missing hint and discover
            # a stale installation through CMAKE_PREFIX_PATH or its registry.
            raise ValueError(f"install did not produce {package / 'ZkcCompilerConfig.cmake'}")
        for name in ("zkc-compile", "zkc-opt"):
            for option in ("--help", "--version"):
                run([prefix / "bin" / name, option])
        run(["cmake", "-S", ROOT / "common/tests/consumer", "-B", consumer,
             "-G", "Ninja", f"-DZkcCompiler_DIR={package}",
             *[f"-D{key}={value}" for key, value in selected.items()]])
        run(["cmake", "--build", consumer])
        run(["ctest", "--test-dir", consumer, "--output-on-failure"])
    elif args.operation == "clean-reports":
        clear_report_directory(ROOT / os.environ.get("ZKC_REPORTS_DIR", "build/reports"))


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
