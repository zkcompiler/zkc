#!/usr/bin/env python3
"""Explicit workspace preparation and native build operations.

The compiler profile is owned by CMakePresets.json. Nix supplies tools; these
operations only manage mutable checkout outputs. Tests live in tests/run.py.
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
    run([sys.executable, ROOT / "formal/cache_dependencies.py",
         *(["--with-arklib"] if deps == "arklib" else []),
         "--output", reports_root() / f"formal/cache-{deps}.json"], cwd=ROOT / "formal")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["setup", "configure", "compiler", "rust", "lean",
                                             "fetch-lean", "lean-integration", "lean-fresh", "install", "bench", "clean-reports"])
    parser.add_argument("--profile", default="release")
    parser.add_argument("--deps", choices=["main", "arklib"], default="main")
    parser.add_argument("--output")
    args = parser.parse_args()
    validate_environment()
    # Native Cargo paths keep Cargo's cwd-relative meaning even though the
    # commands below consistently run at the repository root.
    if os.environ.get("CARGO_TARGET_DIR"):
        os.environ["CARGO_TARGET_DIR"] = str(Path(os.environ["CARGO_TARGET_DIR"]).resolve())
    if args.operation not in {"setup", "fetch-lean", "lean-integration", "lean-fresh", "install"}:
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
        fetch_lean("main")
    elif args.operation == "fetch-lean":
        fetch_lean(args.deps)
    elif args.operation == "lean-integration":
        run(["lake", "build"], cwd=ROOT / "formal/integrations/arklib")
        run([sys.executable, ROOT / "formal/checks/check_clients.py", "--with-arklib",
             "--output", reports_root() / "formal/clients-arklib"], cwd=ROOT / "formal")
    elif args.operation == "lean-fresh":
        run([sys.executable, ROOT / "formal/reproduce.py", "--with-arklib",
             "--output", reports_root() / "formal/fresh"], cwd=ROOT / "formal")
    elif args.operation == "configure":
        configure(args.profile)
    elif args.operation == "compiler":
        configure(args.profile)
        run(["cmake", "--build", "--preset", args.profile], cwd=ROOT / "compiler")
    elif args.operation == "lean":
        run(["lake", "build"], cwd=ROOT / "formal")
    elif args.operation == "rust":
        run(["cargo", "build", "--release", "--locked", "--workspace", "--bins", "--examples"])
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
        run(["cmake", "-S", ROOT / "tests/consumer", "-B", consumer,
             "-G", "Ninja", f"-DZkcCompiler_DIR={package}",
             *[f"-D{key}={value}" for key, value in selected.items()]])
        run(["cmake", "--build", consumer])
        run([consumer / "consumer"])
    elif args.operation == "bench":
        output = Path(args.output or ROOT / "build/bench").resolve()
        output.mkdir(parents=True, exist_ok=True)
        for manifest, binary, filename in [
            ("bench/range-native/Cargo.toml", None, "range-native.json"),
            ("bench/air-proof/Cargo.toml", "air_baseline", "air-baseline.json"),
            ("bench/air-proof/Cargo.toml", "upstream_stark", "upstream-stark.json"),
        ]:
            with (output / filename).open("w") as stream:
                run(["cargo", "run", "--release", "--locked", "--manifest-path", manifest,
                     *(["--bin", binary] if binary else [])], stdout=stream)
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
