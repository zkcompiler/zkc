#!/usr/bin/env python3
"""Run maintained test scopes against built outputs, without building them.

Both just and Nix call this driver. Tool selection and report locations use the
same contract as direct pytest and Cargo invocations. No scope installs tools,
updates locks, or substitutes a missing tool with an executable on PATH.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests/support"))
from toolchain import Missing, Toolchain  # noqa: E402
from workspace import compiler_directory, reports_root, validate_environment  # noqa: E402
from processes import Interrupted, run as run_process  # noqa: E402
from reporting import new_directory  # noqa: E402


def run(arguments, *, cwd=ROOT, env=None, stdout=None):
    arguments = list(map(str, arguments))
    print(f"+ {shlex.join(arguments)}", flush=True)
    child = dict(os.environ)
    # Standalone generator scripts share the native harness modules.
    child["PYTHONPATH"] = os.pathsep.join(map(str, [ROOT / "tests/support",
                                                  ROOT / "compiler/test/support", ROOT / "scripts"]))
    if env:
        child.update(env)
    run_process(arguments, cwd=cwd, env=child, stdout=stdout, check=True, cleanup_grace=5)


def formal_checks():
    return sorted((ROOT / "formal/checks").glob("*.py")) + sorted(
        (ROOT / "formal/consumers").glob("*/check.py")) + [
            ROOT / "tests/support/formal/check_cli.py"]


def demo(output):
    """Compile a source Entry and execute independent common-Host proof calls."""
    tools = Toolchain()
    output.mkdir(parents=True, exist_ok=False)

    def emit(name, arguments):
        path = output / name
        with path.open("w") as stream:
            run(arguments, stdout=stream)
        return json.loads(path.read_text())

    package, proof = output / "proof.entry", output / "proof.bin"
    built = emit("build.json", [tools.runtime, "compile", f"--compiler={tools.compiler}",
        "--module=schnorr=libraries/schnorr/lib.zkc",
        "--module=example=examples/projects/schnorr/main.zkc",
        "--entry=example::Proof", f"--output={package}"])
    for command, request, role, expected in [("prove", "prover", "producer", "produced"),
                                              ("verify", "verifier", "validator", "accepted")]:
        report = emit(f"{role}.json", [tools.runtime, command, package, built["package_sha256"],
            ROOT / f"examples/projects/schnorr/{request}.json", proof])
        if report["status"] != expected:
            raise RuntimeError(f"{command} did not report {expected}; see {output}")
    print(f"Proof accepted: {proof.stat().st_size} bytes. Files: {output}", flush=True)


def execute(scope, args):
    reports = reports_root()
    if scope in ("integration", "harness"):
        reports.mkdir(parents=True, exist_ok=True)
        # Without the Nix development defaults use one worker, not the host's
        # entire CPU count (each worker may run threaded native tools).
        workers = os.environ.get("PYTEST_XDIST_AUTO_NUM_WORKERS", "1")
        if not workers.isdecimal() or int(workers) < 1:
            raise ValueError("PYTEST_XDIST_AUTO_NUM_WORKERS must be a positive integer")
        selection = "tests/harness" if scope == "harness" else "tests"
        report = "harness.xml" if scope == "harness" else "tests.xml"
        run(["uv", "run", "--no-sync", "--locked", "pytest", selection, "-n", workers,
             f"--junit-xml={reports / report}"])
    elif scope == "rust":
        run(["cargo", "test", "--workspace", "--locked", "--all-features", "--no-fail-fast"])
    elif scope == "compiler":
        compiler_directory(args.profile)
        run(["ctest", "--preset", args.profile, "--output-junit", reports / "ctest.xml"], cwd=ROOT / "compiler")
    elif scope == "lean":
        output = reports / "formal"
        output.mkdir(parents=True, exist_ok=True)
        for check in formal_checks():
            run([sys.executable, check], env={"PYTHONPATH": str(ROOT / "tests/support/formal")})
    elif scope == "docs":
        run([sys.executable, "tests/check_docs.py", "--all"])
    elif scope == "demo":
        demo(reports / "demo")
    elif scope == "lint":
        run([sys.executable, "scripts/format.py"])
        run(["cargo", "fmt", "--all", "--", "--check"])
        run(["cargo", "clippy", "--workspace", "--locked", "--all-targets",
             "--all-features", "--", "-D", "warnings"])
        run(["uv", "run", "--no-sync", "--locked", "ruff", "check", "."])
    elif scope == "project":
        # Nix's independent style check owns documentation and lint.
        for part in ["integration", "demo"]:
            execute(part, args)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scope", choices=["integration", "harness", "rust", "compiler", "lean",
                                          "docs", "demo", "lint", "project"])
    parser.add_argument("--profile", default="release")
    args = parser.parse_args()
    validate_environment()
    # Normalize native Cargo's cwd-relative setting before changing cwd.
    if os.environ.get("CARGO_TARGET_DIR"):
        os.environ["CARGO_TARGET_DIR"] = str(Path(os.environ["CARGO_TARGET_DIR"]).resolve())
    output = new_directory(reports_root() / "runs", args.scope)
    os.environ["ZKC_REPORTS_DIR"] = str(output)
    print(f"Reports: {output}", flush=True)
    record = {"scope": args.scope, "argv": sys.argv, "status": "running",
              "started_utc": datetime.now(timezone.utc).isoformat()}
    manifest = output / "run.json"
    manifest.write_text(json.dumps(record, indent=2) + "\n")
    try:
        execute(args.scope, args)
        record["status"] = "pass"
    except BaseException as error:
        record["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        record["error"] = str(error)
        raise
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        manifest.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    try:
        main()
    except Interrupted as error:
        sys.exit(128 + error.signum)
    except subprocess.CalledProcessError as error:
        print(error, file=sys.stderr)
        sys.exit(error.returncode if error.returncode >= 0 else 128 - error.returncode)
    except (Missing, ValueError, OSError) as error:
        sys.exit(str(error))
