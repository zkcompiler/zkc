#!/usr/bin/env python3
"""Run maintained test scopes against built outputs, without building them.

Both just and Nix call this driver. Tool selection and report locations use the
same contract as direct pytest and Cargo invocations. No scope installs tools,
updates locks, or substitutes a missing checker with an executable on PATH.
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
    # These imports are needed by standalone artifact scripts, not by every
    # program a developer runs in the shell.
    child["PYTHONPATH"] = os.pathsep.join(map(str, [ROOT / "tests/support",
                                                  ROOT / "compiler/test/support"]))
    if env:
        child.update(env)
    run_process(arguments, cwd=cwd, env=child, stdout=stdout, check=True, cleanup_grace=5)


def artifact(output):
    tools = Toolchain()
    # Resolve every input before creating the report.
    zkc = tools.runtime
    compiler = tools.compiler
    lean = tools.checker("interactive-protocol")
    primitive = tools.primitive
    fixture = tools.example("artifact_fixture")
    baseline = tools.example("artifact_baseline")
    reference = tools.checker("artifact-reference")
    output.mkdir(parents=True, exist_ok=False)
    (output / "direct").mkdir(parents=True)
    run([sys.executable, "crates/zkc-tools/tests/artifact_host.py", "--zkc", zkc,
         "--fixture-exporter", fixture, "--compiler", compiler, "--lean", lean,
         "--output-dir", output / "host"])
    run([sys.executable, "crates/zkc-tools/tests/artifact_limits.py", "--zkc", zkc,
         "--compiler", compiler, "--lean", lean, "--primitive", primitive,
         "--output", output / "limits"])
    run([sys.executable, "crates/zkc-tools/tests/artifact_profile.py", "--native", zkc,
         "--compiler", compiler, "--lean-checker", lean, "--lean-reference", reference,
         "--output", output / "profile"])
    run([sys.executable, "crates/zkc-tools/tests/artifact_identity.py", "--zkc", zkc,
         "--compiler", compiler, "--lean", lean, "--reference", reference,
         "--primitive", primitive, "--fixture-exporter", fixture,
         "--output-dir", output / "identity"])
    run([sys.executable, "crates/zkc-tools/tests/artifact_reference.py", "--zkc", zkc,
         "--compiler", compiler, "--lean", lean, "--fixture-exporter", fixture,
         "--reference-driver", "tests/support/run_reference.py", "--reference", reference,
         "--primitive", primitive, "--output-dir", output / "reference"])
    run([sys.executable, "tests/artifact/artifact_differential.py", "--native", zkc,
         "--compiler", compiler, "--lean-checker", lean, "--lean-reference", reference,
         "--primitive", primitive, "--fixtures", output / "reference",
         "--output", output / "differential", "--skip-prefixes", "--mutations", "16"])
    for family in ["dleq", "committed-two-factor"]:
        run([baseline, "fixture", ROOT / f"crates/zkc-tools/tests/fixtures/artifact/{family}.json",
             ROOT / f"crates/zkc-tools/tests/fixtures/artifact/{family}.construction.json", output / "direct" / family])
    run([sys.executable, "tests/artifact/artifact_baseline.py", "--baseline", baseline,
         "--fixtures", output / "direct", "--output", output / "baseline", "--host", zkc,
         "--compiler", compiler, "--participant-checker", lean,
         "--lean", reference, "--primitive", primitive])


def formal_checks():
    return sorted((ROOT / "formal/checks").glob("*.py")) + sorted(
        (ROOT / "formal/consumers").glob("*/check.py"))


def demo(output):
    """Compile the authored committed argument and run separate proof processes."""
    tools = Toolchain()
    compiler, runtime = tools.compiler, tools.runtime
    lean, fixture = tools.checker("interactive-protocol"), tools.example("artifact_fixture")
    output.mkdir(parents=True, exist_ok=False)
    inputs = output / "inputs"
    run([fixture, inputs])  # Explicit development setup, never an implicit host action.
    source = ROOT / "examples/protocols/committed-two-factor.pir"
    descriptor = ROOT / "examples/protocols/committed-two-factor.construction.pir"

    def emit(name, arguments):
        path = output / name
        with path.open("w") as stream:
            run(arguments, stdout=stream)
        return path

    original = emit("source.json", [compiler, "protocol-source", source])
    selection = emit("descriptor.json", [compiler, "protocol-source", descriptor])
    construction = emit("construction.json", [compiler, "protocol-construct", source, descriptor])
    common = output / "common.json"
    common.write_text(json.dumps(json.loads(construction.read_text())[2]) + "\n")
    participants = emit("participants.json", [compiler, "protocol-compile", common])
    proof = output / "proof.bin"
    for command, role, expected in [("produce-artifact", "producer", "produced"),
                                    ("validate-artifact", "validator", "accepted")]:
        report = emit(f"{role}.json", [runtime, command, original, selection, construction,
                      participants, inputs / f"committed-two-factor.{role}.json",
                      compiler, lean, proof, "10000", "--trace=none"])
        if json.loads(report.read_text())["status"] != expected:
            raise RuntimeError(f"{command} did not report {expected}; see {report}")
    print(f"Proof accepted: {proof.stat().st_size} bytes. Files: {output}", flush=True)


def execute(scope, args):
    reports = reports_root()
    if scope in ("cross", "harness"):
        reports.mkdir(parents=True, exist_ok=True)
        # Without the Nix development defaults use one worker, not the host's
        # entire CPU count (each worker may itself run threaded checkers).
        workers = os.environ.get("PYTEST_XDIST_AUTO_NUM_WORKERS", "1")
        if not workers.isdecimal() or int(workers) < 1:
            raise ValueError("PYTEST_XDIST_AUTO_NUM_WORKERS must be a positive integer")
        selection = "tests/harness" if scope == "harness" else "tests"
        report = "harness.xml" if scope == "harness" else "tests.xml"
        run(["uv", "run", "--no-sync", "--locked", "pytest", selection, "-n", workers,
             f"--junit-xml={reports / report}"])
    elif scope == "artifact":
        artifact(Path(args.output).resolve() if args.output else reports / "artifact")
    elif scope == "rust":
        run(["cargo", "test", "--workspace", "--locked", "--all-features", "--no-fail-fast"])
    elif scope == "bench":
        # These intentionally separate workspaces are not reached by the root
        # Cargo command. Exercise their correctness controls, not measurements.
        for manifest in sorted((ROOT / "bench").glob("*/Cargo.toml")):
            run(["cargo", "test", "--manifest-path", manifest, "--locked", "--all-features"])
    elif scope == "compiler":
        compiler_directory(args.profile)
        run(["ctest", "--preset", args.profile, "--output-junit", reports / "ctest.xml"], cwd=ROOT / "compiler")
    elif scope == "lean":
        output = reports / "formal"
        output.mkdir(parents=True, exist_ok=True)
        for check in formal_checks():
            run([sys.executable, check])
    elif scope == "evidence":
        run([sys.executable, "tests/groth16/reproduce.py", "check-evidence"])
    elif scope == "docs":
        run([sys.executable, "tests/check_docs.py", "--all"])
    elif scope == "demo":
        demo(reports / "demo")
    elif scope == "groth16":
        if not args.fixture:
            raise ValueError("groth16 requires --fixture PATH")
        fixture = Path(args.fixture).resolve()
        if not fixture.is_dir():
            raise ValueError(f"Groth16 fixture directory does not exist: {fixture}")
        run(["cargo", "test", "-p", "zkc-tools", "--features", "test-utils", "--locked",
             "--test", "groth16", "--test", "snarkjs_import", "--test", "frontend_projects", "--", "--include-ignored"],
            env={"ZKC_GROTH16_FIXTURE": str(fixture)})
    elif scope == "lint":
        run(["cargo", "fmt", "--all", "--", "--check"])
        run(["cargo", "clippy", "--workspace", "--locked", "--all-targets",
             "--all-features", "--", "-D", "warnings"])
        run(["uv", "run", "--no-sync", "--locked", "ruff", "check", "."])
    elif scope == "project":
        # Nix's independent style check owns documentation and lint.
        for part in ["cross", "artifact", "lean", "evidence", "demo"]:
            execute(part, args)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scope", choices=["cross", "harness", "artifact", "rust", "bench", "compiler", "lean",
                                          "evidence", "docs", "demo", "groth16", "lint", "project"])
    parser.add_argument("--profile", default="release")
    parser.add_argument("--output", help="artifact report directory")
    parser.add_argument("--fixture", help="reproduced Groth16 fixture directory")
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
