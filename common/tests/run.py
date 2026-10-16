#!/usr/bin/env python3
"""Run maintained checks without synchronizing dependencies.

Just prepares ordinary project builds; Nix supplies installed packages. Checks
may compile their own test targets and consumers. Install-domain explicitly
prepares isolated base/domain builds unless existing builds are selected.
"""

import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from workspace import compiler_directory, reports_root, validate_environment  # noqa: E402
from processes import Interrupted, checked  # noqa: E402
from reporting import run_report  # noqa: E402


def run(arguments, *, cwd=ROOT, env=None, stdout=None):
    child = dict(os.environ)
    child["PYTHONPATH"] = os.pathsep.join(map(str, [ROOT / "common/tests/support",
                                                  ROOT / "compiler/test/support", ROOT / "scripts"]))
    if env:
        child.update(env)
    checked(arguments, cwd=cwd, env=child, stdout=stdout)


def lean_checks():
    return sorted((ROOT / "lean/checks").glob("*.py")) + sorted(
        (ROOT / "lean/consumers").glob("*/check.py"))


def execute(scope, args):
    reports = reports_root()
    if scope in {"integration", "harness", "sdk"}:
        workers = os.environ.get("PYTEST_XDIST_AUTO_NUM_WORKERS", "1")
        if not workers.isdecimal() or int(workers) < 1:
            raise ValueError("PYTEST_XDIST_AUTO_NUM_WORKERS must be a positive integer")
        selection = {
            "harness": ["common/tests/harness"],
            "sdk": ["common/tests/consumer"],
            "integration": ["common/tests/protocol", "common/tests/kernels"],
        }[scope]
        run(["uv", "run", "--no-sync", "--locked", "pytest", *selection, "-n", workers,
             f"--junit-xml={reports / (scope + '.xml')}"])
    elif scope == "rust":
        run(["cargo", "test", "--workspace", "--locked", "--all-features", "--no-fail-fast"])
    elif scope == "compiler":
        compiler_directory(args.profile)
        run(["ctest", "--preset", args.profile, "--output-junit", reports / "ctest.xml"], cwd=ROOT / "compiler")
    elif scope == "lean":
        for check in lean_checks():
            selection = ["--main-only"] if check.name in {"audit_imports.py", "check_library.py"} else []
            run([sys.executable, check, *selection])
    elif scope == "lean-integration":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--integration", "arklib"])
        run([sys.executable, ROOT / "lean/checks/check_clients.py", "--with-arklib",
             "--output", reports / "lean/clients-arklib"], cwd=ROOT / "lean")
    elif scope == "lean-clean":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--integration", "clean"])
        directory = ROOT / "lean/integrations/clean"
        output = reports / "lean/clean-air-control.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("w") as stream:
            run(["lake", "env", "lean", "--run", "TestsClean/Control.lean"], cwd=directory, stdout=stream)
        control = ROOT / "common/tests/fixtures/clean/air-control.json"
        if output.read_bytes() != control.read_bytes():
            raise ValueError(f"{control.relative_to(ROOT)} is not the current Clean export; "
                             f"review {output} and replace the fixture with it")
        source = reports / "lean/clean-sources"
        run(["lake", "env", "lean", "--run", "CleanExamples.lean", source], cwd=directory)
        run([sys.executable, ROOT / "compiler/adapters/clean/regenerate.py", "check", source,
             ROOT / "compiler/adapters/clean/fixtures"])
    elif scope == "lean-native":
        compiler = Path(args.compiler_build).resolve() if args.compiler_build else compiler_directory(args.profile)
        bridge = ROOT / "lean/bridges/common"
        output = reports / "lean/native"
        run([sys.executable, bridge / "check.py", "--compiler", compiler / "zkc-compile",
             "--reference", compiler / "test/zkc-common_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/common-source", "--cases", "80",
             "--report", output / "differential.json"])
        run([sys.executable, ROOT / "lean/bridges/structured/check.py",
             "--compiler", compiler / "zkc-compile",
             "--reference", compiler / "test/zkc-structured_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/structured-source",
             "--report", output / "structured/report.json"])
        run([sys.executable, ROOT / "lean/bridges/structured/open_protocol.py",
             "--compiler", compiler / "zkc-compile",
             "--reference", compiler / "test/zkc-structured_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/structured-source",
             "--report", output / "structured-open/report.json"])
        run([sys.executable, ROOT / "lean/bridges/structured/primitives.py",
             "--compiler", compiler / "zkc-compile",
             "--reference", compiler / "test/zkc-structured_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/structured-source",
             "--report", output / "structured-primitives/report.json"])
        run([sys.executable, ROOT / "lean/bridges/structured/maps.py",
             "--compiler", compiler / "zkc-compile",
             "--reference", compiler / "test/zkc-structured_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/structured-source",
             "--report", output / "structured-maps/report.json"])
        run([sys.executable, ROOT / "lean/bridges/structured/applications.py",
             "--compiler", compiler / "zkc-compile",
             "--reference", compiler / "test/zkc-structured_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/structured-source",
             "--report", output / "structured-applications/report.json"])
        run([sys.executable, ROOT / "lean/bridges/structured/inlining.py",
             "--compiler", compiler / "zkc-compile",
             "--optimizer", compiler / "zkc-opt",
             "--reference", compiler / "test/zkc-structured_reference-test",
             "--lean", ROOT / "lean/.lake/build/bin/structured-source",
             "--report", output / "structured-inlining/report.json"])
        run([sys.executable, bridge / "verify_tests.py", "--compiler", compiler / "zkc-compile",
             "--output", output / "requests"])
        run([sys.executable, bridge / "intent_tests.py", "--compiler", compiler / "zkc-compile",
             "--output", output / "intent"])
    elif scope == "install":
        from check_sdk import check_install
        check_install(args, run)
    elif scope == "install-domain":
        from check_domain import install_domain
        install_domain(args, run)
    elif scope == "docs":
        run([sys.executable, "common/tests/check_docs.py", "--all"])
    elif scope == "style":
        run(["just", "--list"])
        nix = [ROOT / "flake.nix", *sorted((ROOT / "nix").rglob("*.nix"))]
        run(["nixfmt", "--check", *nix])
        run(["actionlint", "-shellcheck=", *sorted((ROOT / ".github/workflows").glob("*.yml"))])
        run(["cargo", "fmt", "--all", "--", "--check"])
        run(["uv", "run", "--no-sync", "--locked", "ruff", "check", "."])
    elif scope == "lint":
        execute("style", args)
        run([sys.executable, "scripts/format.py"])
        run(["cargo", "clippy", "--workspace", "--locked", "--all-targets",
             "--all-features", "--", "-D", "warnings"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    scopes = parser.add_subparsers(dest="scope", required=True)
    for scope in ["integration", "harness", "sdk", "rust", "compiler", "lean",
                  "lean-integration", "lean-clean", "lean-native", "install", "install-domain", "docs", "style", "lint"]:
        command = scopes.add_parser(scope)
        if scope in {"compiler", "install", "install-domain", "lean-native"}:
            command.add_argument("--profile", default="release", help="CMake build profile (default: release)")
        if scope == "lean-native":
            command.add_argument("--compiler-build", help="explicit prepared compiler build directory")
        if scope in {"install", "install-domain"}:
            command.add_argument("--output", help="fresh installation output directory")
        if scope == "install-domain":
            command.add_argument("--base-build", help="explicit base CMake build directory")
            command.add_argument("--domain-build", help="explicit envelope CMake build directory")
            command.add_argument("--skip-build", action="store_true",
                                 help="install already built, cache-checked directories without rebuilding")
    args = parser.parse_args()
    validate_environment()
    if os.environ.get("CARGO_TARGET_DIR"):
        os.environ["CARGO_TARGET_DIR"] = str(Path(os.environ["CARGO_TARGET_DIR"]).resolve())
    with run_report(reports_root(), args.scope, sys.argv):
        execute(args.scope, args)


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
