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


# Maintained Lean packages whose closure does not reach Program (support.packages.audited).
DEPENDENCY_FREE = ("core", "formal")


def lean_checks():
    # These tools operate on explicitly supplied snapshots or prepared sources.
    snapshot_tools = {"build_replay_tools.py", "check_independent.py", "check_migration.py",
                      "source_responsibility.py", "check_source_construction_cost.py"}
    # Native comparisons run binaries that this lane does not build.
    native = {"check_source_admission.py"}
    return sorted(path for path in (ROOT / "lean/checks").glob("*.py")
                  if path.name not in snapshot_tools | native)


def lean_native(args):
    compiler = Path(args.compiler_build).resolve() if args.compiler_build else compiler_directory(args.profile)
    output = reports_root() / "lean/native"
    # Admission and execution comparisons are distinct from declaration/security
    # checks. This lane never synthesizes or installs protocol proofs.
    run([sys.executable, ROOT / "lean/checks/check_source_admission.py",
         "--compiler", compiler / "zkc-compile",
         "--reference", compiler / "test/zkc-structured_reference-test",
         "--output", output])


def execute(scope, args):
    reports = reports_root()
    if scope in {"integration", "harness", "sdk", "smoke"}:
        workers = os.environ.get("PYTEST_XDIST_AUTO_NUM_WORKERS", "1")
        if not workers.isdecimal() or int(workers) < 1:
            raise ValueError("PYTEST_XDIST_AUTO_NUM_WORKERS must be a positive integer")
        selection = {
            "harness": ["common/tests/harness"],
            "sdk": ["common/tests/consumer"],
            "integration": ["common/tests/protocol", "common/tests/kernels"],
        }.get(scope)
        if scope == "smoke":
            sys.path.insert(0, str(ROOT / 'common/tests/support'))
            from smoke import MATRIX, cases
            selection = cases([args.family] if args.family else MATRIX)
        run(["uv", "run", "--no-sync", "--locked", "pytest", *selection, "-n", workers,
             f"--junit-xml={reports / (scope + '.xml')}"])
    elif scope == "rust":
        run(["cargo", "test", "--workspace", "--locked", "--all-features", "--no-fail-fast"])
        # Timing controls refuse execution-count instrumentation, so their
        # ordinary-build tests need a separate lane from the feature-on refusal.
        run(["cargo", "test", "--locked", "-p", "zkc-benchmarks"])
        # Keep the feature-off collector's zero-cost contract in the maintained lane.
        run(["cargo", "test", "--locked", "-p", "zkc-runtime", "--lib", "execution_counts"])
    elif scope == "compiler":
        compiler_directory(args.profile)
        run(["ctest", "--preset", args.profile, "--output-junit", reports / "ctest.xml"], cwd=ROOT / "compiler")
    elif scope == "lean":
        for check in lean_checks():
            selection = ["--core-only"] if check.name in {"audit_imports.py", "check_library.py", "check_package_ownership.py", "check_records.py", "check_clients.py"} else []
            if check.name == "check_migration_exporter.py":
                selection = ["--package", ROOT / "lean/program", "--output", reports / "lean/migration-exporter"]
            run([sys.executable, check, *selection])
        # The packages outside Program's closure are outside the core-only selection:
        # they have no standalone client, and core's declaration names overlap the IR
        # core model's in the theorem ledger. Each selection includes its closure, so
        # the checks of formal also cover the core it requires.
        for name in DEPENDENCY_FREE:
            for check in ("check_library.py", "check_package_ownership.py", "audit_imports.py"):
                run([sys.executable, ROOT / "lean/checks" / check, "--package", name])
        # Formal's driver prints its receipts and fails when a check of a hypothesis does not hold.
        run(["lake", "test"], cwd=ROOT / "lean/formal")
    elif scope == "lean-verification":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--package", "verification"])
        run([sys.executable, ROOT / "lean/checks/check_package_ownership.py", "--package", "verification"])
        run([sys.executable, ROOT / "lean/checks/audit_imports.py", "--package", "verification"])
        run([sys.executable, ROOT / "lean/checks/check_clients.py", "--package", "verification",
             "--output", reports / "lean/clients-verification"], cwd=ROOT / "lean")
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--package", "verification"])
    elif scope == "lean-integration":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--package", "applications"])
        run([sys.executable, ROOT / "lean/checks/check_package_ownership.py", "--package", "applications"])
        run([sys.executable, ROOT / "lean/checks/audit_imports.py", "--package", "applications"])
        run([sys.executable, ROOT / "lean/checks/check_clients.py", "--package", "applications",
             "--output", reports / "lean/clients-arklib"], cwd=ROOT / "lean")
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--package", "applications"])
    elif scope == "lean-clean":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--package", "applications"])
        run([sys.executable, ROOT / "lean/checks/check_package_ownership.py", "--package", "applications"])
        run([sys.executable, ROOT / "lean/checks/audit_imports.py", "--package", "applications"])
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--package", "applications"])
        directory = ROOT / "lean/adapters/clean"
        output = reports / "lean/clean-air-control.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("w") as stream:
            run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                 "--run", "Zkc/Tests/Clean/Control.lean"], cwd=directory, stdout=stream)
        control = ROOT / "common/tests/fixtures/clean/air-control.json"
        if output.read_bytes() != control.read_bytes():
            raise ValueError(f"{control.relative_to(ROOT)} is not the current Clean export; "
                             f"review {output} and replace the fixture with it")
        source = reports / "lean/clean-sources"
        run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
             "--run", "Zkc/Applications/Clean.lean", source], cwd=ROOT / "lean/applications")
        run([sys.executable, ROOT / "compiler/adapters/clean/regenerate.py", "check", source,
             ROOT / "compiler/adapters/clean/fixtures"])
    elif scope == "lean-native":
        lean_native(args)
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
        run(["cargo", "clippy", "--locked", "-p", "zkc-runtime", "--all-targets",
             "--", "-D", "warnings"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    scopes = parser.add_subparsers(dest="scope", required=True)
    for scope in ["integration", "harness", "sdk", "smoke", "rust", "compiler", "lean",
                  "lean-verification", "lean-integration", "lean-clean", "lean-native", "install", "install-domain", "docs", "style", "lint"]:
        command = scopes.add_parser(scope)
        if scope == 'smoke':
            sys.path.insert(0, str(ROOT / 'common/tests/support'))
            from smoke import MATRIX
            command.add_argument('--family', choices=sorted(MATRIX))
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
