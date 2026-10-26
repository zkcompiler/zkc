#!/usr/bin/env python3
"""Run maintained checks without synchronizing dependencies.

Just prepares ordinary project builds; Nix supplies installed packages. Checks
may compile their own test targets and consumers. Install-domain explicitly
prepares isolated base/domain builds unless existing builds are selected.
"""

import argparse
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from workspace import compiler_directory, output_directory, reports_root, validate_environment  # noqa: E402
from processes import Interrupted, checked  # noqa: E402
from reporting import new_directory, run_report  # noqa: E402


def run(arguments, *, cwd=ROOT, env=None, stdout=None):
    child = dict(os.environ)
    child["PYTHONPATH"] = os.pathsep.join(map(str, [ROOT / "common/tests/support",
                                                  ROOT / "compiler/test/support", ROOT / "scripts"]))
    if env:
        child.update(env)
    checked(arguments, cwd=cwd, env=child, stdout=stdout)


def lean_checks():
    # These tools require explicitly selected snapshots, exports, or build destinations.
    # They have no default input selection for checking the current checkout.
    snapshot_tools = {"build_replay_tools.py", "check_independent.py", "check_migration.py", "check_subject_roots.py",
                      "source_responsibility.py"}
    # These checks need the native compiler and run in lean-native instead.
    native_checks = {"check_local_service_admission.py"}
    return sorted(path for path in (ROOT / "lean/checks").glob("*.py")
                  if path.name not in snapshot_tools | native_checks) + sorted(
        (ROOT / "lean/consumers").glob("*/check.py"))


NATIVE_STAGES = ("bridges", "subjects", "normal-forms", "reports")


@contextmanager
def native_stage(selection, name):
    """Retain completed work and timing even when a later stage fails."""
    started = time.monotonic()
    selection["running"] = name
    path = Path(selection["path"])
    path.write_text(json.dumps(selection, indent=2) + "\n")
    try:
        yield
    except BaseException:
        selection["failed"] = name
        raise
    else:
        selection["completed"].append(name)
    finally:
        selection["timings"][name] = time.monotonic() - started
        selection["running"] = None
        path.write_text(json.dumps(selection, indent=2) + "\n")


def lean_native(args):
    compiler = Path(args.compiler_build).resolve() if args.compiler_build else compiler_directory(args.profile)
    bridge = ROOT / "lean/bridges/common"
    output = reports_root() / "lean/native"
    # The structured suites of this run share one executable store. Each child is
    # given the store; this process's environment is left unchanged.
    store = {"ZKC_TOOL_STORE": str(output / "tool-store")}
    stages = [stage for stage in NATIVE_STAGES if stage in (args.stage or NATIVE_STAGES)]
    selection = dict(format="zkc.validation-selection/0", stages=stages, subjects=args.subject,
                     coverage="full" if set(stages) == set(NATIVE_STAGES) and not args.subject else "partial",
                     completed=[], timings={})
    output.mkdir(parents=True, exist_ok=True)
    selection["path"] = str(output / "selection.json")
    with native_stage(selection, "preflight"):
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--integration", "arklib",
             "--preflight"], env=store)
    if "bridges" in stages:
        with native_stage(selection, "bridges"):
            run([sys.executable, bridge / "check.py", "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-common_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/common-source", "--cases", "80",
                 "--report", output / "differential.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/check.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/open_protocol.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-open/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/primitives.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-primitives/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/maps.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-maps/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/aggregates.py",
                 "--compiler", compiler / "zkc-compile",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-aggregates/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/scoped.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-scoped/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/tables.py",
                 "--compiler", compiler / "zkc-compile",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-tables/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/applications.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-applications/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/repeats.py",
                 "--compiler", compiler / "zkc-compile",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-repeats/report.json"], env=store)
            run([sys.executable, ROOT / "lean/bridges/structured/inlining.py",
                 "--compiler", compiler / "zkc-compile",
                 "--optimizer", compiler / "zkc-opt",
                 "--reference", compiler / "test/zkc-structured_reference-test",
                 "--lean", ROOT / "lean/.lake/build/bin/structured-source",
                 "--report", output / "structured-inlining/report.json"], env=store)
            run([sys.executable, bridge / "verify_tests.py", "--compiler", compiler / "zkc-compile",
                 "--output", output / "requests"], env=store)
            run([sys.executable, bridge / "intent_tests.py", "--compiler", compiler / "zkc-compile",
                 "--output", output / "intent"], env=store)
            run([sys.executable, ROOT / "lean/checks/check_local_service_admission.py",
                 "--compiler", compiler / "zkc-compile",
                 "--output", output / "local-services"], env=store)
    if "subjects" in stages:
        with native_stage(selection, "subjects"):
            # Every subject manifest: exports, generated modules, kernel checks, generic
            # mutations, the runtime differential and the per-subject evidence records.
            subjects = new_directory(output, "subjects")
            run([sys.executable, ROOT / "lean/bridges/subject.py", "--check", "--runtime",
                 "--compiler", compiler / "zkc-compile", "--native", output_directory("native") / "zkc",
                 "--output", subjects, *[arg for name in args.subject for arg in ("--subject", name)],
                 *(["--fresh-bodies"] if args.fresh_bodies else [])], env=store)
            evidence = subjects / "evidence"
    if "normal-forms" in stages:
        with native_stage(selection, "normal-forms"):
            for request in sorted((ROOT / "lean/bridges/structured/normal-forms").glob("*.toml")):
                run([sys.executable, ROOT / "lean/bridges/structured/normal_forms.py", request, "--check"], env=store)
    if "reports" in stages:
        with native_stage(selection, "reports"):
            # The assurance reports join the declaration records with this run's evidence.
            run([sys.executable, ROOT / "lean/checks/check_records.py", "--integration", "arklib",
                 "--evidence", evidence,
                 *[arg for name in args.subject for arg in ("--subject", name)]], env=store)


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
            if check.name in {"check_constructed_views.py", "check_structured_bindings.py"}:
                # The generated syntax and its refusal controls import the
                # prepared package and must see Lake's dependency search path.
                run(["lake", "env", sys.executable, check,
                     "--records", reports / "lean" / check.stem], cwd=ROOT / "lean")
                continue
            selection = ["--main-only"] if check.name in {"audit_imports.py", "check_library.py", "check_package_ownership.py"} else []
            if check.name == "check_migration_exporter.py":
                selection = ["--package", ROOT / "lean", "--output", reports / "lean/migration-exporter"]
            run([sys.executable, check, *selection])
    elif scope == "lean-security":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--integration", "security"])
        run([sys.executable, ROOT / "lean/checks/check_package_ownership.py", "--integration", "security"])
        run([sys.executable, ROOT / "lean/checks/audit_imports.py", "--integration", "security"])
        run([sys.executable, ROOT / "lean/checks/check_clients.py", "--with-security",
             "--output", reports / "lean/clients-security"], cwd=ROOT / "lean")
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--integration", "security"])
        run(["lake", "env", sys.executable,
             ROOT / "lean/security/checks/check_abi_installations.py",
             reports / "lean/abi-installations"], cwd=ROOT / "lean/security")
        run(["uv", "run", "--no-sync", "--locked", "pytest",
             "lean/security/checks/test_receipt_reporting.py",
             f"--junit-xml={reports / 'lean/receipt-reporting.xml'}"])
    elif scope == "lean-integration":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--integration", "arklib"])
        run([sys.executable, ROOT / "lean/checks/check_package_ownership.py", "--integration", "arklib"])
        run([sys.executable, ROOT / "lean/checks/audit_imports.py", "--integration", "arklib"])
        run([sys.executable, ROOT / "lean/checks/check_clients.py", "--with-arklib",
             "--output", reports / "lean/clients-arklib"], cwd=ROOT / "lean")
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--integration", "arklib"])
    elif scope == "lean-clean":
        run([sys.executable, ROOT / "lean/checks/check_library.py", "--integration", "clean"])
        run([sys.executable, ROOT / "lean/checks/check_package_ownership.py", "--integration", "clean"])
        run([sys.executable, ROOT / "lean/checks/audit_imports.py", "--integration", "clean"])
        run([sys.executable, ROOT / "lean/checks/check_records.py", "--integration", "clean"])
        directory = ROOT / "lean/integrations/clean"
        output = reports / "lean/clean-air-control.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("w") as stream:
            run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                 "--run", "TestsClean/Control.lean"], cwd=directory, stdout=stream)
        control = ROOT / "common/tests/fixtures/clean/air-control.json"
        if output.read_bytes() != control.read_bytes():
            raise ValueError(f"{control.relative_to(ROOT)} is not the current Clean export; "
                             f"review {output} and replace the fixture with it")
        source = reports / "lean/clean-sources"
        run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
             "--run", "CleanExamples.lean", source], cwd=directory)
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
                  "lean-security", "lean-integration", "lean-clean", "lean-native", "install", "install-domain", "docs", "style", "lint"]:
        command = scopes.add_parser(scope)
        if scope == 'smoke':
            sys.path.insert(0, str(ROOT / 'common/tests/support'))
            from smoke import MATRIX
            command.add_argument('--family', choices=sorted(MATRIX))
        if scope in {"compiler", "install", "install-domain", "lean-native"}:
            command.add_argument("--profile", default="release", help="CMake build profile (default: release)")
        if scope == "lean-native":
            command.add_argument("--compiler-build", help="explicit prepared compiler build directory")
            command.add_argument("--stage", action="append", choices=NATIVE_STAGES,
                                 help="run selected stages (default: all; partial runs are recorded)")
            command.add_argument("--subject", action="append", default=[],
                                 help="select subjects and their reports; requires explicit --stage subjects")
            command.add_argument("--fresh-bodies", action="store_true",
                                 help="regenerate bodies without replaying Lake printer output")
        if scope in {"install", "install-domain"}:
            command.add_argument("--output", help="fresh installation output directory")
        if scope == "install-domain":
            command.add_argument("--base-build", help="explicit base CMake build directory")
            command.add_argument("--domain-build", help="explicit envelope CMake build directory")
            command.add_argument("--skip-build", action="store_true",
                                 help="install already built, cache-checked directories without rebuilding")
    args = parser.parse_args()
    if args.scope == "lean-native":
        stages = args.stage or list(NATIVE_STAGES)
        if len(stages) != len(set(stages)):
            parser.error("each --stage may be selected only once")
        if args.subject and (not args.stage or "subjects" not in stages):
            parser.error("--subject requires explicit --stage subjects")
        if "reports" in stages and "subjects" not in stages:
            parser.error("reports requires --stage subjects in the same run")
        if args.fresh_bodies and "subjects" not in stages:
            parser.error("--fresh-bodies requires the subjects stage")
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
