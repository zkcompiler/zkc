"""Repeated native operations retain evidence and require explicit preparation."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
from types import SimpleNamespace

import pytest

from harness import executable, load

ROOT = Path(__file__).resolve().parents[3]


@pytest.mark.parametrize("entrypoint,operation", [("scripts/develop.py", "fetch-lean"),
                                                   ("common/tests/run.py", "lean-integration")])
def test_repeated_preparation_keeps_previous_reports(entrypoint, operation, monkeypatch, tmp_path):
    developer = load("driver", entrypoint)
    outputs, calls = [], []

    def run(arguments, **kwargs):
        args = list(map(str, arguments))
        calls.append(args)
        if "--output" in args:
            output = Path(args[args.index("--output") + 1])
            assert not output.exists()
            output.parent.mkdir(parents=True, exist_ok=True)
            if output.suffix != ".json":
                output.mkdir()
                output /= "evidence.json"
            output.write_text(str(len(outputs)))
            outputs.append(output)

    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["develop.py", operation])
    for _ in range(2):
        developer.main()
    assert len(set(outputs)) == 2
    assert [path.read_text() for path in outputs] == ["0", "1"]
    roots = list((tmp_path / "reports/runs").iterdir())
    assert len(roots) == 2
    assert all(json.loads((root / "run.json").read_text())["status"] == "pass" for root in roots)
    assert all(any(path.is_relative_to(root) for root in roots) for path in outputs)


@pytest.mark.parametrize("current", [True, False])
def test_clean_integration_requires_the_committed_control(current, monkeypatch, tmp_path):
    developer = load("test_runner", "common/tests/run.py")
    fixture = tmp_path / "common/tests/fixtures/clean/air-control.json"
    fixture.parent.mkdir(parents=True)
    fixture.write_text('{"format":"zkc.clean-air-control/0"}\n')
    calls = []

    def run(arguments, cwd=None, stdout=None):
        calls.append((list(map(str, arguments)), cwd))
        if stdout is not None:
            stdout.write(fixture.read_text() if current else "{}\n")

    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setattr(developer, "ROOT", tmp_path)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["develop.py", "lean-clean"])
    if current:
        developer.main()
    else:
        with pytest.raises(ValueError, match="air-control.json is not the current Clean export"):
            developer.main()
    assert calls[0] == ([sys.executable, str(tmp_path / "lean/checks/check_library.py"),
                         "--integration", "clean"], None)
    # Check actual package providers and exhaustive import coverage before
    # records and the retained native control.
    assert calls[1:4] == [([sys.executable, str(tmp_path / f"lean/checks/{name}"),
                            "--integration", "clean"], None)
                          for name in ("check_package_ownership.py", "audit_imports.py", "check_records.py")]
    assert calls[4] == (["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                         "--run", "TestsClean/Control.lean"],
                        tmp_path / "lean/integrations/clean")
    if current:
        assert calls[5][0][:7] == ["lake", "env", "lean", "-DautoImplicit=false",
                                   "-DwarningAsError=true", "--run", "CleanExamples.lean"]
        assert calls[6][0][1:3] == [str(tmp_path / "compiler/adapters/clean/regenerate.py"), "check"]
        assert calls[5][0][7] == calls[6][0][3]
    assert len(calls) == (7 if current else 5)
    root, = (tmp_path / "reports/runs").iterdir()
    assert json.loads((root / "run.json").read_text())["status"] == ("pass" if current else "failed")


def test_native_lean_checks_subjects_then_source_views_then_records(monkeypatch, tmp_path):
    developer = load("test_runner", "common/tests/run.py")
    calls, stores = [], set()

    def run(arguments, **kwargs):
        calls.append(list(map(str, arguments)))
        stores.add((kwargs.get("env") or {}).get("ZKC_TOOL_STORE"))

    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setattr(developer, "ROOT", tmp_path)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.delenv("ZKC_TOOL_STORE", raising=False)
    monkeypatch.setattr(sys, "argv", ["run.py", "lean-native", "--compiler-build", str(tmp_path / "compiler")])
    developer.main()
    # Every child shares one tool store, given to it; the store does not leak into
    # this process, where later suites would find their tools already retained.
    store, = stores
    assert Path(store).is_relative_to(tmp_path / "reports")
    assert "ZKC_TOOL_STORE" not in os.environ
    # Subject generation and checked source views precede the records join.
    subject, checked, records = calls[-3:]
    assert subject[:4] == [sys.executable, str(tmp_path / "lean/bridges/subject.py"), "--check", "--runtime"]
    output = Path(subject[subject.index("--output") + 1])
    assert output.is_dir() and output.is_relative_to(tmp_path / "reports")
    assert checked == [sys.executable, str(tmp_path / "lean/checks/check_source_views.py")]
    assert records == [sys.executable, str(tmp_path / "lean/checks/check_records.py"),
                       "--integration", "arklib", "--evidence", str(output / "evidence")]
    assert not any("construction/check.py" in part or "executable/check.py" in part
                   for call in calls for part in call)
    services, = [call for call in calls if any(part.endswith("check_local_service_admission.py") for part in call)]
    assert services == [sys.executable, str(tmp_path / "lean/checks/check_local_service_admission.py"),
                        "--compiler", str(tmp_path / "compiler/zkc-compile"),
                        "--output", str(output.parent / "local-services")]


@pytest.mark.parametrize("explicit", [False, True])
def test_install_uses_empty_prefix_and_fresh_consumer(explicit, monkeypatch, tmp_path, native_config):
    developer = load("test_runner", "common/tests/run.py")
    prefixes, builds, completed, discovery = [], [], [], []
    consumer_prefixes = []
    cpu_headers = ("Compiler/NativeCompilation.h", "Compiler/NativeLanguage.h",
                   "Compiler/Run.h", "Transforms/Protocol.h", "Transforms/PipelineOptions.h")

    def run(arguments, **kwargs):
        args = list(map(str, arguments))
        if "--install" in args:
            prefix = Path(args[args.index("--prefix") + 1])
            assert prefix.is_dir() and not list(prefix.iterdir())
            (prefix / "installed-header").write_text(str(len(prefixes)))
            package = prefix / "lib/cmake/ZkcCompiler"
            package.mkdir(parents=True)
            (package / "ZkcCompilerConfig.cmake").write_text("# installed config")
            for relative in ("bin", "include/zkc/Target/Cpu", "include/zkc/Target/Evm",
                             "include/zkc/Dialect/Evm"):
                (prefix / relative).mkdir(parents=True)
            for relative in (*cpu_headers, "Compiler/Evm.h", "Compiler/Compilation.h"):
                header = prefix / "include/zkc" / relative
                header.parent.mkdir(parents=True, exist_ok=True)
                header.write_text("// installed header")
            for component in ("Compiler", "CpuTarget", "EvmTarget", "Driver", "Tools"):
                (prefix / "lib" / f"libZkc{component}.a").write_bytes(b"archive")
                (package / f"Zkc{component}Targets.cmake").write_text("# installed export")
            prefixes.append(prefix)
        elif "-S" in args:
            build = Path(args[args.index("-B") + 1])
            assert not build.exists(), "a stale consumer cache can mask a broken install"
            build.mkdir()
            hint, = [arg.removeprefix("-DZkcCompiler_DIR=") for arg in args
                     if arg.startswith("-DZkcCompiler_DIR=")]
            selected = Path(hint).parents[2]
            source = Path(args[args.index("-S") + 1]).name
            if source in {"common-only", "evm-only"}:
                assert selected != prefixes[-1]
                assert not (selected / "bin").exists()
                assert not (selected / "include/zkc/Target/Cpu").exists()
                for relative in cpu_headers:
                    assert not (selected / "include/zkc" / relative).exists()
                removed = ("CpuTarget", "Driver", "Tools")
                if source == "common-only":
                    removed += ("EvmTarget",)
                    assert not (selected / "include/zkc/Target").exists()
                    assert not (selected / "include/zkc/Dialect/Evm").exists()
                    assert not (selected / "include/zkc/Compiler/Evm.h").exists()
                else:
                    assert (selected / "include/zkc/Target/Evm").is_dir()
                    assert (selected / "lib/libZkcEvmTarget.a").is_file()
                for component in removed:
                    assert not (selected / "lib" / f"libZkc{component}.a").exists()
                    assert not (Path(hint) / f"Zkc{component}Targets.cmake").exists()
            else:
                assert source == "consumer" and selected == prefixes[-1]
                assert (selected / "lib/libZkcCpuTarget.a").is_file()
            assert (selected / "include/zkc/Compiler/Compilation.h").is_file()
            assert (selected / "lib/libZkcCompiler.a").is_file()
            (build / "CMakeCache.txt").write_text(str(selected))
            consumer_prefixes.append(selected)
            builds.append(build)
        elif "--build" in args:
            assert args == ["cmake", "--build", str(builds[-1]), "--parallel", "2"]
        elif args[-1] in {"--help", "--version"}:
            assert Path(args[0]).parent == prefixes[-1] / "bin"
            discovery.append(args)
        else:
            expected = ["ctest", "--test-dir", str(builds[-1]), "--output-on-failure"]
            if builds[-1].name != "consumer":
                expected.append("--no-tests=error")
            assert args == expected
            completed.append(builds[-1])

    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    for number in range(2):
        args = ["develop.py", "install"]
        if explicit:
            args += ["--output", str(tmp_path / f"selected-{number}")]
        monkeypatch.setattr(sys, "argv", args)
        developer.main()
    assert len(set(prefixes)) == 2
    assert len(set(builds)) == len(completed) == 6
    assert len(discovery) == 8
    assert [path.joinpath("installed-header").read_text() for path in prefixes] == ["0", "1"]
    assert [path.joinpath("CMakeCache.txt").read_text() for path in builds] == list(map(str, consumer_prefixes))
    assert all(path.is_relative_to(tmp_path / "reports/runs") for path in builds)
    if not explicit:
        assert all(prefix.parent == build.parent for prefix, build in zip(prefixes, builds[2::3]))


@pytest.mark.parametrize("kind", ["directory", "file", "symlink", "dangling-symlink"])
def test_install_refuses_existing_prefix_without_running_commands(kind, monkeypatch, tmp_path, native_config):
    developer = load("test_runner", "common/tests/run.py")
    prefix = tmp_path / "prefix"
    retained = tmp_path / "retained"
    retained.mkdir()
    marker = retained / "keep"
    marker.write_text("user data")
    if kind == "directory":
        prefix.mkdir()
        marker = prefix / "keep"
        marker.write_text("user data")
    elif kind == "file":
        prefix.write_text("user data")
        marker = prefix
    else:
        prefix.symlink_to(retained if kind == "symlink" else tmp_path / "absent")
    calls = []
    monkeypatch.setattr(developer, "run", lambda *args, **kwargs: calls.append(args))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["develop.py", "install", "--output", str(prefix)])
    with pytest.raises(ValueError, match="refusing existing install prefix"):
        developer.main()
    assert not calls
    assert marker.read_text() == "user data"
    assert os.path.lexists(prefix)


@pytest.mark.parametrize("scope", ["integration", "harness", "sdk", "style", "lint", "lean-security"])
def test_uv_test_and_lint_commands_never_sync(scope, monkeypatch, tmp_path):
    runner = load("runner", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(runner, "run", lambda args, **kwargs: calls.append(list(map(str, args))))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path))
    runner.execute(scope, SimpleNamespace())
    uv = [args for args in calls if args[0] == "uv"]
    assert len(uv) == 1
    assert uv[0][:5] == ["uv", "run", "--no-sync", "--locked", "ruff" if scope in {"style", "lint"} else "pytest"]
    assert not any("sync" in args or "fetch" in args for args in calls)
    if scope == "lean-security":
        assert "lean/security/checks/test_receipt_reporting.py" in uv[0]


@pytest.mark.parametrize("driver,operation,child", [
    ("common/tests/run.py", "integration", "uv"),
    ("scripts/develop.py", "lean", "lake"),
])
@pytest.mark.parametrize("status", [7, -signal.SIGTERM])
def test_driver_preserves_child_exit_status(driver, operation, child, status, monkeypatch, tmp_path):
    tool = executable(tmp_path / child)
    action = f"sys.exit({status})" if status > 0 else f"os.kill(os.getpid(), {-status})"
    tool.write_text(f"#!{sys.executable}\nimport os, sys\n{action}\n")
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    result = subprocess.run([sys.executable, str(ROOT / driver), operation],
                            capture_output=True, text=True, timeout=10)
    assert result.returncode == (status if status > 0 else 128 - status), result.stderr
    if driver == "common/tests/run.py":
        manifest, = (tmp_path / "reports/runs").glob("*/run.json")
        assert json.loads(manifest.read_text())["status"] == "failed"


def test_ctest_writes_junit_to_each_run(monkeypatch, tmp_path):
    ctest = executable(tmp_path / "ctest")
    ctest.write_text(f'''#!{sys.executable}
import sys
from pathlib import Path
assert sys.argv[1:3] == ["--preset", "release"]
Path(sys.argv[sys.argv.index("--output-junit") + 1]).write_text("<testsuite tests='1'/>")
''')
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    for _ in range(2):
        subprocess.run([sys.executable, str(ROOT / "common/tests/run.py"), "compiler"],
                       capture_output=True, text=True, check=True, timeout=10)
    reports = list((tmp_path / "reports/runs").glob("*/ctest.xml"))
    assert len(reports) == 2
    assert all(report.read_text() == "<testsuite tests='1'/>" for report in reports)


def test_missing_installed_config_cannot_fall_back_to_an_old_package(monkeypatch, tmp_path, native_config):
    developer = load("test_runner", "common/tests/run.py")
    stale = tmp_path / "old-install/lib/cmake/ZkcCompiler"
    stale.mkdir(parents=True)
    config = stale / "ZkcCompilerConfig.cmake"
    config.write_text("# stale config")
    monkeypatch.setenv("CMAKE_PREFIX_PATH", str(tmp_path / "old-install"))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["develop.py", "install"])
    calls = []
    monkeypatch.setattr(developer, "run", lambda args, **kwargs: calls.append(list(map(str, args))))
    with pytest.raises(ValueError, match="install did not produce.*ZkcCompilerConfig.cmake"):
        developer.main()
    assert len(calls) == 1 and calls[0][:2] == ["cmake", "--install"]
    assert config.read_text() == "# stale config"


def test_setup_prepares_only_native_dependencies(monkeypatch):
    developer = load("developer", "scripts/develop.py")
    calls = []
    monkeypatch.setattr(developer, "run", lambda args, **kwargs: calls.append(args))
    developer.execute(SimpleNamespace(operation="setup"))
    assert calls == [["uv", "sync", "--locked"], ["cargo", "fetch", "--locked"]]


def test_unknown_scope_is_rejected(tmp_path):
    result = subprocess.run([sys.executable, str(ROOT / "common/tests/run.py"), "invalid-scope"],
                            capture_output=True, text=True, timeout=10)
    assert result.returncode == 2 and "invalid choice" in result.stderr


def test_current_lean_checks_do_not_run_snapshot_tools():
    developer = load("test_runner_snapshot_selection", "common/tests/run.py")
    selected = {path.name for path in developer.lean_checks()}
    assert {"audit_imports.py", "check_package_ownership.py", "check_records.py"} <= selected
    assert not selected.intersection({"build_replay_tools.py", "check_independent.py", "check_migration.py", "source_responsibility.py",
                                      "check_subject_roots.py", "check_local_service_admission.py"})


def test_generated_view_controls_use_the_prepared_lean_environment(monkeypatch, tmp_path):
    runner = load("test_view_control_environment", "common/tests/run.py")
    calls = []
    monkeypatch.setattr(runner, "run", lambda args, **kwargs: calls.append((list(map(str, args)), kwargs)))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path))
    runner.execute("lean", SimpleNamespace())
    for name in ("check_constructed_views", "check_structured_bindings"):
        (command, options), = [(args, opts) for args, opts in calls
                              if str(ROOT / f"lean/checks/{name}.py") in args]
        assert command == ["lake", "env", sys.executable, str(ROOT / f"lean/checks/{name}.py"),
                           "--records", str(tmp_path / "lean" / name)]
        assert options["cwd"] == ROOT / "lean"
