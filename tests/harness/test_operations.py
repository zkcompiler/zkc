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

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("operation", ["setup", "fetch-lean", "lean-integration"])
def test_repeated_preparation_keeps_previous_reports(operation, monkeypatch, tmp_path):
    developer = load("developer", "scripts/develop.py")
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
    if operation == "setup":
        assert [call for call in calls if call[0] == "uv"] == [["uv", "sync", "--locked"]] * 2


@pytest.mark.parametrize("explicit", [False, True])
def test_install_uses_empty_prefix_and_fresh_consumer(explicit, monkeypatch, tmp_path, native_config):
    developer = load("developer", "scripts/develop.py")
    prefixes, builds, completed, discovery = [], [], [], []

    def run(arguments, **kwargs):
        args = list(map(str, arguments))
        if "--install" in args:
            prefix = Path(args[args.index("--prefix") + 1])
            assert prefix.is_dir() and not list(prefix.iterdir())
            (prefix / "installed-header").write_text(str(len(prefixes)))
            package = prefix / "lib/cmake/ZkcCompiler"
            package.mkdir(parents=True)
            (package / "ZkcCompilerConfig.cmake").write_text("# installed config")
            prefixes.append(prefix)
        elif "-S" in args:
            build = Path(args[args.index("-B") + 1])
            assert not build.exists(), "a stale consumer cache can mask a broken install"
            build.mkdir()
            (build / "CMakeCache.txt").write_text(str(prefixes[-1]))
            assert f"-DZkcCompiler_DIR={prefixes[-1]}/lib/cmake/ZkcCompiler" in args
            builds.append(build)
        elif "--build" in args:
            assert Path(args[-1]) == builds[-1]
        elif args[-1] in {"--help", "--version"}:
            assert Path(args[0]).parent == prefixes[-1] / "bin"
            discovery.append(args)
        else:
            assert args == [str(builds[-1] / "consumer")]
            completed.append(builds[-1])

    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    for number in range(2):
        args = ["develop.py", "install"]
        if explicit:
            args += ["--output", str(tmp_path / f"selected-{number}")]
        monkeypatch.setattr(sys, "argv", args)
        developer.main()
    assert len(set(prefixes)) == len(set(builds)) == len(completed) == 2
    assert len(discovery) == 8
    assert [path.joinpath("installed-header").read_text() for path in prefixes] == ["0", "1"]
    assert [path.joinpath("CMakeCache.txt").read_text() for path in builds] == list(map(str, prefixes))
    assert all(path.is_relative_to(tmp_path / "reports/runs") for path in builds)
    if not explicit:
        assert all(prefix.parent == build.parent for prefix, build in zip(prefixes, builds))


@pytest.mark.parametrize("kind", ["directory", "file", "symlink", "dangling-symlink"])
def test_install_refuses_existing_prefix_without_running_commands(kind, monkeypatch, tmp_path, native_config):
    developer = load("developer", "scripts/develop.py")
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


@pytest.mark.parametrize("scope", ["cross", "harness", "lint"])
def test_uv_test_and_lint_commands_never_sync(scope, monkeypatch, tmp_path):
    runner = load("runner", "tests/run.py")
    calls = []
    monkeypatch.setattr(runner, "run", lambda args, **kwargs: calls.append(list(map(str, args))))
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path))
    runner.execute(scope, SimpleNamespace())
    uv = [args for args in calls if args[0] == "uv"]
    assert len(uv) == 1
    assert uv[0][:5] == ["uv", "run", "--no-sync", "--locked", "ruff" if scope == "lint" else "pytest"]
    assert not any("sync" in args or "fetch" in args for args in calls)


@pytest.mark.parametrize("driver,operation,child", [
    ("tests/run.py", "cross", "uv"),
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
    if driver == "tests/run.py":
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
        subprocess.run([sys.executable, str(ROOT / "tests/run.py"), "compiler"],
                       capture_output=True, text=True, check=True, timeout=10)
    reports = list((tmp_path / "reports/runs").glob("*/ctest.xml"))
    assert len(reports) == 2
    assert all(report.read_text() == "<testsuite tests='1'/>" for report in reports)


def test_demo_writes_under_current_run_reports(monkeypatch, tmp_path):
    runner = load("runner", "tests/run.py")
    tools = SimpleNamespace(compiler="compiler", runtime="runtime", checker=lambda _: "lean",
                            example=lambda _: "fixture")
    monkeypatch.setattr(runner, "Toolchain", lambda: tools)
    outputs = []

    def run(args, stdout=None, **kwargs):
        if args[0] == "fixture":
            Path(args[1]).mkdir()
        if stdout:
            outputs.append(Path(stdout.name))
            if args[1] == "protocol-construct":
                stdout.write(json.dumps(["construction", [], ["common"]]))
            elif args[1] in {"produce-artifact", "validate-artifact"}:
                Path(args[-3]).write_bytes(b"proof")
                stdout.write(json.dumps({"status": "produced" if args[1] == "produce-artifact"
                                         else "accepted"}))
            else:
                stdout.write("[]")

    monkeypatch.setattr(runner, "run", run)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "run"))
    runner.execute("demo", SimpleNamespace())
    output = tmp_path / "run/demo"
    assert all(path.parent == output for path in outputs)
    assert json.loads((output / "common.json").read_text()) == ["common"]
    assert (output / "proof.bin").read_bytes() == b"proof"
    assert json.loads((output / "validator.json").read_text())["status"] == "accepted"
    # Reusing the same invocation output must not overwrite a prior proof.
    with pytest.raises(FileExistsError):
        runner.execute("demo", SimpleNamespace())


def test_missing_installed_config_cannot_fall_back_to_an_old_package(monkeypatch, tmp_path, native_config):
    developer = load("developer", "scripts/develop.py")
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
