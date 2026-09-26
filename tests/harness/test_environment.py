"""Configuration boundaries are identical for native and packaged test callers."""

import json
import os
from pathlib import Path
import re
import subprocess
import sys

import pytest

from harness import executable, fake_command, load
from toolchain import Missing, Toolchain, records_root
import workspace

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("old", workspace.REMOVED)
def test_removed_alias_cannot_select_a_different_tool(old, monkeypatch):
    monkeypatch.setenv(old, "/obsolete/path")
    with pytest.raises(ValueError, match=old):
        Toolchain()


@pytest.mark.parametrize("name", ["ZKC_COMPILER_BIN", "ZKC_NATIVE_BIN", "ZKC_LEAN_BIN", "ZKC_REPORTS_DIR"])
def test_empty_explicit_paths_are_errors(name, monkeypatch):
    monkeypatch.setenv(name, "")
    with pytest.raises(ValueError, match="nonempty"):
        Toolchain()


def test_project_paths_use_checkout_root_from_another_cwd(monkeypatch, tmp_path):
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("ZKC_COMPILER_BIN", "build/selected compiler")
    assert Toolchain().directories["compiler"] == ROOT / "build/selected compiler"
    monkeypatch.setenv("ZKC_REPORTS_DIR", "build/selected reports")
    assert records_root() == ROOT / "build/selected reports/tests"


def test_cargo_target_keeps_native_cwd_semantics(monkeypatch, tmp_path):
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("CARGO_TARGET_DIR", "cargo outputs")
    assert Toolchain().directories["native"] == tmp_path / "cargo outputs/release"
    monkeypatch.setenv("ZKC_NATIVE_BIN", "build/installed/bin")
    assert Toolchain().directories["native"] == ROOT / "build/installed/bin"


def test_invalid_override_never_uses_another_build_or_path(monkeypatch, tmp_path):
    executable(tmp_path / "path/zkc-compile")
    monkeypatch.setenv("PATH", str(tmp_path / "path"))
    monkeypatch.setenv("ZKC_COMPILER_BIN", str(tmp_path / "missing"))
    with pytest.raises(Missing, match="missing"):
        Toolchain().compiler
    (tmp_path / "missing").mkdir()
    (tmp_path / "missing/zkc-compile").mkdir()
    with pytest.raises(Missing):
        Toolchain().compiler
    (tmp_path / "missing/zkc-compile").rmdir()
    executable(tmp_path / "missing/zkc-compile")
    assert Toolchain().compiler == tmp_path / "missing/zkc-compile"


def test_ctest_uses_exact_target_and_refuses_a_missing_one(monkeypatch, tmp_path):
    compiler_tools = load("compiler_tools", "compiler/test/support/tools.py")
    ordinary = executable(tmp_path / "bin/zkc-compile")
    target = executable(tmp_path / "different target/selected-compile")
    monkeypatch.setenv("ZKC_COMPILER_BIN", str(ordinary.parent))
    monkeypatch.setenv("ZKC_CTEST_COMPILER", str(target))
    assert compiler_tools.tool("compiler") == target
    target.unlink()
    with pytest.raises(compiler_tools.Missing):
        compiler_tools.tool("compiler")
    monkeypatch.setenv("ZKC_CTEST_COMPILER", "")
    with pytest.raises(compiler_tools.Missing, match="empty"):
        compiler_tools.tool("compiler")


def test_formal_and_python_reports_share_one_root(monkeypatch, tmp_path):
    formal = load("formal_evidence", "formal/support/evidence.py")
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports with spaces"))
    assert formal.records("library") == records_root().parent / "formal/library"
    domain = load("domain_reference", "formal/checks/check_domain_reference.py")
    assert domain.REPORTS == records_root().parent / "formal/domain-reference"


@pytest.mark.parametrize("profile,relative", [("release", "build/compiler"),
                                               ("dev", "build/compiler-dev"),
                                               ("sanitize", "build/compiler-sanitize"),
                                               ("shared", "build/compiler-shared")])
def test_profile_directory_agrees_with_cmake_presets(profile, relative):
    assert workspace.compiler_directory(profile) == ROOT / relative


def test_every_tool_resolver_defaults_to_the_same_build_directories():
    """Rust tests resolve tools without running Python, so they keep their own
    copy of the defaults; the compiler's is the release preset's directory."""
    source = (ROOT / "crates/zkc-test-support/src/lib.rs").read_text()
    rust = set(re.findall(r'Build::\w+ => \("(ZKC_\w+)", "([^"]+)"\)', source))
    assert rust == set(workspace.DIRECTORIES.values())
    assert ROOT / workspace.DIRECTORIES["compiler"][1] == workspace.compiler_directory("release")


def test_hidden_or_unknown_profile_is_not_a_build_target():
    for profile in ["base", "missing", "dev; touch unexpected"]:
        with pytest.raises(ValueError, match="profile"):
            workspace.compiler_directory(profile)


def test_just_forwards_profile_and_native_environment_without_reinterpreting(monkeypatch, tmp_path, native_config):
    for name in ["cmake", "ctest"]:
        fake_command(tmp_path, name)
    record = tmp_path / "commands.jsonl"
    monkeypatch.setenv("COMMAND_RECORD", str(record))
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv("CMAKE_BUILD_PARALLEL_LEVEL", "3")
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    subprocess.run(["just", "--justfile", str(ROOT / "justfile"), "test-compiler", "dev"],
                   cwd=tmp_path, check=True, capture_output=True, text=True)
    commands = [json.loads(line) for line in record.read_text().splitlines()]
    reports = list((tmp_path / "reports/runs").glob("compiler-*"))
    assert len(reports) == 1
    assert [(c["command"], c["arguments"]) for c in commands] == [
        ("cmake", ["--preset", "dev",
                   f"-DCMAKE_C_COMPILER={native_config['CC']}",
                   f"-DCMAKE_CXX_COMPILER={native_config['CXX']}",
                   f"-DMLIR_DIR={native_config['MLIR_DIR']}",
                   f"-DCMAKE_MAKE_PROGRAM={native_config['NINJA']}"]),
        ("cmake", ["--build", "--preset", "dev"]),
        ("ctest", ["--preset", "dev", "--output-junit", str(reports[0] / "ctest.xml")]),
    ]
    assert all(c["cwd"] == str(ROOT / "compiler") and c["jobs"] == "3" for c in commands)


def test_cross_driver_preserves_report_path_as_one_argument(monkeypatch, tmp_path):
    fake_command(tmp_path, "uv")
    record = tmp_path / "commands.jsonl"
    monkeypatch.setenv("COMMAND_RECORD", str(record))
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "report space"))
    monkeypatch.setenv("PYTEST_XDIST_AUTO_NUM_WORKERS", "2")
    subprocess.run([sys.executable, str(ROOT / "tests/run.py"), "cross"],
                   cwd=tmp_path, check=True, capture_output=True, text=True)
    command = json.loads(record.read_text())
    reports = list((tmp_path / "report space/runs").glob("cross-*"))
    assert len(reports) == 1
    assert command["arguments"][-3:] == ["-n", "2", f"--junit-xml={reports[0] / 'tests.xml'}"]
    assert json.loads((reports[0] / "run.json").read_text())["status"] == "pass"
    assert command["cwd"] == str(ROOT)


@pytest.mark.parametrize("recipe,arguments", [
    ("test-artifact", ["tests/run.py", "artifact", "--output"]),
    ("bench", ["scripts/develop.py", "bench", "--output"]),
    ("test-install", ["scripts/develop.py", "install", "--output"]),
])
def test_just_output_argument_is_forwarded_literally(recipe, arguments, monkeypatch, tmp_path):
    fake_command(tmp_path, "python3")
    record = tmp_path / "commands.jsonl"
    monkeypatch.setenv("COMMAND_RECORD", str(record))
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ['PATH']}")
    output = str(tmp_path / "reports with spaces; $(invalid)")
    subprocess.run(["just", "--justfile", str(ROOT / "justfile"), "--no-deps", recipe, output],
                   cwd=tmp_path, check=True, capture_output=True, text=True)
    command = json.loads(record.read_text())
    expected = arguments + [output] + (["--profile", "release"] if recipe == "test-install" else [])
    assert command["arguments"] == expected


def test_cleanup_refuses_the_checkout(monkeypatch, tmp_path):
    developer = load("developer", "scripts/develop.py")
    checkout = tmp_path / "disposable-checkout"
    checkout.mkdir()
    marker = checkout / "source.txt"
    marker.write_text("keep")
    monkeypatch.setattr(workspace, "ROOT", checkout)
    monkeypatch.setattr(developer, "ROOT", checkout)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(checkout))
    monkeypatch.setattr(sys, "argv", ["develop.py", "clean-reports"])
    with pytest.raises(ValueError, match="refusing"):
        developer.main()
    assert marker.read_text() == "keep"


def test_lean_reproduction_receives_the_selected_report_directory(monkeypatch, tmp_path):
    developer = load("developer", "scripts/develop.py")
    calls = []
    def run(args, **kwargs):
        calls.append(list(map(str, args)))
        target = Path(args[-1])
        assert not target.exists(), "reproduction requires a fresh, absent target"
        target.mkdir(parents=True)
        (target / "evidence").write_text(str(len(calls)))
    monkeypatch.setattr(developer, "run", run)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setattr(sys, "argv", ["develop.py", "lean-fresh"])
    for _ in range(2):
        developer.main()
    outputs = [Path(call[-1]) for call in calls]
    assert outputs[0] != outputs[1]
    assert all(output.is_relative_to(tmp_path / "reports/runs") for output in outputs)
    assert [output.joinpath("evidence").read_text() for output in outputs] == ["1", "2"]
    assert all(call[:-1] == [sys.executable, str(ROOT / "formal/reproduce.py"),
                            "--with-arklib", "--output"] for call in calls)


@pytest.mark.parametrize("exists", [False, True])
def test_explicit_missing_or_nonexecutable_lean_snapshot_fails_before_testing(tmp_path, exists):
    baseline = tmp_path / "snapshot"
    if exists:
        baseline.write_text("not executable")
    result = subprocess.run([sys.executable, str(ROOT / "formal/checks/FrontendIdentity.py"),
                             "--baseline", str(baseline)], capture_output=True, text=True, timeout=10)
    assert result.returncode == 2
    assert "explicit baseline is not an executable file" in result.stderr


def test_doctor_accepts_gnu_time_without_a_packaged_version(monkeypatch):
    doctor = load("doctor", "scripts/doctor.py")
    monkeypatch.setattr(doctor.shutil, "which", lambda name: "/usr/bin/time")
    monkeypatch.setattr(doctor, "run_process", lambda *args, **kwargs:
                        subprocess.CompletedProcess(args[0], 0, "time (GNU Time) UNKNOWN\n", ""))
    assert doctor.inspect("gnu-time", ["time", "--version"])["status"] == "pass"
    assert doctor.inspect("rust", ["rustc", "--version"], "1.98.0")["status"] == "fail"


def test_cleanup_refuses_symlink_before_resolving_reports(monkeypatch, tmp_path):
    target = tmp_path / "retained"
    target.mkdir()
    marker = target / "evidence.json"
    marker.write_text("retained")
    alias = tmp_path / "reports"
    alias.symlink_to(target, target_is_directory=True)
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(alias))
    result = subprocess.run([sys.executable, str(ROOT / "scripts/develop.py"), "clean-reports"],
                            capture_output=True, text=True)
    assert result.returncode > 0 and "symlink" in result.stderr
    assert marker.read_text() == "retained"
