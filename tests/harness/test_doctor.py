"""Doctor and configure describe the explicitly selected CMake toolchain."""

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from harness import load
import workspace

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("description,status", [
    ("rustc 1.98.1 (abc 2026-09-01)", "pass"),
    ("rustc 1.99.0 (abc 2026-10-01)", "pass"),
    ("rustc 1.99.0-nightly (abc 2026-09-01)", "fail"),
    ("rustc 1.99.0-beta.1 (abc 2026-09-01)", "fail"),
])
def test_rust_stable_accepts_new_releases_but_not_prereleases(description, status, monkeypatch):
    doctor = load("doctor", "scripts/doctor.py")
    monkeypatch.setattr(doctor.shutil, "which", lambda name: "/tools/rustc")
    monkeypatch.setattr(doctor, "run_process", lambda *args, **kwargs:
                        subprocess.CompletedProcess(args, 0, description, ""))
    record = doctor.rust_version("stable")
    assert record["status"] == status
    assert record["channel"] == "stable"
    assert record["expected"] is None


@pytest.mark.parametrize("variable", ["CC", "CXX", "MLIR_DIR"])
@pytest.mark.parametrize("value", [None, "", "  "])
def test_configure_and_doctor_refuse_missing_selection(variable, value, monkeypatch, tmp_path, native_config):
    if value is None:
        monkeypatch.delenv(variable)
    else:
        monkeypatch.setenv(variable, value)
    for arguments in (["scripts/develop.py", "configure"], ["scripts/doctor.py", "--json"]):
        result = subprocess.run([sys.executable, str(ROOT / arguments[0]), *arguments[1:]],
                                capture_output=True, text=True, timeout=10)
        assert result.returncode > 0
        assert "requires explicit" in result.stderr and variable in result.stderr
        assert "+ cmake" not in result.stdout


@pytest.mark.parametrize("variable", ["CC", "CXX", "MLIR_DIR"])
def test_invalid_native_selection_is_not_replaced_by_defaults(variable, monkeypatch, tmp_path, native_config):
    monkeypatch.setenv(variable, str(tmp_path / "absent"))
    with pytest.raises(ValueError, match=variable):
        workspace.native_configuration()


@pytest.mark.parametrize("version,status,note", [
    ("23.1.2", "pass", False), ("23.1.0", "pass", True), ("22.1.2", "fail", False),
])
def test_package_version_distinguishes_required_major_from_tested_patch(version, status, note, tmp_path):
    doctor = load("doctor", "scripts/doctor.py")
    (tmp_path / "MLIRConfigVersion.cmake").write_text(f'set(PACKAGE_VERSION "{version}")\n')
    record = doctor.package_version("MLIR", tmp_path, "23.1.2")
    assert record["version"] == version and record["status"] == status
    assert ("note" in record) == note


def test_unreadable_package_version_fails(tmp_path):
    doctor = load("doctor", "scripts/doctor.py")
    assert doctor.package_version("MLIR", tmp_path, "23.1.2")["status"] == "fail"


@pytest.mark.parametrize("version,status", [("23.1.0", "pass"), ("22.1.0", "fail")])
def test_standalone_mlir_version_comes_from_selected_config(version, status, tmp_path):
    doctor = load("doctor", "scripts/doctor.py")
    (tmp_path / "MLIRConfigVersion.cmake").write_text('set(PACKAGE_VERSION "")\n')
    config = tmp_path / "MLIRConfig.cmake"
    config.write_text(f'set(LLVM_VERSION {version})\n'
                      'find_package(LLVM ${LLVM_VERSION} EXACT REQUIRED CONFIG)\n')
    record = doctor.package_version("MLIR", tmp_path, "23.1.0")
    assert record["version"] == version and record["status"] == status
    assert record["path"] == str(config)


@pytest.mark.parametrize("required", ["23.1.0", "23.1.2"])
def test_mlir_version_metadata_must_agree(required, tmp_path):
    doctor = load("doctor", "scripts/doctor.py")
    (tmp_path / "MLIRConfigVersion.cmake").write_text('set(PACKAGE_VERSION "23.1.0")\n')
    (tmp_path / "MLIRConfig.cmake").write_text(f'set(LLVM_VERSION "{required}")\n')
    record = doctor.package_version("MLIR", tmp_path, "23.1.0")
    assert record["status"] == ("pass" if required == "23.1.0" else "fail")


def test_empty_mlir_version_does_not_use_unrelated_or_commented_metadata(tmp_path):
    doctor = load("doctor", "scripts/doctor.py")
    (tmp_path / "MLIRConfigVersion.cmake").write_text('set(PACKAGE_VERSION "")\n')
    (tmp_path / "MLIRConfig.cmake").write_text('# set(LLVM_VERSION "23.1.0")\n')
    (tmp_path / "LLVMConfigVersion.cmake").write_text('set(PACKAGE_VERSION "23.1.0")\n')
    assert doctor.package_version("MLIR", tmp_path, "23.1.0")["status"] == "fail"


@pytest.mark.parametrize("state", ["matching", "stale-cache", "stale-generated", "stale-ninja"])
def test_doctor_reports_c_and_cxx_and_detects_stale_cache(state, monkeypatch, tmp_path, native_config, capsys):
    doctor = load("doctor", "scripts/doctor.py")
    checkout = tmp_path / "checkout"
    (checkout / "compiler").mkdir(parents=True)
    (checkout / "formal").mkdir()
    (checkout / "compiler/CMakeLists.txt").write_text('set(ZKC_TESTED_LLVM_VERSION "23.1.2")\n')
    (checkout / "rust-toolchain.toml").write_text('[toolchain]\nchannel = "1.98.0"\n')
    (checkout / "formal/lean-toolchain").write_text("leanprover/lean4:v4.30.0\n")
    build = tmp_path / "build"
    build.mkdir()
    stale = state != "matching"
    cached_cc = "/old/compiler" if state == "stale-cache" else native_config["CC"]
    cached_ninja = "/old/ninja" if state == "stale-ninja" else native_config["NINJA"]
    (build / "CMakeCache.txt").write_text(
        f"CMAKE_C_COMPILER:FILEPATH={cached_cc}\n"
        f"CMAKE_CXX_COMPILER:FILEPATH={native_config['CXX']}\n"
        f"CMAKE_MAKE_PROGRAM:FILEPATH={cached_ninja}\n"
        f"MLIR_DIR:PATH={native_config['MLIR_DIR']}\n"
        "CMAKE_CACHE_MAJOR_VERSION:INTERNAL=3\n"
        "CMAKE_CACHE_MINOR_VERSION:INTERNAL=30\n"
        "CMAKE_CACHE_PATCH_VERSION:INTERNAL=2\n")
    if state == "stale-generated":
        generated = build / "CMakeFiles/3.30.2/CMakeCCompiler.cmake"
        generated.parent.mkdir(parents=True)
        cached_cc = "/old/compiler"
        generated.write_text(f'set(CMAKE_C_COMPILER "{cached_cc}")\n')
    monkeypatch.setattr(doctor, "ROOT", checkout)
    monkeypatch.setattr(doctor, "compiler_directory", lambda _: build)
    commands = []

    def inspect(name, command, expected=None, directory=None):
        commands.append((name, command))
        # GCC's version need not match the LLVM library's version.
        return {"tool": name, "path": command[0], "version": "12.2.0", "status": "pass"}

    monkeypatch.setattr(doctor, "inspect", inspect)
    monkeypatch.setattr(doctor, "python_environment", lambda: {"tool": "python-env", "status": "pass"})
    monkeypatch.setattr(sys, "argv", ["doctor.py", "--json"])
    assert doctor.main() == stale
    report = json.loads(capsys.readouterr().out)
    assert ("cc", [native_config["CC"], "--version"]) in commands
    assert ("cxx", [native_config["CXX"], "--version"]) in commands
    assert report["workspace"]["cached_cmake"]["CMAKE_C_COMPILER"] == cached_cc
    assert report["workspace"]["selected_cmake"]["CMAKE_C_COMPILER"] == os.environ["CC"]
    if stale:
        assert any("just configure" in record.get("error", "") for record in report["tools"])


def test_native_configuration_requires_ninja(monkeypatch, native_config):
    monkeypatch.setenv("PATH", "")
    with pytest.raises(ValueError, match="requires ninja on PATH"):
        workspace.native_configuration()


@pytest.mark.parametrize("description,version,noted", [
    ("Ubuntu clang version 22.1.8", "22.1.8", True),
    ("Ubuntu clang version 23.1.2", "23.1.2", False),
    ("gcc (Ubuntu 14.2.0) 14.2.0", "14.2.0", False),
])
def test_a_clang_major_other_than_mlir_is_noted(description, version, noted):
    doctor = load("doctor", "scripts/doctor.py")
    records = [{"tool": "mlir", "version": "23.1.2"},
               {"tool": "cxx", "version": version, "description": description}]
    doctor.note_compiler_major(records)
    assert ("note" in records[1]) == noted


@pytest.mark.parametrize("state", ["absent", "current", "behind"])
def test_python_environment_is_checked_against_the_lock(state, monkeypatch, tmp_path):
    doctor = load("doctor", "scripts/doctor.py")
    environment = tmp_path / "venv"
    if state != "absent":
        environment.mkdir()
    monkeypatch.setenv("UV_PROJECT_ENVIRONMENT", str(environment))
    calls = []

    def check(command, **_):
        calls.append(command)
        return subprocess.CompletedProcess(command, 1 if state == "behind" else 0, "", "")

    monkeypatch.setattr(doctor, "run_process", check)
    record = doctor.python_environment()
    assert record["path"] == str(environment)
    assert record["status"] == "pass"
    assert calls == ([] if state == "absent" else [["uv", "sync", "--locked", "--check", "--offline"]])
    assert ("note" in record) == (state != "current")
