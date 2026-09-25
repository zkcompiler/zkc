"""Harness controls isolate configuration from the build outputs under test."""

import os

import pytest
import workspace


@pytest.fixture(autouse=True)
def clean_environment(monkeypatch):
    for name in list(workspace.REMOVED) + [
        "ZKC_COMPILER_BIN", "ZKC_NATIVE_BIN", "ZKC_LEAN_BIN", "ZKC_REPORTS_DIR",
        "CARGO_TARGET_DIR", "PYTEST_XDIST_AUTO_NUM_WORKERS",
        "CC", "CXX", "MLIR_DIR", "LLVM_CONFIG",
    ]:
        monkeypatch.delenv(name, raising=False)


@pytest.fixture
def native_config(monkeypatch, tmp_path):
    from harness import executable

    selected = {}
    for name in ("CC", "CXX"):
        path = executable(tmp_path / "toolchain" / name.lower())
        monkeypatch.setenv(name, str(path))
        selected[name] = str(path)
    mlir = tmp_path / "toolchain/mlir"
    mlir.mkdir()
    (mlir / "MLIRConfig.cmake").write_text("# controlled package\n")
    (mlir / "MLIRConfigVersion.cmake").write_text('set(PACKAGE_VERSION "23.1.2")\n')
    monkeypatch.setenv("MLIR_DIR", str(mlir))
    selected["MLIR_DIR"] = str(mlir)
    ninja = executable(tmp_path / "toolchain/ninja")
    monkeypatch.setenv("PATH", str(ninja.parent) + os.pathsep + os.environ["PATH"])
    selected["NINJA"] = str(ninja)
    return selected
