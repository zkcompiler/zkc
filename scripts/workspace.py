"""Local workspace paths shared by development commands and Python tests.

Tool versions belong to Nix and language manifests. This module only resolves
mutable checkout paths and rejects obsolete, ambiguous environment settings.
All ZKC path settings are relative to the checkout, not the caller's directory.
"""

import json
import os
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REMOVED = {
    "ZKC_JOBS": "use the build tool's parallelism variable (see docs/development/README.md)",
    "ZKC_BUILD_PRESET": "pass a profile argument, e.g. just build-compiler dev",
    "ZKC_COMPILER_BUILD": "use a CMake preset; select its output with ZKC_COMPILER_BIN",
    "ZKC_COMPILER": "set ZKC_COMPILER_BIN to the directory containing zkc-compile",
    "ZKC_SOURCE_BENCH": "set ZKC_COMPILER_BIN to the compiler output directory",
    "ZKC_SERVICE_COMPILER": "set ZKC_COMPILER_BIN to the compiler output directory",
    "ZKC_SERVICE_OPTIMIZER": "set ZKC_COMPILER_BIN to the compiler output directory",
    "ZKC_REQUIREMENTS_TEST": "set ZKC_COMPILER_BIN to the compiler output directory",
    "ZKC_OPTIMIZER": "set ZKC_COMPILER_BIN to the directory containing zkc-opt",
    "ZKC_LEAN": "set ZKC_LEAN_BIN to the directory containing the Lean checkers",
    "ZKC_PHYSICAL_CHECKER": "set ZKC_LEAN_BIN to the directory containing the Lean checkers",
    "ZKC_TEST_RECORDS": "set ZKC_REPORTS_DIR to the reports root (without /tests)",
}
DIRECTORIES = {
    "compiler": ("ZKC_COMPILER_BIN", "build/compiler"),
    "native": ("ZKC_NATIVE_BIN", "target/release"),
    "lean": ("ZKC_LEAN_BIN", "formal/.lake/build/bin"),
}


def validate_environment():
    for name, replacement in REMOVED.items():
        if name in os.environ:
            raise ValueError(f"{name} was removed; {replacement}")
    for name in [entry[0] for entry in DIRECTORIES.values()] + ["ZKC_REPORTS_DIR"]:
        if name in os.environ and not os.environ[name].strip():
            raise ValueError(f"{name} must be a nonempty path; unset it to use the default")


def checkout_path(value):
    path = Path(value)
    return (path if path.is_absolute() else ROOT / path).resolve()


def output_directory(kind):
    validate_environment()
    variable, fallback = DIRECTORIES[kind]
    if variable in os.environ:
        return checkout_path(os.environ[variable])
    if kind == "native" and os.environ.get("CARGO_TARGET_DIR"):
        # Cargo interprets this native setting relative to the invoking cwd.
        return Path(os.environ["CARGO_TARGET_DIR"]).resolve() / "release"
    return ROOT / fallback


def reports_root():
    validate_environment()
    return checkout_path(os.environ.get("ZKC_REPORTS_DIR", "build/reports"))


def compiler_directory(profile):
    """Read this repository's preset rather than maintaining another path map.

Only the macros used by the checked-in presets are supported here. Refuse an
unknown macro instead of silently sending integration tests to another build.
"""
    presets = json.loads((ROOT / "compiler/CMakePresets.json").read_text())
    entries = {entry["name"]: entry for entry in presets["configurePresets"]}
    if profile not in entries or entries[profile].get("hidden"):
        raise ValueError(f"unknown public CMake profile: {profile}")

    def directory(name, seen):
        if name in seen:
            raise ValueError("cyclic CMake preset inheritance")
        entry = entries[name]
        if "binaryDir" in entry:
            return entry["binaryDir"]
        parents = entry.get("inherits", [])
        if isinstance(parents, str):
            parents = [parents]
        for parent in parents:
            result = directory(parent, seen | {name})
            if result:
                return result
        return None

    value = directory(profile, set())
    if not value:
        raise ValueError(f"CMake profile {profile} has no binaryDir")
    value = value.replace("${sourceDir}", str(ROOT / "compiler"))
    value = value.replace("${presetName}", profile)
    if "$" in value:
        raise ValueError(f"unsupported binaryDir macro in CMake profile {profile}: {value}")
    return Path(value).resolve()


def native_configuration():
    """Explicit native selections, also supplied by the Nix development shell.

    CC/CXX name executable files (wrappers are fine); build flags belong in
    CFLAGS/CXXFLAGS. Pass these to CMake even with an existing cache, so changing
    the environment cannot leave a silently selected old compiler in use.
    """
    missing = [name for name in ("CC", "CXX", "MLIR_DIR") if not os.environ.get(name, "").strip()]
    if missing:
        raise ValueError("native configuration requires explicit " + ", ".join(missing)
                         + "; set CC, CXX and MLIR_DIR or enter nix develop")
    selected = {}
    for variable, cache in (("CC", "CMAKE_C_COMPILER"), ("CXX", "CMAKE_CXX_COMPILER")):
        path = shutil.which(os.environ[variable])
        if path is None:
            raise ValueError(f"{variable} must name an executable file: {os.environ[variable]}")
        selected[cache] = str(Path(path).absolute())
    mlir = Path(os.environ["MLIR_DIR"]).resolve()
    if not (mlir / "MLIRConfig.cmake").is_file():
        raise ValueError(f"MLIR_DIR does not contain MLIRConfig.cmake: {mlir}")
    selected["MLIR_DIR"] = str(mlir)
    # Every public preset uses Ninja. CMake otherwise retains a cached older
    # executable even when today's PATH selects a different installation.
    ninja = shutil.which("ninja")
    if ninja is None:
        raise ValueError("native configuration requires ninja on PATH")
    selected["CMAKE_MAKE_PROGRAM"] = str(Path(ninja).absolute())
    return selected


def clear_report_directory(path):
    """Clear generated reports, refusing checkout sources and home/ancestor paths."""
    supplied = Path(path).absolute()
    if supplied.is_symlink():
        raise ValueError(f"refusing to remove report directory symlink {supplied}")
    path = supplied.resolve()
    home = Path.home().resolve()
    if (path == home or path in home.parents or path == ROOT or path in ROOT.parents
            or path == ROOT / "build"
            or (path.is_relative_to(ROOT) and not path.is_relative_to(ROOT / "build"))):
        raise ValueError(f"refusing to remove non-report directory {path}")
    if path.exists():
        shutil.rmtree(path)
