#!/usr/bin/env python3
"""Report selected tool paths and reject incompatible language toolchains."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

from workspace import compiler_directory, native_configuration, output_directory, reports_root, validate_environment
from processes import Interrupted, run as run_process

ROOT = Path(__file__).resolve().parents[1]


def inspect(name, command, expected=None, directory=ROOT):
    path = shutil.which(command[0])
    record = {"tool": name, "path": path, "expected": expected, "status": "pass"}
    if path is None:
        return record | {"status": "fail", "error": "tool is not on PATH"}
    try:
        run = run_process([path, *command[1:]], cwd=directory,
                             text=True, capture_output=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired) as error:
        return record | {"status": "fail", "error": str(error)}
    text = (run.stdout or run.stderr).strip()
    match = re.search(r"\b\d+\.\d+(?:\.\d+)?\b", text)
    version = match[0] if match else None
    record.update(version=version, description=text.splitlines()[0] if text else "")
    # Some distributions build GNU time without a numeric package version.
    # Its tool identity is still explicit; pinned language versions stay strict.
    identified_time = name == "gnu-time" and text.startswith("time (GNU Time)")
    if run.returncode or (version is None and not identified_time):
        record.update(status="fail", error=text or f"exit {run.returncode}")
    elif expected and version != expected:
        record.update(status="fail", error=f"expected {expected}, found {version}")
    return record


def rust_version(channel):
    """A stable channel accepts new releases without requiring a dated override."""
    record = inspect("rust", ["rustc", "--version"],
                     None if channel == "stable" else channel)
    record["channel"] = channel
    if channel == "stable" and record["status"] == "pass":
        description = record.get("description", "")
        if not re.match(r"rustc \d+\.\d+\.\d+\s", description):
            record.update(status="fail", error="the project uses stable Rust, not a prerelease")
    return record


def package_version(name, directory, tested):
    """Read the selected CMake package, independently of an llvm-config on PATH."""
    path = Path(directory) / f"{name}ConfigVersion.cmake"
    record = {"tool": name.lower(), "path": str(path), "tested": tested, "status": "pass"}

    def literal_version(file, variable):
        source = file.read_text() if file.is_file() else ""
        match = re.search(rf'(?m)^[ \t]*set\(\s*{variable}\s+"?(\d+\.\d+\.\d+)"?\s*\)', source)
        return match[1] if match else None

    version = literal_version(path, "PACKAGE_VERSION")
    if name == "MLIR":
        # Standalone MLIR packages can leave PACKAGE_VERSION empty. Their
        # main config still records the exact LLVM version used by CMake.
        config = Path(directory) / "MLIRConfig.cmake"
        required = literal_version(config, "LLVM_VERSION")
        if version and required and version != required:
            return record | {"status": "fail", "error": "inconsistent MLIR package version metadata"}
        if not version and required:
            version = required
            record["path"] = str(config)
    if not version:
        return record | {"status": "fail", "error": "cannot read the selected CMake package version"}
    record["version"] = version
    if version.split(".")[0] != "23":
        record.update(status="fail", error="the main compiler requires LLVM/MLIR 23")
    elif version != tested:
        record["note"] = f"differs from tested {tested}; record this version with evidence"
    return record


def note_compiler_major(records):
    """Note a clang whose major release is not the selected MLIR's.

    The compiler builds against either, but the Nix shell and CI pair clang
    with the same LLVM release, so a different major is a difference between
    this build and theirs worth seeing.
    """
    mlir = next((r for r in records if r["tool"] == "mlir"), {})
    major = (mlir.get("version") or "").split(".")[0]
    for record in records:
        version = record.get("version") or ""
        if (major and record["tool"] in ("cc", "cxx") and "clang" in record.get("description", "")
                and version.split(".")[0] != major):
            record["note"] = f"clang {version} with MLIR {major}; the Nix shell and CI use clang {major}"


def python_environment():
    """Tests run under `uv run --no-sync`, which uses the environment as it is.

    Record drift from `uv.lock` without rejecting compatible newer packages.
    The lock identifies a reproducible environment, not a compatibility rule.
    """
    environment = Path(os.environ.get("UV_PROJECT_ENVIRONMENT") or ROOT / ".venv")
    record = {"tool": "python-env", "path": str(environment), "status": "pass"}
    if not environment.exists():
        return record | {"note": "no project environment yet; just setup creates it"}
    try:
        check = run_process(["uv", "sync", "--locked", "--check", "--offline"], cwd=ROOT,
                            text=True, capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as error:
        return record | {"note": f"could not compare the environment with uv.lock: {error}"}
    if check.returncode:
        return record | {"note": "the environment does not reproduce uv.lock, or its offline "
                                 "comparison is unavailable; uv sync --locked restores the "
                                 "recorded environment when reproduction is needed"}
    return record


def cached_configuration(profile):
    cache = compiler_directory(profile) / "CMakeCache.txt"
    if not cache.is_file():
        return {}
    entries = {}
    source = cache.read_text()
    for line in source.splitlines():
        match = re.match(r"(CMAKE_C_COMPILER|CMAKE_CXX_COMPILER|CMAKE_MAKE_PROGRAM|MLIR_DIR|LLVM_DIR):[^=]+=(.*)", line)
        if match:
            entries[match[1]] = match[2]
    # A command-line -DCMAKE_C_COMPILER=clang can leave an unresolved name in
    # CMakeCache even though CMake recorded an absolute executable elsewhere.
    # Use the generated compiler description belonging to this cache's version;
    # resolving an old bare name against today's PATH could report another tool.
    versions = [re.search(rf"^CMAKE_CACHE_{part}_VERSION:INTERNAL=(\d+)$", source, re.MULTILINE)
                for part in ("MAJOR", "MINOR", "PATCH")]
    if all(versions):
        version = ".".join(match[1] for match in versions)
        for language in ("C", "CXX"):
            description = cache.parent / "CMakeFiles" / version / f"CMake{language}Compiler.cmake"
            if description.is_file():
                key = f"CMAKE_{language}_COMPILER"
                match = re.search(rf'set\({key} "([^"]+)"\)', description.read_text())
                if match:
                    entries[key] = match[1]
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--profile", default="release")
    args = parser.parse_args()
    try:
        validate_environment()
        selected = native_configuration()
        cached = cached_configuration(args.profile)
    except ValueError as error:
        parser.error(str(error))
    rust = tomllib.loads((ROOT / "rust-toolchain.toml").read_text())["toolchain"]["channel"]
    lean = (ROOT / "formal/lean-toolchain").read_text().strip().split(":v")[-1]
    records = [
        inspect("cc", [selected["CMAKE_C_COMPILER"], "--version"]),
        inspect("cxx", [selected["CMAKE_CXX_COMPILER"], "--version"]),
        rust_version(rust),
        inspect("lean", ["lean", "--version"], lean, ROOT / "formal"),
        inspect("cmake", ["cmake", "--version"]),
        inspect("ninja", ["ninja", "--version"]),
        inspect("python", [sys.executable, "--version"]),
        inspect("uv", ["uv", "--version"]),
        inspect("just", ["just", "--version"]),
        inspect("gnu-time", ["time", "--version"]),
    ]
    tested = re.search(r'set\(ZKC_TESTED_LLVM_VERSION\s+"([^"]+)"',
                       (ROOT / "compiler/CMakeLists.txt").read_text())[1]
    records.insert(0, package_version("MLIR", selected["MLIR_DIR"], tested))
    records.append(python_environment())
    note_compiler_major(records)
    # This is an auxiliary tool, not evidence of the package CMake selected.
    llvm_config = os.environ.get("LLVM_CONFIG") or (
        "llvm-config" if shutil.which("llvm-config") else "llvm-config-23")
    records.append(inspect("llvm-config", [llvm_config, "--version"]))
    if cached.get("LLVM_DIR"):
        records.append(package_version("LLVM", cached["LLVM_DIR"], tested))
    for key, value in cached.items():
        if key not in selected:
            continue
        cached_path = shutil.which(value) if key.startswith("CMAKE_") else value
        if cached_path is None or Path(cached_path).absolute() != Path(selected[key]):
            records.append({"tool": "cmake-cache", "status": "fail",
                            "error": f"{key}: cache uses {value}, selected {selected[key]}; "
                                     f"run just configure {args.profile}"})
    if sys.version_info < (3, 12):
        records.append({"tool": "python-floor", "status": "fail", "error": "Python 3.12+ required"})
    if shutil.which("nix"):
        records.append(inspect("nix", ["nix", "--version"]))
    result = {"status": "pass" if all(r["status"] == "pass" for r in records) else "fail",
              "tools": records,
              "workspace": {"profile": args.profile, "selected_cmake": selected,
                            "cached_cmake": cached, "outputs": {kind: str(output_directory(kind))
                                         for kind in ("compiler", "native", "lean")},
                            "reports": str(reports_root())}}
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        for record in records:
            print(f"{record['tool']:<9} {record.get('version') or '?':<12} "
                  f"{record.get('path') or '-'}")
            if record.get("error"):
                print(f"  {record['error']}")
            if record.get("note"):
                print(f"  {record['note']}")
        for key, value in selected.items():
            print(f"selected {key}: {value}")
        for key, value in cached.items():
            print(f"cached {key}: {value}")
        for kind, directory in result["workspace"]["outputs"].items():
            print(f"{kind + ' output':<16} {directory}")
        print(f"{'reports':<16} {result['workspace']['reports']}")
    return result["status"] != "pass"


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Interrupted as error:
        sys.exit(128 + error.signum)
