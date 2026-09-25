#!/usr/bin/env python3
"""Opt-in build using a read-only, pinned external LLZK worker toolchain."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]  # compiler/adapters/llzk -> repository root


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_snapshot(repository, revision, snapshot):
    """Compare every tracked blob to git's pinned tree; never change that tree."""
    listing = subprocess.check_output(
        ["git", "-C", str(repository), "ls-tree", "-r", "-z", revision]
    )
    count = 0
    for record in listing.split(b"\0"):
        if not record:
            continue
        meta, name = record.split(b"\t", 1)
        mode, kind, expected = meta.split()
        if kind != b"blob":
            raise ValueError("unexpected git submodule in pinned source")
        path = snapshot / os.fsdecode(name)
        data = (
            os.fsencode(os.readlink(path)) if mode == b"120000" else path.read_bytes()
        )
        actual = hashlib.sha1(
            b"blob " + str(len(data)).encode() + b"\0" + data
        ).hexdigest()
        if actual != expected.decode():
            raise ValueError(f"pin mismatch: {path}")
        count += 1
    return count


def environment(study):
    llvm = study / "bootstrap/sysroot/usr/lib/llvm-20"
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = (
        f"{llvm}/lib:{study}/bootstrap/sysroot/usr/lib/x86_64-linux-gnu"
    )
    return llvm, env


def verify_package(study, llvm):
    """Check the actual exported package paths, not just a nearby Git checkout.

    This checks custody and records build inputs. It does not prove that those
    sources produced the prebuilt libraries.
    """
    package = study / "current-build"
    source = study / "sources/llzk-current"
    cache = (package / "CMakeCache.txt").read_text()
    home = re.search(r"^CMAKE_HOME_DIRECTORY:INTERNAL=(.+)$", cache, re.M)
    if not home or Path(home[1]).resolve() != source.resolve():
        raise ValueError("LLZK package source directory mismatch")
    exports = (package / "LLZKTargets.cmake").read_text()
    paths = re.findall(
        r'(?:IMPORTED_LOCATION_RELEASE|INTERFACE_INCLUDE_DIRECTORIES) "([^"]+)"',
        exports,
    )
    if not paths:
        raise ValueError("missing LLZK package exports")
    roots = [p.resolve() for p in (source, package, llvm)]
    for group in paths:
        for name in group.split(";"):
            path = Path(name)
            # The exported package also lists optional executables that this
            # adapter neither builds nor links. Linked archives and includes
            # must exist; missing optional bin targets are harmless.
            optional_tool = path.parent == package / "bin"
            if (
                not path.is_absolute()
                or (not path.exists() and not optional_tool)
                or not any(path.resolve().is_relative_to(root) for root in roots)
            ):
                raise ValueError(f"LLZK package path mismatch: {name}")
    return {
        name: sha(package / name)
        for name in ("LLZKConfig.cmake", "LLZKTargets.cmake", "CMakeCache.txt")
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--study", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    study, work = args.study.resolve(), args.work.resolve()
    if work == study or study in work.parents:
        parser.error("work must be outside the read-only worker tree")
    work.mkdir(parents=True, exist_ok=True)
    pins = json.loads((HERE / "pins.json").read_text())
    revision = pins["llzk-current"]["revision"]
    blobs = verify_snapshot(
        study / "sources/llzk-lib", revision, study / "sources/llzk-current"
    )
    llvm, env = environment(study)
    package_inputs = verify_package(study, llvm)
    command = [
        "cmake",
        "-S",
        str(REPO / "compiler/adapters/llzk"),
        "-B",
        str(work / "build"),
        "-G",
        "Ninja",
        "-DCMAKE_BUILD_TYPE=Release",
        f"-DCMAKE_C_COMPILER={llvm}/bin/clang",
        f"-DCMAKE_CXX_COMPILER={llvm}/bin/clang++",
        f"-DLLVM_DIR={llvm}/lib/cmake/llvm",
        f"-DMLIR_DIR={llvm}/lib/cmake/mlir",
        f"-DLLZK_DIR={study}/current-build",
        f"-DZKC_LLZK_REVISION={revision}",
    ]
    for cmd in [
        command,
        ["cmake", "--build", str(work / "build"), "-j", "2"],
        ["ctest", "--test-dir", str(work / "build"), "--output-on-failure"],
    ]:
        subprocess.run(cmd, env=env, check=True)
    # Static library origin and generated headers remain part of build trust.
    libraries = {
        str(p.relative_to(study)): sha(p)
        for p in sorted((study / "current-build").rglob("*.a"))
    }
    generated = {
        str(p.relative_to(study)): sha(p)
        for p in sorted((study / "current-build").rglob("*.inc"))
    }
    sources = {
        p.name: sha(p)
        for p in (REPO / "compiler/adapters/llzk").glob("*")
        if p.is_file()
    }
    record = dict(
        llzk_revision=revision,
        tracked_blobs_verified=blobs,
        package_inputs=package_inputs,
        libraries=libraries,
        generated_headers=generated,
        adapter_sources=sources,
        shared_parser_guard_sha256=sha(
            REPO / "compiler/include/zkc/Support/MLIRInput.h"
        ),
        binary_sha256=sha(work / "build/zkc-llzk"),
        llvm_library_sha256=sha(llvm / "lib/libLLVM.so.20.1"),
    )
    (work / "build-inputs.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
