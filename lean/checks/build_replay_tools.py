#!/usr/bin/env python3
"""Build a local, explicitly labeled Lean 4.35 replay runtime from pinned sources.

No fetch, Lake build, installed-tool mutation, or project compilation occurs.
The recipe follows Lean's pinned CMake/lean4lean-minimal-init link adaptation;
see replay_tools/README.md for upstream attribution and input preparation.
"""

import argparse
import os
from pathlib import Path
import shutil
import sys

import check_independent as audit


def inventory(prefix):
    """Exact installed compiler, headers, oleans, archives, and linker inputs.

    Only in-prefix symlinks are allowed for installed inputs. Local outputs are
    always regular copies, never hardlinks or writable aliases of these inputs.
    """
    result = {}
    for directory in ["bin", "lib", "include"]:
        for file in sorted((prefix / directory).rglob("*")):
            if file.is_symlink() and not file.resolve().is_relative_to(prefix):
                raise audit.CheckError(f"installed input symlink escapes toolchain: {file}")
            if file.is_file():
                result[str(file.relative_to(prefix))] = audit.identity(file)
    return result


def copy_checked(source, target, expected):
    before = audit.identity(source)
    if before[0]["sha256"] != expected:
        raise audit.CheckError(f"pinned input hash mismatch: {source}")
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    if audit.identity(source) != before or audit.digest(target) != expected:
        raise audit.CheckError(f"input changed while copying: {source}")


def build(args, output, runner):
    pins = audit.read_json(audit.REPLAY_SOURCES)
    build_environment = runner.environment
    runner.environment = audit.checking_environment()
    prefix, _ = audit.tools_for(output, args.lake, runner, paranoid=True)
    runner.environment = build_environment
    revision = runner.run([str(prefix / "bin/lean"), "--githash"], output, "lean-revision").strip()
    if revision != pins["repositories"]["lean"]["revision"]:
        raise audit.CheckError("installed Lean revision differs from pinned build recipe")
    installed = inventory(prefix)
    sources = {"lean": prefix / "src/lean", "lean4lean": args.lean4lean_source.resolve(),
               "batteries": args.batteries_source.resolve(), "lean4export": args.export_source.resolve()}
    for name, expected in pins["sources"].items():
        repository, relative = name.split("/", 1)
        copy_checked(sources[repository] / relative, output / "sources" / name, expected)
    for i, patch in enumerate(pins["patches"]):
        target = patch["target"]
        repository, _ = target.split("/", 1)
        local_patch = output / "patches" / patch["file"]
        copy_checked(audit.REPLAY_SOURCES.parent / "patches" / patch["file"], local_patch, patch["sha256"])
        runner.run(["patch", "--batch", "--fuzz=0", "-p2" if repository == "lean" else "-p1",
                    "-i", str(local_patch)], output / "sources" / repository, f"patch-{i}")
        if audit.digest(output / "sources" / target) != patch["patched_sha256"]:
            raise audit.CheckError(f"patched source hash mismatch: {target}")
    inputs = {"toolchain": {k: v[0] for k, v in installed.items()},
              "sources": {k: audit.digest(output / "sources" / k) for k in pins["sources"]},
              "patches": pins["patches"]}
    receipt = {"format": audit.TOOLSET_FORMAT, "label": "patched Lean 4.35.0 replay",
               "recipe_sha256": audit.digest(audit.REPLAY_SOURCES),
               "builder_sha256": audit.digest(Path(__file__)), "inputs": inputs,
               "commands": [], "runtime": {}, "reuse": None}
    sysroot = output / "sysroot"
    (sysroot / "bin").mkdir(parents=True)
    if args.reuse:
        previous, previous_root, stamps = audit.replay_toolset(args.reuse, prefix)
        if previous["inputs"] != inputs:
            raise audit.CheckError("cannot reuse replay tools: sources/options/toolchain differ")
        for name in audit.PATCHED_CHECKERS:
            copy_checked(previous_root / "bin" / name, sysroot / "bin" / name,
                         previous["runtime"]["bin/" + name]["sha256"])
        if any(audit.identity(Path(p)) != expected for p, expected in stamps.items()):
            raise audit.CheckError("reused replay toolset changed")
        receipt["reuse"] = {"manifest": str(args.reuse.absolute()), "sha256": audit.digest(args.reuse),
                            "commands": previous["commands"]}
    else:
        recipe = pins["recipe"]
        # Lean chooses a search root for a namespace, rather than falling back
        # per missing submodule. Mirror installed inputs read-only; omit every
        # sidecar of our two outputs so compilation cannot follow a write alias.
        native = output / "build/native"
        native.mkdir(parents=True)
        for file in (prefix / "lib/lean").rglob("*"):
            relative = file.relative_to(prefix / "lib/lean")
            target = native / relative
            if file.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            elif not str(relative).startswith(("Lean/Replay.", "LeanChecker.")):
                target.symlink_to(file)

        def compile_module(name, directory):
            repository, relative = name.split("/", 1)
            source_root = output / "sources" / repository
            stem = output / "build" / directory / Path(relative).with_suffix("")
            stem.parent.mkdir(parents=True, exist_ok=True)
            runner.run([str(prefix / "bin/lean"), *recipe["lean"], "-R", str(source_root),
                        "-o", str(stem.with_suffix(".olean")), "-c", str(stem.with_suffix(".c")),
                        str(source_root / relative)], output, f"compile-{len(runner.commands)}",
                       env={"LEAN_PATH": str(output / "build" / directory)})
            runner.run([str(prefix / "bin/leanc"), *recipe["compile"], "-c", str(stem.with_suffix(".c")),
                        "-o", str(stem.with_suffix(".o"))], output, f"object-{len(runner.commands)}")
            return stem.with_suffix(".o")

        replay, checker = [compile_module(n, "native") for n in pins["modules"]["native"]]
        for name in audit.PATCHED_CHECKERS[:2]:
            runner.run([str(prefix / "bin/leanc"), "-o", str(sysroot / "bin" / name),
                        str(checker), str(replay), *recipe["link"][name]], output, f"link-{name}")
        objects = [compile_module(n, "lean4lean") for n in pins["modules"]["lean4lean"]]
        main = output / "build/lean4lean/Main.o"
        runner.run([str(prefix / "bin/leanc"), "-o", str(sysroot / "bin/lean4lean"),
                    str(main), *map(str, sorted(o for o in objects if o != main)),
                    *recipe["link"]["lean4lean"]], output, "link-lean4lean")
    for relative in audit.RUNTIME_FILES:
        target = sysroot / relative
        if relative not in {f"bin/{n}" for n in audit.PATCHED_CHECKERS}:
            copy_checked(prefix / relative, target, installed[relative][0]["sha256"])
        target.chmod(0o555 if relative.startswith("bin/") else 0o444)
        receipt["runtime"][relative] = audit.identity(target)[0]
    if inventory(prefix) != installed:
        raise audit.CheckError("installed toolchain changed during replay build")
    for name, expected in inputs["sources"].items():
        if audit.digest(output / "sources" / name) != expected:
            raise audit.CheckError(f"local build source changed: {name}")
    receipt["commands"] = runner.commands
    audit.write_json(output / "manifest.json", receipt)
    audit.replay_toolset(output / "manifest.json", prefix)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="stock Lean 4.35.0 Lake launcher")
    parser.add_argument("--lean4lean-source", required=True, type=Path)
    parser.add_argument("--batteries-source", required=True, type=Path)
    parser.add_argument("--export-source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path, help="new local directory")
    parser.add_argument("--reuse", type=Path, help="prior build manifest; reuse only with identical inputs/options")
    parser.add_argument("--memory-mb", type=audit.positive, default=65536)
    parser.add_argument("--timeout", type=audit.positive, default=120, help="seconds per compiler/linker")
    args = parser.parse_args(argv)
    output = args.output.resolve()
    runner = None
    created = False
    try:
        audit.checking_environment()
        output.mkdir(parents=True, exist_ok=False)
        created = True
        (output / "home").mkdir()
        # No inherited compiler/linker/path configuration. The absolute pinned
        # compiler uses its own bundled clang and static archives.
        runner = audit.Runner(output, memory_mb=args.memory_mb, timeout=args.timeout,
                             environment={"PATH": os.defpath, "HOME": str(output / "home"), "LANG": "C.UTF-8"})
        build(args, output, runner)
        print(f"Built explicit patched replay tools: {output / 'manifest.json'}")
    except (OSError, ValueError) as error:
        if created:
            audit.write_json(output / "failure.json", {"status": "failed", "error": str(error),
                                                      "commands": runner.commands if runner else []})
        print(f"replay tool build failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
