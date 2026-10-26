#!/usr/bin/env python3
"""Capture locked declarations, compare fixed models, or replay current proofs.

This driver never builds. Capture reads existing oleans and makes no freshness
claim. Compare uses Lake's export-only paths, retaining its sandbox and every
bundled paranoid checker. See ../docs/development/independent-checking.md.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import selectors
import signal
import shutil
import stat
import subprocess
import sys
import time


LEAN = Path(__file__).resolve().parents[1]
PACKAGES = {"main": "", "security": "security", "arklib": "integrations/arklib",
            "clean": "integrations/clean"}
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
# Lean 4.35 Lake/CLI/Check.lean: primitiveTargets and builtinTargets.
# Explicit exports bypass Lake's exporter, so the caller must include these.
PRIMITIVES = """Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq
Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList
Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam
semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind""".split()
CHECKERS = ["leanchecker", "leanchecker-paranoid", "lean4lean", "nanoda_bin",
            "con-leche", "con-ron"]
CAPTURE_FORMAT = "zkc.independent-exports/0"
REPORT_FORMAT = "zkc.independent-comparison/0"
REPLAY_FORMAT = "zkc.independent-replay/0"
TOOLSET_FORMAT = "zkc.replay-toolset/0"
REPLAY_SOURCES = LEAN / "checks/replay_tools/manifest.json"
PATCHED_CHECKERS = CHECKERS[:3]
RUNTIME_FILES = ([f"bin/{n}" for n in ["lake", "lean", "leanexport", *CHECKERS]] +
                 [f"lib/lean/{n}.so" for n in ["libLake_shared", "libInit_shared",
                                               "libleanshared", "libleanshared_1", "libleanshared_2"]])


class CheckError(ValueError):
    """An incomplete or rejected check, never an acceptance."""


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def file_metadata(path):
    s = path.lstat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_mode)


def identity(path):
    """Notice replacement and in-place writes, including bytes restored mid-check."""
    before = path.stat()
    result = {"sha256": digest(path), "bytes": before.st_size}
    def stamp(s):
        return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_mode)
    if stamp(before) != stamp(path.stat()):
        raise CheckError(f"file changed while hashing: {path}")
    return result, stamp(before)


def regular_file(root, relative):
    """Local toolsets have no symlinks, special files, or paths outside their root."""
    path = Path(relative)
    if path.is_absolute() or not path.parts or any(p in {".", ".."} for p in path.parts):
        raise CheckError(f"invalid toolset path: {relative}")
    current = root
    for part in path.parts:
        current = current / part
        if current.is_symlink():
            raise CheckError(f"symlink in toolset: {current}")
    if not stat.S_ISREG(current.stat().st_mode):
        raise CheckError(f"not a regular toolset file: {current}")
    return current


def checking_environment():
    # Lake tests presence, even for an empty value. Installation and dynamic
    # loader overrides must not redirect the tools whose hashes we record.
    forbidden = {"LAKE_CHECK_EXPORT", "LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN", "LEAN", "LAKE_HOME",
                 "LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT"}
    for name in sorted(forbidden & os.environ.keys()):
        raise CheckError(f"unset {name} before independent checking")
    return {k: v for k, v in os.environ.items()
            if k in {"PATH", "HOME", "ELAN_HOME", "ELAN_TOOLCHAIN", "COMPARATOR_BWRAP", "TMPDIR"}}


def guard_files(runner, files):
    if not isinstance(runner, Runner):
        return
    snapshots = {path: identity(path) for path in files}

    def unchanged():
        for path, expected in snapshots.items():
            if identity(path) != expected:
                raise CheckError(f"input changed during checking: {path}")

    runner.guards.append(unchanged)
    unchanged()


def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"duplicate JSON key {key}")
        result[key] = value
    return result


def read_json(path):
    try:
        if Path(path).stat().st_size > 16 * 1024**2:
            raise CheckError(f"{path}: metadata exceeds 16 MiB")
        return json.loads(Path(path).read_text(), object_pairs_hook=unique_json_object)
    except (OSError, ValueError) as error:
        raise CheckError(f"cannot read {path}: {error}") from error


def write_json(path, value):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def names(value, label):
    if (not isinstance(value, list) or not all(isinstance(n, str) and n and
            not any(c.isspace() for c in n) and not n.startswith("-") for n in value)
            or len(set(value)) != len(value)):
        raise CheckError(f"{label}: expected unique nonempty Lean names")
    return value


def configuration(root):
    """Require exact lock coverage and the standard axiom policy in every package."""
    lock = read_json(root / "checks/claims.lock.json")
    if not isinstance(lock, dict) or set(lock) != {"format", "theorems"} or \
            lock["format"] != "zkc.claims-lock/0" or not isinstance(lock["theorems"], dict) or not lock["theorems"]:
        raise CheckError("invalid claims lock")
    groups = {package: {"theorems": [], "modules": set()} for package in PACKAGES}
    for name, row in lock["theorems"].items():
        names([name], "lock theorem")
        if not isinstance(row, dict) or not isinstance(row.get("package"), str) or row["package"] not in PACKAGES:
            raise CheckError(f"{name}: unknown lock package")
        names([row.get("module")], f"{name} module")
        group = groups[row["package"]]
        group["theorems"].append(name)
        group["modules"].add(row["module"])
    fields = {"challenge_module", "solution_module", "theorem_names",
              "definition_names", "permitted_axioms"}
    for package, group in groups.items():
        path = root / PACKAGES[package] / "comparator.json"
        config = read_json(path)
        if not isinstance(config, dict) or set(config) != fields:
            raise CheckError(f"{path}: unexpected comparator fields")
        for field in ("challenge_module", "solution_module"):
            names([config[field]], str(path))
        expected = sorted(group["theorems"])
        if not expected or sorted(names(config["theorem_names"], str(path))) != expected:
            raise CheckError(f"{path}: theorem_names must exactly cover its locked declarations")
        if config["definition_names"] != [] or \
                sorted(names(config["permitted_axioms"], str(path))) != sorted(AXIOMS):
            raise CheckError(f"{path}: definition holes or changed permitted axioms are forbidden")
        group.update(theorems=expected, modules=sorted(group["modules"]), config=path, policy=config)
    return groups


class Runner:
    """Sequential children with process-group cancellation and bounded streams."""

    def __init__(self, output, memory_mb=8192, log_mb=8, export_mb=2048, timeout=1800, environment=None):
        self.output = output
        self.memory = memory_mb * 1024**2
        self.log_limit = log_mb * 1024**2
        self.export_limit = export_mb * 1024**2
        self.timeout = timeout
        self.commands = []
        self.environment = environment
        self.guards = []

    def run(self, command, cwd, label, export=None, env=None):
        for guard in self.guards:
            guard()
        log = self.output / f"{label}.log"
        record = {"command": [str(c) for c in command], "cwd": str(cwd), "log": log.name}
        if env:
            record["environment_overrides"] = env
        self.commands.append(record)
        started = time.monotonic()

        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (self.memory, self.memory))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

        child = None
        try:
            with log.open("xb") as logs, selectors.DefaultSelector() as selector:
                # Capture stdout as an artifact only for leanexport; all diagnostics
                # share one bounded log. No pipe is buffered with communicate().
                stream = export.open("xb") if export else None
                try:
                    child = subprocess.Popen(record["command"], cwd=cwd, stdin=subprocess.DEVNULL,
                                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                             env={**(os.environ if self.environment is None else self.environment),
                                                  **(env or {}), "LEAN_ABORT_ON_PANIC": "1"},
                                             start_new_session=True, preexec_fn=limits)
                    selector.register(child.stdout, selectors.EVENT_READ, bool(export))
                    selector.register(child.stderr, selectors.EVENT_READ, False)
                    totals = {False: 0, True: 0}
                    while selector.get_map() or child.poll() is None:
                        if time.monotonic() - started > self.timeout:
                            raise CheckError(f"{label}: timeout after {self.timeout}s")
                        for key, _ in selector.select(timeout=0.1):
                            chunk = os.read(key.fileobj.fileno(), 65536)
                            if not chunk:
                                selector.unregister(key.fileobj)
                                continue
                            target = key.data
                            totals[target] += len(chunk)
                            bound = self.export_limit if target else self.log_limit
                            if totals[target] > bound:
                                raise CheckError(f"{label}: {'export' if target else 'log'} output limit exceeded")
                            (stream if target else logs).write(chunk)
                    record["exit_code"] = child.wait()
                    if child.returncode:
                        raise CheckError(f"{label}: exited {child.returncode}; see {log}")
                finally:
                    if stream:
                        stream.close()
        except BaseException:
            if child is not None:
                # Descendants may retain pipes even after their parent exits.
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                child.wait()
            raise
        finally:
            if child is not None:
                child.stdout.close()
                child.stderr.close()
            record["seconds"] = round(time.monotonic() - started, 3)
            for guard in self.guards:
                guard()
        return log.read_text() if export is None else None

    def verify_inputs(self):
        for guard in self.guards:
            guard()


def tools_for(root, lake, runner, paranoid=False):
    # Lake tests presence, not truthiness: even an empty value selects its
    # internal export path instead of checking the supplied proof artifact.
    if paranoid:
        environment = checking_environment()
        if isinstance(runner, Runner) and runner.environment is None:
            runner.environment = environment
    # Discover the toolchain without evaluating the workspace's lakefile. This
    # matters in compare mode, before Lake's export-checking sandbox starts.
    # Explicit --lake launchers must have a sibling lean launcher; the default
    # names resolve through the same PATH/toolchain selection.
    lean = str(Path(lake).with_name("lean"))
    prefix = Path(runner.run([lean, "--print-prefix"], root, "toolchain-prefix").strip())
    if not prefix.is_absolute():
        raise CheckError("lean --print-prefix did not return an absolute toolchain path")
    binaries = ["lake", "lean", "leanexport", *(CHECKERS if paranoid else [])]
    for name in binaries:
        binary = prefix / "bin" / name
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise CheckError(f"missing bundled tool: {binary}")
    version = runner.run([str(prefix / "bin/lean"), "--version"], root, "toolchain-version").strip()
    if not version.startswith("Lean (version 4.35.0,"):
        raise CheckError(f"unsupported toolchain (primitive target list is for Lean 4.35.0): {version}")
    return prefix, {"version": version, "binaries": {n: digest(prefix / "bin" / n) for n in binaries}}


def replay_toolset(path, stock_prefix):
    """Validate a build receipt against this checkout's finite patch recipe.

    Hashes identify reviewed inputs, not authenticity. The build receipt remains
    a reviewable assertion about the source-to-binary build, like capture provenance.
    """
    path = path.absolute()
    if path != path.resolve():
        raise CheckError("symlink in replay toolset path")
    root = path.parent
    regular_file(root, path.name)
    manifest_identity = identity(path)
    receipt = read_json(path)
    fields = {"format", "label", "recipe_sha256", "builder_sha256", "inputs", "commands", "runtime", "reuse"}
    if (not isinstance(receipt, dict) or set(receipt) != fields or receipt["format"] != TOOLSET_FORMAT or
            receipt["label"] != "patched Lean 4.35.0 replay" or receipt["recipe_sha256"] != digest(REPLAY_SOURCES) or
            receipt["builder_sha256"] != digest(LEAN / "checks/build_replay_tools.py")):
        raise CheckError("unsupported or changed replay toolset recipe")
    inputs = receipt["inputs"]
    if not isinstance(inputs, dict) or set(inputs) != {"toolchain", "sources", "patches"}:
        raise CheckError("missing replay build inputs")
    pins = read_json(REPLAY_SOURCES)
    patched_sources = dict(pins["sources"])
    for patch in pins["patches"]:
        patched_sources[patch["target"]] = patch["patched_sha256"]
        if digest(REPLAY_SOURCES.parent / "patches" / patch["file"]) != patch["sha256"]:
            raise CheckError("changed replay patch")
    if inputs["sources"] != patched_sources or inputs["patches"] != pins["patches"]:
        raise CheckError("replay source/patch identity mismatch")
    toolchain = inputs["toolchain"]
    if not isinstance(toolchain, dict) or not set(RUNTIME_FILES) <= toolchain.keys():
        raise CheckError("missing stock runtime provenance")
    for relative in RUNTIME_FILES:
        if identity(stock_prefix / relative)[0] != toolchain[relative]:
            raise CheckError(f"stock toolchain differs from replay build: {relative}")
    runtime = receipt["runtime"]
    if not isinstance(runtime, dict) or set(runtime) != set(RUNTIME_FILES):
        raise CheckError("replay toolset must retain every selected checker and runtime library")
    if not isinstance(receipt["commands"], list) or not receipt["commands"]:
        raise CheckError("missing replay build commands")
    snapshots = {str(path): manifest_identity}
    for name, expected in patched_sources.items():
        file = regular_file(root, "sources/" + name)
        snapshots[str(file)] = identity(file)
        if snapshots[str(file)][0]["sha256"] != expected:
            raise CheckError(f"replay source identity mismatch: {name}")
    for patch in pins["patches"]:
        file = regular_file(root, "patches/" + patch["file"])
        snapshots[str(file)] = identity(file)
        if snapshots[str(file)][0]["sha256"] != patch["sha256"]:
            raise CheckError(f"replay patch identity mismatch: {file}")
    sysroot = root / "sysroot"
    if any(p.is_symlink() for p in sysroot.rglob("*")):
        raise CheckError("symlink in replay runtime")
    actual = {str(p.relative_to(sysroot)) for p in sysroot.rglob("*") if not p.is_dir()}
    if actual != set(runtime):
        raise CheckError("unexpected replay runtime files")
    for relative, expected in runtime.items():
        file = regular_file(sysroot, relative)
        snapshots[str(file)] = identity(file)
        if snapshots[str(file)][0] != expected:
            raise CheckError(f"replay binary/library identity mismatch: {relative}")
        if relative.startswith("bin/") and not os.access(file, os.X_OK):
            raise CheckError(f"nonexecutable replay tool: {relative}")
        if relative not in {f"bin/{n}" for n in PATCHED_CHECKERS} and expected != toolchain[relative]:
            raise CheckError(f"replay toolset changed a stock tool/library: {relative}")
    return receipt, sysroot, snapshots


def select_replay_toolset(path, prefix, toolchain, output, runner):
    if path is None:
        return prefix, toolchain
    receipt, sysroot, snapshots = replay_toolset(path, prefix)
    # Run a separate regular-file snapshot. Lake binds this complete runtime
    # read-only, so symlinks into hidden home/tmp directories are unnecessary.
    frozen = output / "replay-runtime"
    for relative, expected in receipt["runtime"].items():
        source = regular_file(sysroot, relative)
        target = frozen / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        target.chmod(0o555 if relative.startswith("bin/") else 0o444)
        snapshots[str(target)] = identity(target)
        if snapshots[str(target)][0] != expected:
            raise CheckError(f"replay runtime changed while copying: {relative}")

    def unchanged():
        for runtime_root in [sysroot, frozen]:
            actual = {str(p.relative_to(runtime_root)) for p in runtime_root.rglob("*") if not p.is_dir()}
            if actual != set(RUNTIME_FILES):
                raise CheckError(f"replay toolset layout changed during checking: {runtime_root}")
        for directory, expected in directories.items():
            if file_metadata(directory) != expected:
                raise CheckError(f"replay toolset directory changed during checking: {directory}")
        for name, expected in snapshots.items():
            file = Path(name)
            if file != file.resolve() or identity(file) != expected:
                raise CheckError(f"replay toolset changed during checking: {name}")

    # Directory ctime also notices an extra loader input added and removed
    # between checks, while every originally recorded file remains unchanged.
    directories = {directory: file_metadata(directory)
                   for runtime_root in [sysroot, frozen]
                   for directory in [runtime_root, *runtime_root.rglob("*")] if directory.is_dir()}
    unchanged()
    runner.guards.append(unchanged)
    return frozen, {**toolchain, "replay_toolset": {"manifest": str(path), "sha256": digest(path),
                                                  "provenance": receipt}}


def export_command(lake, exporter, group):
    return [lake, "env", str(exporter), *group["modules"], "--",
            *group["theorems"], *AXIOMS, *PRIMITIVES]


def capture(root, groups, selected, output, lake, runner):
    prefix, toolchain = tools_for(root, lake, runner)
    source = {"revision": runner.run(["git", "rev-parse", "HEAD"], root, "source-revision").strip(),
              "status": runner.run(["git", "status", "--porcelain=v1", "--untracked-files=normal"],
                                   root.parent, "source-status")}
    runner.run(["git", "diff", "--binary", "HEAD"], root.parent, "source-diff")
    source["diff_sha256"] = digest(output / "source-diff.log")
    manifest = {"format": CAPTURE_FORMAT, "created_utc": datetime.now(timezone.utc).isoformat(),
                "source": source, "toolchain": toolchain,
                "lock_sha256": digest(root / "checks/claims.lock.json"), "packages": {}}
    for package in selected:
        print(f"capture {package}: {len(groups[package]['theorems'])} declarations", flush=True)
        directory = root / PACKAGES[package]
        group = groups[package]
        search = runner.run([lake, "env", "printenv", "LEAN_PATH"], directory, f"{package}-search-path").strip()
        inputs = {}
        for module in group["modules"]:
            relative = Path(*module.split("."))
            candidates = [(directory / part / relative).with_suffix(".olean")
                          for part in search.split(os.pathsep) if part]
            olean = next((p.resolve() for p in candidates if p.is_file()), None)
            if olean is None:
                raise CheckError(f"{package}: missing existing olean for {module}; build separately before capture")
            inputs[module] = {str(p): digest(p) for p in sorted(olean.parent.glob(olean.name + "*")) if p.is_file()}
        inputs_before = {p: h for row in inputs.values() for p, h in row.items()}
        path = output / f"{package}.ndjson"
        command = export_command(lake, prefix / "bin/leanexport", group)
        runner.run(command, directory, f"{package}-export", export=path)
        if any(digest(p) != h for p, h in inputs_before.items()):
            raise CheckError(f"{package}: selected oleans changed during capture; retry after the build finishes")
        manifest["packages"][package] = {
            "file": path.name, "sha256": digest(path), "bytes": path.stat().st_size,
            "theorems": group["theorems"], "modules": group["modules"], "inputs": inputs,
            "comparator_sha256": digest(group["config"]), "command": command}
    manifest["commands"] = runner.commands
    write_json(output / "manifest.json", manifest)


def load_artifacts(path, groups, selected, export_limit=2048 * 1024**2):
    """Validate one independently captured export set and its provenance."""
    manifest = read_json(path)
    if not isinstance(manifest, dict):
        raise CheckError(f"{path}: expected an export manifest")
    if manifest.get("format") == CAPTURE_FORMAT:
        rows = manifest.get("packages")
        if set(manifest) != {"format", "created_utc", "source", "toolchain", "lock_sha256", "packages", "commands"}:
            raise CheckError(f"{path}: unexpected capture manifest fields")
        if not isinstance(manifest.get("source"), dict) or \
                set(manifest["source"]) != {"revision", "status", "diff_sha256"} or \
                not isinstance(manifest["source"].get("revision"), str) or \
                not re.fullmatch(r"[0-9a-f]{40}", manifest["source"]["revision"]) or \
                not isinstance(manifest.get("toolchain"), dict) or \
                set(manifest["toolchain"]) != {"version", "binaries"} or \
                not isinstance(manifest["toolchain"].get("version"), str) or \
                not manifest["toolchain"]["version"] or not isinstance(manifest.get("lock_sha256"), str) or \
                not re.fullmatch(r"[0-9a-f]{64}", manifest["lock_sha256"]):
            raise CheckError(f"{path}: missing capture provenance")
    else:
        raise CheckError(f"{path}: unsupported export manifest format")
    if not isinstance(rows, dict) or set(rows) - set(PACKAGES):
        raise CheckError(f"{path}: invalid package artifacts")
    result = {}
    for package in selected:
        row = rows.get(package)
        if not isinstance(row, dict):
            raise CheckError(f"{path}: missing package {package}")
        fields = {"file", "sha256", "bytes", "theorems", "modules", "inputs", "comparator_sha256", "command"}
        if set(row) != fields:
            raise CheckError(f"{path}: unexpected {package} artifact fields")
        if sorted(names(row.get("theorems"), str(path))) != groups[package]["theorems"]:
            raise CheckError(f"{path}: {package} declaration coverage differs from the lock")
        file = row.get("file")
        if not isinstance(file, str) or Path(file).name != file:
            raise CheckError(f"{path}: artifact file must be a basename")
        artifact = (path.parent / file).resolve()
        if artifact.is_file() and artifact.stat().st_size > export_limit:
            raise CheckError(f"{path}: {package} export output limit exceeded")
        if not artifact.is_file() or artifact.stat().st_size != row.get("bytes") or \
                digest(artifact) != row.get("sha256"):
            raise CheckError(f"{path}: {package} missing artifact or size/SHA-256 mismatch")
        result[package] = artifact
    return manifest, result


def require_export_roots(path, roots):
    """Check actual root presence for replay, which has no comparator target walk.

    Keep only the finite prefixes of locked names, not the entire export graph.
    Kernels still parse/check every record; this inventory is not an evaluator.
    """
    prefixes = {".".join(name.split(".")[:i]) for name in roots
                for i in range(1, len(name.split(".")) + 1)}
    identifiers, seen, found = {0: ""}, set(), set()
    with path.open() as stream:
        while raw := stream.readline(8 * 1024**2 + 1):
            if len(raw.encode()) > 8 * 1024**2:
                raise CheckError(f"{path}: export record exceeds 8 MiB")
            try:
                row = json.loads(raw, object_pairs_hook=unique_json_object)
                if "in" in row and "str" in row:
                    part = row["str"]
                    parent = identifiers.get(part["pre"])
                    # Lean name components can themselves contain dots; such
                    # a component is distinct from a dotted locked namespace.
                    name = ((parent + "." if parent else "") + part["str"]
                            if parent is not None and "." not in part["str"] else None)
                    if name in prefixes:
                        if name in seen:
                            raise CheckError(f"{path}: duplicate root name table entry: {name}")
                        identifiers[row["in"]] = name
                        seen.add(name)
                for kind in ["def", "thm", "opaque", "axiom", "quot"]:
                    if kind in row and identifiers.get(row[kind]["name"]) in roots:
                        found.add(identifiers[row[kind]["name"]])
                if "inductive" in row:
                    for kind in ["types", "ctors", "recs"]:
                        found.update(identifiers[d["name"]] for d in row["inductive"][kind]
                                     if identifiers.get(d["name"]) in roots)
            except (ValueError, TypeError, KeyError) as error:
                raise CheckError(f"{path}: malformed export inventory: {error}") from error
    if missing := set(roots) - found:
        raise CheckError(f"{path}: missing locked export roots: {sorted(missing)}")


def compare(root, groups, selected, output, lake, runner, base_path, candidate_path, toolset_path=None):
    if base_path.samefile(candidate_path):
        raise CheckError("base and candidate manifests must be independent artifacts")
    export_limit = getattr(runner, "export_limit", 2048 * 1024**2)
    base, challenges = load_artifacts(base_path, groups, selected, export_limit)
    candidate, solutions = load_artifacts(candidate_path, groups, selected, export_limit)
    if any(a.samefile(b) for a in challenges.values() for b in solutions.values()):
        raise CheckError("base and candidate exports must be independent artifacts (including hard links)")
    guard_files(runner, [base_path, candidate_path, *challenges.values(), *solutions.values()])
    prefix, toolchain = tools_for(root, lake, runner, paranoid=True)
    if candidate["toolchain"]["version"] != toolchain["version"] or \
            ("toolchain" in base and base["toolchain"]["version"] != toolchain["version"]):
        raise CheckError("capture and comparison toolchain versions differ")
    prefix, toolchain = select_replay_toolset(toolset_path, prefix, toolchain, output, runner)
    report = {"format": REPORT_FORMAT, "status": "checking", "packages": {}, "toolchain": toolchain,
              "lock_sha256": digest(root / "checks/claims.lock.json"),
              "base": {"manifest": str(base_path), "sha256": digest(base_path), "provenance": base},
              "candidate": {"manifest": str(candidate_path), "sha256": digest(candidate_path), "provenance": candidate}}
    try:
        for package in selected:
            print(f"compare {package}: {len(groups[package]['theorems'])} declarations", flush=True)
            # Freeze the reviewed policy in the report directory before invoking Lake.
            config = output / f"{package}-comparator.json"
            write_json(config, groups[package]["policy"])
            directory = root / PACKAGES[package]
            runner.run([str(prefix / "bin/lake"), "comparator", "--config", str(config),
                        "--challenge-from-export", str(challenges[package]),
                        "--solution-from-export", str(solutions[package])], directory, f"{package}-comparator")
            runner.run([str(prefix / "bin/lake"), "check", "--paranoid", "--from-export",
                        str(solutions[package])], directory, f"{package}-paranoid")
            report["packages"][package] = {"status": "passed", "theorems": groups[package]["theorems"]}
        # A mutable export cannot acquire a verdict using its earlier digest.
        load_artifacts(base_path, groups, selected, export_limit)
        load_artifacts(candidate_path, groups, selected, export_limit)
        if digest(base_path) != report["base"]["sha256"] or digest(candidate_path) != report["candidate"]["sha256"]:
            raise CheckError("artifact manifest changed during comparison")
        if isinstance(runner, Runner):
            runner.verify_inputs()
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=str(error))
        raise
    finally:
        report["commands"] = runner.commands
        write_json(output / "report.json", report)


def replay(root, groups, selected, output, lake, runner, candidate_path, toolset_path=None):
    """Current proof/axiom validation only; no fixed-model or transition verdict."""
    export_limit = getattr(runner, "export_limit", 2048 * 1024**2)
    candidate, solutions = load_artifacts(candidate_path, groups, selected, export_limit)
    guard_files(runner, [candidate_path, *solutions.values()])
    prefix, toolchain = tools_for(root, lake, runner, paranoid=True)
    if candidate["toolchain"]["version"] != toolchain["version"]:
        raise CheckError("capture and replay toolchain versions differ")
    prefix, toolchain = select_replay_toolset(toolset_path, prefix, toolchain, output, runner)
    report = {"format": REPLAY_FORMAT, "status": "checking", "packages": {}, "toolchain": toolchain,
              "scope": "proof and standard axiom validation; no model comparison or baseline acceptance",
              "lock_sha256": digest(root / "checks/claims.lock.json"),
              "candidate": {"manifest": str(candidate_path), "sha256": digest(candidate_path), "provenance": candidate}}
    try:
        for package in selected:
            print(f"replay {package}: {len(groups[package]['theorems'])} declarations", flush=True)
            require_export_roots(solutions[package], groups[package]["theorems"])
            runner.run([str(prefix / "bin/lake"), "check", "--paranoid", "--from-export",
                        str(solutions[package])], root / PACKAGES[package], f"{package}-paranoid")
            report["packages"][package] = {"status": "passed", "theorems": groups[package]["theorems"]}
        load_artifacts(candidate_path, groups, selected, export_limit)
        if digest(candidate_path) != report["candidate"]["sha256"]:
            raise CheckError("artifact manifest changed during replay")
        if isinstance(runner, Runner):
            runner.verify_inputs()
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=str(error))
        raise
    finally:
        report["commands"] = runner.commands
        write_json(output / "report.json", report)


def positive(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["capture", "compare", "replay"])
    parser.add_argument("--lean-root", type=Path, default=LEAN)
    parser.add_argument("--package", choices=list(PACKAGES), action="append", help="repeatable; default: all four")
    parser.add_argument("--output", type=Path, required=True, help="new directory, never overwritten")
    parser.add_argument("--base-manifest", type=Path)
    parser.add_argument("--candidate-manifest", type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--replay-toolset", type=Path, help="explicit locally built patched replay manifest (checking only)")
    parser.add_argument("--memory-mb", type=positive, default=8192, help="address-space bound per child")
    parser.add_argument("--log-mb", type=positive, default=8, help="bound per command, combined stdout/stderr")
    parser.add_argument("--export-mb", type=positive, default=2048, help="bound per export")
    parser.add_argument("--timeout", type=positive, default=1800, help="seconds per command")
    args = parser.parse_args(argv)
    if args.mode == "compare" and (not args.base_manifest or not args.candidate_manifest):
        parser.error("compare requires explicit --base-manifest and --candidate-manifest")
    if args.mode == "capture" and (args.base_manifest or args.candidate_manifest):
        parser.error("capture does not accept comparison artifacts")
    if args.mode == "capture" and args.replay_toolset:
        parser.error("capture uses the stock exporter; --replay-toolset is for checking only")
    if args.mode == "replay" and (not args.candidate_manifest or args.base_manifest):
        parser.error("replay requires --candidate-manifest and does not accept --base-manifest")
    output = args.output.resolve()
    created = False
    runner = None
    try:
        root = args.lean_root.resolve()
        groups = configuration(root)
        selected = list(dict.fromkeys(args.package or PACKAGES))
        output.mkdir(parents=True, exist_ok=False)
        created = True
        runner = Runner(output, args.memory_mb, args.log_mb, args.export_mb, args.timeout)
        if args.mode == "capture":
            capture(root, groups, selected, output, args.lake, runner)
            print(f"Captured artifacts only; no checking verdict: {output / 'manifest.json'}")
        elif args.mode == "compare":
            compare(root, groups, selected, output, args.lake, runner,
                    args.base_manifest.resolve(), args.candidate_manifest.resolve(), args.replay_toolset)
            print(f"Passed {sum(len(groups[p]['theorems']) for p in selected)} locked declarations: {output / 'report.json'}")
        else:
            replay(root, groups, selected, output, args.lake, runner,
                   args.candidate_manifest.resolve(), args.replay_toolset)
            print(f"Proof/axiom replay passed only; model review remains separate: {output / 'report.json'}")
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        if created:
            write_json(output / "failure.json", {"status": "failed", "error": str(error),
                                                "commands": runner.commands if runner else []})
        print(f"independent checking failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
