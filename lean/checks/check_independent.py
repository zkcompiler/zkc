#!/usr/bin/env python3
"""Capture locked declarations, or compare explicit independent export artifacts.

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


class CheckError(ValueError):
    """An incomplete or rejected check, never an acceptance."""


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise CheckError(f"{path}: duplicate JSON key {key}")
            result[key] = value
        return result
    try:
        if Path(path).stat().st_size > 16 * 1024**2:
            raise CheckError(f"{path}: metadata exceeds 16 MiB")
        return json.loads(Path(path).read_text(), object_pairs_hook=unique)
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

    def __init__(self, output, memory_mb=8192, log_mb=8, export_mb=2048, timeout=1800):
        self.output = output
        self.memory = memory_mb * 1024**2
        self.log_limit = log_mb * 1024**2
        self.export_limit = export_mb * 1024**2
        self.timeout = timeout
        self.commands = []

    def run(self, command, cwd, label, export=None):
        log = self.output / f"{label}.log"
        record = {"command": [str(c) for c in command], "cwd": str(cwd), "log": log.name}
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
                                             env={**os.environ, "LEAN_ABORT_ON_PANIC": "1"},
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
        return log.read_text() if export is None else None


def tools_for(root, lake, runner, paranoid=False):
    # Lake tests presence, not truthiness: even an empty value selects its
    # internal export path instead of checking the supplied proof artifact.
    if paranoid and "LAKE_CHECK_EXPORT" in os.environ:
        raise CheckError("unset LAKE_CHECK_EXPORT before comparing")
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


def load_artifacts(path, groups, selected):
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
        if not artifact.is_file() or artifact.stat().st_size != row.get("bytes") or \
                digest(artifact) != row.get("sha256"):
            raise CheckError(f"{path}: {package} missing artifact or size/SHA-256 mismatch")
        result[package] = artifact
    return manifest, result


def compare(root, groups, selected, output, lake, runner, base_path, candidate_path):
    if base_path.samefile(candidate_path):
        raise CheckError("base and candidate manifests must be independent artifacts")
    base, challenges = load_artifacts(base_path, groups, selected)
    candidate, solutions = load_artifacts(candidate_path, groups, selected)
    if any(a.samefile(b) for a in challenges.values() for b in solutions.values()):
        raise CheckError("base and candidate exports must be independent artifacts (including hard links)")
    prefix, toolchain = tools_for(root, lake, runner, paranoid=True)
    if candidate["toolchain"]["version"] != toolchain["version"] or \
            ("toolchain" in base and base["toolchain"]["version"] != toolchain["version"]):
        raise CheckError("capture and comparison toolchain versions differ")
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
        load_artifacts(base_path, groups, selected)
        load_artifacts(candidate_path, groups, selected)
        if digest(base_path) != report["base"]["sha256"] or digest(candidate_path) != report["candidate"]["sha256"]:
            raise CheckError("artifact manifest changed during comparison")
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
    parser.add_argument("mode", choices=["capture", "compare"])
    parser.add_argument("--lean-root", type=Path, default=LEAN)
    parser.add_argument("--package", choices=list(PACKAGES), action="append", help="repeatable; default: all four")
    parser.add_argument("--output", type=Path, required=True, help="new directory, never overwritten")
    parser.add_argument("--base-manifest", type=Path)
    parser.add_argument("--candidate-manifest", type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--memory-mb", type=positive, default=8192, help="address-space bound per child")
    parser.add_argument("--log-mb", type=positive, default=8, help="bound per command, combined stdout/stderr")
    parser.add_argument("--export-mb", type=positive, default=2048, help="bound per export")
    parser.add_argument("--timeout", type=positive, default=1800, help="seconds per command")
    args = parser.parse_args(argv)
    if args.mode == "compare" and (not args.base_manifest or not args.candidate_manifest):
        parser.error("compare requires explicit --base-manifest and --candidate-manifest")
    if args.mode == "capture" and (args.base_manifest or args.candidate_manifest):
        parser.error("capture does not accept comparison artifacts")
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
        else:
            compare(root, groups, selected, output, args.lake, runner,
                    args.base_manifest.resolve(), args.candidate_manifest.resolve())
            print(f"Passed {sum(len(groups[p]['theorems']) for p in selected)} locked declarations: {output / 'report.json'}")
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        if created:
            write_json(output / "failure.json", {"status": "failed", "error": str(error),
                                                "commands": runner.commands if runner else []})
        print(f"independent checking failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
