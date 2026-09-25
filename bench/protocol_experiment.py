#!/usr/bin/env python3
"""Retain bounded frontend experiments and measure actual compiler stages."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import shutil
import signal
import stat
import statistics
import subprocess
import sys
import threading
import time

VERSION = "zkc.protocol-experiment/1"
LIMIT = 1024 * 1024
ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def open_regular(path):
    # Nonblocking open lets us reject a FIFO without waiting for its writer.
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NONBLOCK", 0))
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValueError("input must be a regular file")
        return os.fdopen(descriptor, "rb")
    except BaseException:
        os.close(descriptor)
        raise


def file_digest(path):
    with open_regular(path) as stream:
        checksum = hashlib.sha256()
        for block in iter(lambda: stream.read(LIMIT), b""):
            checksum.update(block)
        return checksum.hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def machine():
    cpu = platform.processor()
    try:
        cpu = next(line.split(":", 1)[1].strip() for line in
                   Path("/proc/cpuinfo").read_text().splitlines()
                   if line.startswith("model name"))
    except (OSError, StopIteration):
        pass
    return {"platform": platform.platform(), "machine": platform.machine(),
            "cpu": cpu, "logical_cpus": os.cpu_count(),
            "python": sys.version, "timer": "time.perf_counter_ns"}


def summary(samples):
    return {"samples_ms": samples, "iterations": len(samples),
            "median_ms": statistics.median(samples), "min_ms": min(samples)}


def bounded(value, low, high):
    number = int(value)
    if not low <= number <= high:
        raise argparse.ArgumentTypeError(f"expected {low}..{high}")
    return number


def snapshot(path):
    """One open/read: all stages and the hash consume this same captured value.

    This is not an atomic filesystem snapshot of a concurrently written file.
    The byte string actually read is the sole source authority for this run.
    """
    with open_regular(path) as stream:
        return stream.read(LIMIT + 1)


def presentation(data, seed, enabled):
    if not enabled:
        return data
    rng = random.Random(seed)
    prefix = "\n" * rng.randint(1, 4) + " " * rng.randint(0, 8)
    if not data.lstrip().startswith(b"["):
        prefix += f"// research presentation {rng.getrandbits(64):016x}\n"
    # Only prepend trivia: strings, comments, labels and selectors are untouched.
    return prefix.encode() + data


def synthetic(calls):
    lines = ["module {", "  fn Identity<F: domain Field>(x: F::Element) -> (F::Element) {",
             "    return (x);", "  }", "  configure Open = Identity();"]
    lines += [f'  configure Choice{i} = Open(F = "bls12-381.fr");'
              for i in range(calls)]
    lines += ["  protocol Repeated {", "    roles (Alice);",
              "    inputs (Alice x: bls12-381.fr::Element);",
              "    outputs (Alice bls12-381.fr::Element);"]
    previous = "x"
    for i in range(calls):
        lines.append(f"    local [call{i}] Alice: let v{i} = Choice{i}({previous});")
        previous = f"v{i}"
    lines += [f"    return ({previous});", "  }",
              "  instance repeated: Repeated { roles (Alice = Alice); }",
              "  entry main = repeated;", "}"]
    return ("\n".join(lines) + "\n").encode()


class Bundle:
    def __init__(self, output, argv):
        self.start = time.perf_counter_ns()
        # Even an empty existing directory or dangling symlink is refused.
        self.path = Path(output).absolute()
        self.path.mkdir(mode=0o700, parents=True, exist_ok=False)
        self.path = self.path.resolve()
        self.data = {"format": VERSION, "status": "running", "argv": argv,
                     "created_utc": datetime.now(timezone.utc).isoformat(),
                     "cwd": str(Path.cwd()), "machine": machine(),
                     "tools": {}, "artifacts": {}, "stages": [],
                     "minimization": "none; exact captured reproducer retained",
                     "claims": ["developer measurements only", "no normalization semantics",
                                "no native/Lean execution agreement or correctness proof"]}
        self.save()

    def path_for(self, name):
        # All artifact names are tool-owned, never copied from a supplied name.
        if Path(name).name != name or name in ("", ".", ".."):
            raise ValueError("artifact name must be a single path component")
        return self.path / name

    def record(self, name):
        path = self.path_for(name)
        self.data["artifacts"][name] = {
            "bytes": path.stat().st_size, "sha256": file_digest(path)}

    def write(self, name, data):
        with self.path_for(name).open("xb") as stream:
            stream.write(data)
        self.record(name)
        return name

    def save(self):
        # This is the sole replaceable file, inside our exclusively created directory.
        temporary = self.path_for("manifest.next")
        with temporary.open("xb") as stream:
            stream.write(encode(self.data))
        temporary.replace(self.path_for("manifest.json"))

    def note(self, name, status, reason, required=True):
        stage = {"name": name, "status": status, "reason": reason, "required": required}
        self.data["stages"].append(stage)
        self.save()
        return stage

    def command(self, name, argv, stdin=None, timeout=60, required=True):
        stage = {"name": name, "argv": [str(x) for x in argv],
                 "cwd": str(self.path), "stdin": stdin, "timeout_seconds": timeout,
                 "required": required, "status": "running", "exit_code": None,
                 "stdout": name + ".stdout", "stderr": name + ".stderr"}
        self.data["stages"].append(stage)
        self.save()
        start = time.perf_counter_ns()
        proc = None
        try:
            with self.path_for(stage["stdout"]).open("xb") as out, \
                    self.path_for(stage["stderr"]).open("xb") as err:
                payload = self.path_for(stdin).read_bytes() if stdin else None
                try:
                    proc = subprocess.Popen(stage["argv"], cwd=self.path,
                                            stdin=subprocess.PIPE if stdin else subprocess.DEVNULL,
                                            stdout=out, stderr=err, start_new_session=True)
                    expired = threading.Event()

                    def stop():
                        try:
                            if os.name == "posix":
                                os.killpg(proc.pid, signal.SIGKILL)
                            else:
                                proc.kill()
                        except ProcessLookupError:
                            pass

                    def deadline():
                        if proc.poll() is None:
                            expired.set()
                            stop()

                    # A blocking wait with a watchdog avoids Popen.wait(timeout)'s
                    # timed polling, which otherwise quantizes short CLI samples.
                    watchdog = threading.Timer(timeout, deadline)
                    watchdog.start()
                    try:
                        proc.communicate(input=payload)
                    finally:
                        watchdog.cancel()
                        watchdog.join()
                    stage["exit_code"] = proc.returncode
                    stage["status"] = "success" if proc.returncode == 0 else "refused"
                    if proc.returncode < 0:
                        stage["status"] = "failed"
                    if expired.is_set():
                        stage["status"] = "timeout"
                except KeyboardInterrupt:
                    if proc is not None:
                        stop()
                        proc.communicate()
                        stage["exit_code"] = proc.returncode
                    stage["status"] = "interrupted"
                    raise
                except OSError as error:
                    stage["status"] = "unavailable"
                    stage["reason"] = str(error)
                    err.write((str(error) + "\n").encode())
        finally:
            stage["elapsed_ms"] = (time.perf_counter_ns() - start) / 1e6
            for key in ("stdout", "stderr"):
                if self.path_for(stage[key]).exists():
                    self.record(stage[key])
            self.save()
        return stage

    def tool(self, key, executable, version_args=("--version",)):
        supplied = str(executable)
        found = shutil.which(supplied)
        path = str(Path(found).resolve()) if found else str(Path(supplied).absolute())
        info = {"requested": supplied, "path": path, "version": "unavailable"}
        try:
            info.update(sha256=file_digest(path), bytes=Path(path).stat().st_size)
        except (OSError, ValueError) as error:
            info["unavailable"] = str(error)
        self.data["tools"][key] = info
        probe = self.command(key + "-version", [path, *version_args], required=False)
        if probe["status"] == "success":
            info["version"] = self.path_for(probe["stdout"]).read_text(errors="replace").strip()
        info["version_stage"] = probe["name"]
        self.save()
        return path

    def capture(self, key, path):
        data = snapshot(path)
        name = self.write(key + ".bin", data)
        if key == "original":
            self.write("original.txt", data.decode("utf-8", errors="backslashreplace").encode())
        self.data.setdefault("supplied", {})[key] = {
            "path": str(Path(path).absolute()), "artifact": name,
            "capture_complete": len(data) <= LIMIT}
        self.save()
        if len(data) > LIMIT:
            raise ValueError(f"{key}: exceeds 1 MiB; retained prefix only, stage refused")
        return data, name

    def finish(self):
        bad = [s for s in self.data["stages"]
               if s["required"] and s["status"] != "success"]
        self.data["status"] = "incomplete" if bad else "success"
        self.data["elapsed_ms_before_final_manifest"] = (time.perf_counter_ns() - self.start) / 1e6
        self.save()
        return 1 if bad else 0


def success(stage):
    return stage["status"] == "success"


def run(args, argv):
    bundle = Bundle(args.output, argv)
    try:
        original, _ = bundle.capture("original", args.source)
        data = presentation(original, args.seed, args.presentation)
        source = bundle.write("source.json" if data.lstrip().startswith(b"[") else "source.pir", data)
        bundle.data["source"] = {"artifact": source, "sha256": digest(data),
                                 "seed": args.seed, "presentation": args.presentation,
                                 "authority": "one captured byte string; original path is never reread"}
        if len(data) > LIMIT:
            raise ValueError("presentation exceeds 1 MiB")
        supplied = {}
        for key in ("inputs", "config", "descriptor", "implementations"):
            if getattr(args, key):
                _, supplied[key] = bundle.capture(key, getattr(args, key))
        bundle.data["supplied_policy"] = {
            "config": "retained context only; configurations are embedded in source",
            "inputs": "retained only unless --lean-reference is requested",
            "implementations": "passed to physical CLI stages only; API benchmark uses source choices",
            "descriptor": "passed to protocol-construct only"}
        bundle.data["tools"]["runner"] = {
            "version": VERSION, "sha256": file_digest(__file__), "path": str(Path(__file__).resolve())}
        bundle.data["tools"]["python"] = {
            "version": sys.version, "path": sys.executable, "sha256": file_digest(sys.executable)}
        compiler = bundle.tool("compiler", args.compiler)
        bundle.data["tools"]["compiler"]["supplied_version"] = args.compiler_version
        bench = bundle.tool("bench", args.bench or str(Path(compiler).with_name("zkc-source-bench")))
        opt = bundle.tool("opt", args.opt or str(Path(compiler).with_name("zkc-opt")))
        lean = bundle.tool("lean", args.lean) if args.lean else None
        if lean:
            bundle.data["tools"]["lean"]["supplied_version"] = args.lean_version
        timeout = args.timeout

        def native(name, mode, dependency=None, stdin=source, extra=()):
            if dependency is not None and not success(dependency):
                return bundle.note(name, "skipped", "dependency: " + dependency["name"])
            return bundle.command(name, [compiler, mode, "-", *extra], stdin, timeout)

        syntax = native("syntax", "protocol-parse")
        native("format", "protocol-format", syntax)
        admitted = native("admission", "protocol-source", syntax)
        native("inspection", "protocol-inspect", syntax)
        common = native("common", "protocol-import", admitted)
        native("logical", "protocol-project", common)
        if success(common):
            bundle.command("project", [opt, "--zkc-project-participants", "-"],
                           common["stdout"], timeout)
        else:
            bundle.note("project", "skipped", "dependency: common")
        selections = ("--implementations=" + supplied["implementations"],) if "implementations" in supplied else ()
        native("physical", "protocol-physical-ir", common, extra=selections)
        participants = native("participants", "protocol-compile", common, extra=selections)
        measurement = bundle.command("benchmark", [bench, "-", "--iterations", str(args.iterations),
                                     "--warmup", str(args.warmup)], source, timeout)
        # Keep structured partial API measurements even when the tool refuses.
        try:
            report = json.loads(bundle.path_for(measurement["stdout"]).read_bytes())
            if not isinstance(report, dict) or report.get("format") != "zkc.source-bench/1":
                raise ValueError("unexpected benchmark report")
            bundle.data["measurement"] = report
            if success(measurement) and report.get("status") != "success":
                measurement.update(status="failed", reason="benchmark exit/report disagree")
        except (ValueError, OSError) as error:
            bundle.data["measurement_error"] = str(error)
            if success(measurement):
                measurement["status"] = "failed"
        if "descriptor" in supplied:
            native("construction", "protocol-construct", admitted,
                   extra=(supplied["descriptor"],))
        if lean:
            if success(admitted):
                portable = json.loads(bundle.path_for(admitted["stdout"]).read_bytes(), parse_int=str)
                tag = portable[0] if isinstance(portable, list) and portable else None

                def independent(name, flags, claim, scope):
                    stage = bundle.command(name, [lean, *flags], timeout=timeout)
                    if success(stage):
                        try:
                            response = json.loads(bundle.path_for(stage["stdout"]).read_bytes())
                            if (not isinstance(response, list) or len(response) < 3
                                    or response[:2] != ["checked", claim] or response[-1] != scope):
                                raise ValueError("unexpected checker claim or scope")
                            stage["claim"] = response
                        except ValueError as error:
                            stage.update(status="failed", reason=str(error))
                    bundle.save()
                    return stage

                if tag == "zkc.protocol/1":
                    bundle.note("lean-source", "not_applicable",
                                "No standalone source admission CLI; --check-generic admits the source while checking participants.",
                                required=False)
                else:
                    independent("lean-source", ["--generic-declarations", admitted["stdout"]],
                                "generic-local-formation", "not-whole-source-admission")
                if success(participants):
                    independent("lean-participants", ["--check-generic", admitted["stdout"], participants["stdout"]],
                                "generic-structural-correspondence", "no-elaboration-adequacy-proof")
                else:
                    bundle.note("lean-participants", "skipped", "dependency: participants")
                if args.lean_reference:
                    stage = bundle.command("lean-reference", [lean, "--generic-reference", admitted["stdout"], supplied["inputs"]],
                                           timeout=timeout)
                    if success(stage):
                        try:
                            response = json.loads(bundle.path_for(stage["stdout"]).read_bytes())
                            if (not isinstance(response, list) or len(response) < 5
                                    or response[0] != "zkc.reference-observation/1"):
                                raise ValueError("unexpected reference observation")
                            outcome = response[3]
                            if not isinstance(outcome, list) or not outcome:
                                raise ValueError("missing reference outcome")
                            stage["outcome"] = outcome
                            stage["scope"] = response[-1]
                            if outcome[0] != "returned":
                                stage["status"] = "refused"
                        except ValueError as error:
                            stage.update(status="failed", reason=str(error))
                        bundle.save()
            else:
                bundle.note("lean-source", "skipped", "dependency: admission")
                bundle.note("lean-participants", "skipped", "dependency: admission")
                if args.lean_reference:
                    bundle.note("lean-reference", "skipped", "dependency: admission")
        bundle.data["output_sizes"] = {
            s["name"]: bundle.data["artifacts"][s["stdout"]]["bytes"]
            for s in bundle.data["stages"] if s["status"] == "success" and "stdout" in s}
        bundle.data["emitted_counts"] = {}
        for stage in bundle.data["stages"]:
            if stage["name"] in ("logical", "participants") and success(stage):
                value = json.loads(bundle.path_for(stage["stdout"]).read_bytes(), parse_int=str)
                bundle.data["emitted_counts"][stage["name"]] = {
                    "functions": len(value[3]), "participants": len(value[4]), "entries": len(value[5])}
    except KeyboardInterrupt:
        bundle.note("runner", "interrupted", "KeyboardInterrupt")
        bundle.finish()
        return 130
    except (OSError, ValueError) as error:
        bundle.note("runner", "refused", str(error))
    code = bundle.finish()
    print(str(bundle.path / "manifest.json"))
    return code


def run_suite(bundle, args):
    cases = [(stem, snapshot(ROOT / "tests/fixtures" / (stem + ".pir")))
             for stem in ("generic-dleq", "generic-committed-two-factor")]
    cases += [(f"sharing-{n}", synthetic(n)) for n in args.scales]
    reports = []
    baseline = bundle.tool("baseline", args.baseline_compiler) if args.baseline_compiler else None
    for name, data in cases:
        input_name = bundle.write(name + ".pir", data)
        item = {"case": name, "source_sha256": digest(data), "runs": []}
        durations = []
        cli = {mode: [] for mode in ("protocol-source", "protocol-import", "protocol-project", "protocol-compile")}
        api = {}
        for i in range(args.repeats):
            directory = bundle.path / f"{name}-{i}"
            command = [sys.executable, str(Path(__file__).resolve()), "run",
                       str(bundle.path / input_name), "--output", str(directory),
                       "--compiler", str(Path(shutil.which(args.compiler) or args.compiler).absolute()),
                       "--iterations", str(args.iterations), "--warmup", str(args.warmup),
                       "--timeout", str(args.timeout), "--seed", str(args.seed)]
            for option in ("bench", "opt", "lean", "compiler_version", "lean_version"):
                if getattr(args, option):
                    value = getattr(args, option)
                    if option in ("bench", "opt", "lean"):
                        value = str(Path(shutil.which(value) or value).absolute())
                    command += ["--" + option.replace("_", "-"), value]
            stage = bundle.command(f"{name}-{i}", command, timeout=args.timeout * 20)
            durations.append(stage["elapsed_ms"])
            manifest = directory / "manifest.json"
            if manifest.exists():
                run_report = json.loads(manifest.read_bytes())
                item["runs"].append({"manifest": str(manifest.relative_to(bundle.path)),
                                     "manifest_sha256": file_digest(manifest),
                                     "status": run_report["status"],
                                     "measurement": run_report.get("measurement"),
                                     "output_sizes": run_report.get("output_sizes"),
                                     "emitted_counts": run_report.get("emitted_counts"),
                                     "tools": run_report["tools"]})
                for mode, key in (("protocol-source", "admission"), ("protocol-import", "common"),
                                  ("protocol-project", "logical"), ("protocol-compile", "participants")):
                    stage_result = next((s for s in run_report["stages"] if s["name"] == key), None)
                    if stage_result and success(stage_result):
                        cli[mode].append(stage_result["elapsed_ms"])
                for measured in run_report.get("measurement", {}).get("stages", []):
                    if success(measured):
                        api.setdefault(measured["name"], []).extend(measured["samples_us"])
        item["bundle_process"] = summary(durations)
        item["cli_commands"] = {mode: summary(samples) for mode, samples in cli.items() if samples}
        item["api"] = {name: {"samples_us": samples, "iterations": len(samples),
                              "median_us": statistics.median(samples), "min_us": min(samples)}
                       for name, samples in api.items() if samples}
        if baseline:
            old = {"scope": "whole CLI commands only; frozen source has no Document/inspection APIs",
                   "api_timings": "unavailable", "metadata": "unavailable", "commands": {}}
            for mode in ("protocol-source", "protocol-import", "protocol-project", "protocol-compile"):
                times, statuses = [], []
                for i in range(args.repeats):
                    stage = bundle.command(f"baseline-{name}-{mode}-{i}", [baseline, mode, "-"],
                                           input_name, args.timeout)
                    times.append(stage["elapsed_ms"])
                    statuses.append(stage["status"])
                old["commands"][mode] = {**summary(times), "statuses": statuses}
            item["baseline"] = old
        reports.append(item)
        bundle.data["cases"] = reports
        bundle.save()
    bundle.data["comparison"] = "No speedup claim. Baseline commands fuse parsing/admission; API and bundle timings differ in scope."
    bundle.write("results.json", encode({"format": VERSION, "machine": bundle.data["machine"],
                                       "cases": reports, "comparison": bundle.data["comparison"],
                                       "tools": bundle.data["tools"]}))
    code = bundle.finish()
    print(str(bundle.path / "results.json"))
    return code


def suite(args, argv):
    bundle = Bundle(args.output, argv)
    try:
        return run_suite(bundle, args)
    except KeyboardInterrupt:
        bundle.note("runner", "interrupted", "KeyboardInterrupt")
        bundle.finish()
        return 130
    except (OSError, ValueError) as error:
        bundle.note("runner", "refused", str(error))
        return bundle.finish()


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    parser = argparse.ArgumentParser(description=__doc__, epilog=(
        "Every output directory must be new. Original bytes, readable source, SHA256, "
        "commands, partial stdout/stderr and actual stage statuses are retained. "
        "Exit: 0 all requested stages succeed; 1 incomplete evidence; 2 usage/output refusal."))
    parser.add_argument("--version", action="version", version=VERSION)
    commands = parser.add_subparsers(dest="command", required=True)
    single = commands.add_parser("run", help="capture a source and inspect/measure its compiler stages")
    single.add_argument("source", type=Path, help=".pir or portable JSON, at most 1 MiB")
    batch = commands.add_parser("suite", help="DLEQ, committed two-factor, and bounded shared-call clients")
    for child in (single, batch):
        child.add_argument("--output", required=True, type=Path, help="new durable directory; existing paths refused")
        child.add_argument("--compiler", required=True, help="zkc-compile executable")
        child.add_argument("--bench", help="zkc-source-bench (default: compiler sibling)")
        child.add_argument("--opt", help="zkc-opt (default: compiler sibling), for projected MLIR")
        child.add_argument("--lean", help="optional built independent interactive-protocol executable")
        child.add_argument("--compiler-version", help="optional human version/build label; recorded as supplied")
        child.add_argument("--lean-version", help="optional Lean build label; checker has no version endpoint")
        child.add_argument("--iterations", type=lambda s: bounded(s, 1, 1000), default=7, help="API samples (default: 7)")
        child.add_argument("--warmup", type=lambda s: bounded(s, 0, 100), default=1, help="API warmups (default: 1)")
        child.add_argument("--timeout", type=lambda s: bounded(s, 1, 3600), default=60, help="seconds per command (default: 60)")
        child.add_argument("--seed", type=int, default=418920, help="recorded seed (default: 418920)")
    single.add_argument("--presentation", action="store_true", help="prepend bounded seeded whitespace/comment trivia; preserve all labels")
    single.add_argument("--inputs", type=Path, help="retain supplied input bytes")
    single.add_argument("--config", type=Path, help="retain context only; does not modify embedded configurations")
    single.add_argument("--implementations", type=Path, help="physical binding selection file, passed to native CLI")
    single.add_argument("--descriptor", type=Path, help="construction descriptor, also run protocol-construct")
    single.add_argument("--lean-reference", action="store_true", help="also execute Lean source reference; requires --lean and --inputs")
    batch.add_argument("--repeats", type=lambda s: bounded(s, 1, 20), default=3, help="durable whole-bundle repetitions (default: 3)")
    batch.add_argument("--scales", nargs="+", type=lambda s: bounded(s, 1, 128), default=[1, 16, 64], help="distinct equivalent configurations/local calls (1..128)")
    batch.add_argument("--baseline-compiler", help="optional frozen compiler; compare supported whole CLI commands only")
    args = parser.parse_args(argv)
    if args.command == "run" and args.lean_reference and not (args.lean and args.inputs):
        parser.error("--lean-reference requires --lean and --inputs")
    if args.command == "suite" and len(set(args.scales)) != len(args.scales):
        parser.error("--scales must be distinct")
    try:
        return run(args, argv) if args.command == "run" else suite(args, argv)
    except (OSError, ValueError) as error:
        print(f"refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
