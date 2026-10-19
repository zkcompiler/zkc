#!/usr/bin/env python3
"""Exercise actual MLIR exports against independent SSA and Lean execution.

The reference reads original MLIR, never exported descriptors. Optional Runner
comparisons also traverse preparation and realization. Results are bounded
agreement evidence, not a proof of either compiler boundary.
"""

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time
from uuid import uuid4

import snapshot as constructors
from evidence import archive_sources, atomic_json, check_sources, retain_tool

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from reporting import new_directory  # noqa: E402

FIELD = "bls12-381.fr"
MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def fields(values):
    return [str(value) for value in values]


def returned(*values):
    return ["returned", list(values)]


def definition(snapshot, name):
    matches = [item for item in snapshot[7] if item[1] == name]
    if len(matches) != 1:
        raise ValueError(f"expected one definition: {name}")
    return matches[0]


def typed_value(ty, value):
    if ty == ["bool"]:
        return ["bool", value]
    if ty == ["index"]:
        return ["index", int(value)]
    if ty[0] in ("field", "vector"):
        return [ty[0], ty[1], value]
    raise ValueError(f"unsupported typed input {ty}")


def typed_result(types, expected):
    if expected[0] == "stopped":
        return expected
    return ["returned", [typed_value(ty, value) for ty, value in zip(types, expected[1], strict=True)]]


class Suite:
    source_scope = None

    def __init__(self, args):
        self.args = args
        self.directory = None
        self.commands, self.checks, self.sources = [], [], []
        self.tools, self.tool_records = {}, {}
        self.archives = {}
        self.revision = None
        self.identity = str(uuid4())
        self.started = datetime.now(timezone.utc).isoformat()
        self.rng = random.Random(args.seed)

    def source_inventory(self):
        """None selects Git; subclasses can supply a complete owned source set."""
        return None

    def tool_names(self):
        return ("compiler", "optimizer", "reference", "lean", "runtime")

    def success_status(self):
        return "pass"

    def capture_sources(self, stage):
        return archive_sources(ROOT, self.directory / f"source-{stage}",
                               inventory=self.source_inventory(), scope=self.source_scope)

    def setup(self):
        self.directory = new_directory(self.args.report.resolve().parent / "runs",
                                       self.identity, "structured")
        self.publish("running")
        if self.args.cases < 1:
            raise ValueError("--cases must be positive")
        if self.source_inventory() is None:
            self.revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        self.archives["before"] = self.capture_sources("before")
        tool_dir = self.directory / "tools"
        tool_dir.mkdir()
        store = Path(os.environ.get("ZKC_TOOL_STORE") or self.directory.parent / "tool-store")
        for name in self.tool_names():
            source = getattr(self.args, name, None)
            if source is None:
                continue
            source = source.resolve()
            target = tool_dir / name
            before = retain_tool(source, store, target)
            self.tools[name] = target
            self.tool_records[name] = {"path": str(target), "sha256": before,
                                       "source": str(source)}

    def run(self, action):
        """Own setup and finalization for both structured drivers, including failure."""
        status = None
        try:
            # Clear previous success before allocation, copies, Git or commands.
            self.publish("running")
            self.setup()
            action(self)
        except BaseException as error:
            status = self.failure("setup-or-generation", error)
        try:
            return self.finish(status)
        except BaseException as error:
            failure = self.failure("finalization", error)
            status = "interrupted" if "interrupted" in (status, failure) else "failed"
            # A driver-specific finalizer must not bypass the common terminal
            # publisher. Do not re-enter the failed override.
            return Suite.finish(self, status)

    def failure(self, name, error):
        self.checks.append({"name": name, "passed": False,
                            "error": f"{type(error).__name__}: {error}"})
        print(error, file=sys.stderr)
        return "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"

    def publish(self, status):
        report = {"format": "zkc.structured-comparison/0", "seed": self.args.seed,
                  "argv": sys.argv, "cases": self.args.cases,
                  "run": self.identity, "directory": str(self.directory) if self.directory else None,
                  "status": status, "startedUtc": self.started,
                  "revision": self.revision, "tools": self.tool_records,
                  "sourceArchives": self.archives,
                  "sources": self.sources, "checks": self.checks, "commands": self.commands,
                  "scope": "bounded logical outcomes; no native correspondence theorem or resource equivalence"}
        if status != "running":
            report["finishedUtc"] = datetime.now(timezone.utc).isoformat()
        paths = [self.args.report]
        if self.directory is not None:
            paths.insert(0, self.directory / "report.json")
        errors = []
        for path in paths:
            try:
                atomic_json(path, report)
            except BaseException as error:
                errors.append(error)
        if errors:
            raise next((error for error in errors if isinstance(error, KeyboardInterrupt)), errors[0])

    def command(self, label, argv, success=True, timeout=60):
        start = time.monotonic()
        number = len(self.commands)
        prefix = self.directory / f"command-{number:04d}"
        record = {"label": label, "argv": list(map(str, argv)), "output": str(prefix), "exit": None}
        self.commands.append(record)
        try:
            result = subprocess.run(list(map(str, argv)), cwd=ROOT, capture_output=True,
                                    encoding="utf-8", timeout=timeout)
        except subprocess.TimeoutExpired as error:
            record["error"] = f"{type(error).__name__}: {error}"
            for suffix, output in ((".stdout", error.stdout), (".stderr", error.stderr)):
                # TimeoutExpired may carry bytes even when text mode was requested.
                path = prefix.with_suffix(suffix)
                if isinstance(output, bytes):
                    path.write_bytes(output)
                else:
                    path.write_text(output or "", encoding="utf-8")
            raise
        except (OSError, subprocess.SubprocessError) as error:
            record["error"] = f"{type(error).__name__}: {error}"
            raise
        finally:
            record["seconds"] = round(time.monotonic() - start, 4)
        record["exit"] = result.returncode
        prefix.with_suffix(".stdout").write_text(result.stdout, encoding="utf-8")
        prefix.with_suffix(".stderr").write_text(result.stderr, encoding="utf-8")
        expected = 0 if success else 1
        if result.returncode != expected:
            raise AssertionError(f"{label}: exit {result.returncode}, expected {expected}\n"
                                 f"{result.stdout}\n{result.stderr}")
        if not success and not (result.stdout.strip() or result.stderr.strip()):
            raise AssertionError(f"{label}: refusal has no diagnostic")
        return result.stdout

    def case(self, label, action):
        try:
            action()
            self.checks.append({"name": label, "passed": True})
            print(f"PASS {label}", flush=True)
        except (AssertionError, ValueError, OSError, subprocess.SubprocessError) as error:
            self.checks.append({"name": label, "passed": False, "error": str(error)})
            print(f"FAIL {label}: {error}", flush=True)

    def export(self, label, source, symbol="main"):
        folder = self.directory / label
        folder.mkdir(exist_ok=True)
        original = folder / "source.mlir"
        original.write_text(source, encoding="utf-8")
        output = self.command(label + ":export",
                              [self.tools["compiler"], "protocol-structured", original, "--symbol=" + symbol])
        snapshot = json.loads(output)
        assert snapshot[:4] == ["zkc.structured-source/0", "original",
                                "sha256:" + digest(original), symbol], snapshot[:4]
        path = folder / "source.json"
        path.write_text(output, encoding="utf-8")
        self.command(label + ":check", [self.tools["lean"], "check", path])
        self.sources.append({"name": label, "source": str(original), "sha256": digest(original),
                             "snapshot": str(path), "snapshotSha256": digest(path)})
        return original, path, snapshot

    def compare(self, subject, label, values, expected):
        original, snapshot, data = subject
        request = snapshot.parent / (label + ".inputs.json")
        write_json(request, values)
        entry = definition(data, data[3])
        lean_request = snapshot.parent / (label + ".lean-inputs.json")
        write_json(lean_request, [typed_value(ty, value) for ty, value in zip(entry[4], values, strict=True)])
        native = json.loads(self.command(label + ":reference",
                            [self.tools["reference"], original, data[3], request]))
        formal = json.loads(self.command(label + ":lean",
                            [self.tools["lean"], "run", snapshot, lean_request]))
        assert native == expected and formal == typed_result(entry[5], expected), {
            "reference": native, "lean": formal, "expected": expected}

    def frontend(self, entry):
        source = Path(__file__).parent / "fixtures/accumulate.zkc"
        flags = ["--source-format=zkc", "--module=structured=" + str(source),
                 "--entry=structured::" + entry]
        text = self.command(entry + ":frontend", [self.tools["compiler"], "language-emit", *flags])
        interface = json.loads(self.command(entry + ":interface",
            [self.tools["compiler"], "language-interface", *flags]))
        subject = self.export("frontend-" + entry, text, interface["protocol"])
        write_json(subject[1].parent / "interface.json", interface)
        shutil.copy2(source, subject[1].parent / "source.zkc")
        return subject

    def refuse_snapshot(self, label, snapshot, code=None):
        path = self.directory / (label + ".json")
        write_json(path, snapshot)
        result = json.loads(self.command(label, [self.tools["lean"], "check", path], success=False))
        assert result["status"] == "refused", result
        if code is not None:
            assert result["code"] == code, result

    def refuse_native(self, label, source, code):
        path = self.directory / (label + ".mlir")
        path.write_text(source, encoding="utf-8")
        number = len(self.commands)
        self.command(label, [self.tools["compiler"], "protocol-structured", path, "--symbol=main"],
                     success=False)
        diagnostic = (self.directory / f"command-{number:04d}.stderr").read_text(encoding="utf-8")
        assert code in diagnostic, diagnostic

    def retained(self, subject, stem, module):
        _, _, data = subject
        fixtures = Path(__file__).parent / "fixtures"
        assert data == json.loads((fixtures / (stem + ".json")).read_text(encoding="utf-8"))
        generated = constructors.render(data, "ZkcExamples.Structured." + module + "Data")
        maintained = ROOT / "lean/ZkcExamples/Structured" / (module + "Data.lean")
        assert generated == maintained.read_text(encoding="utf-8"), "constructor data differs from actual export"

    def changed_body(self, subject):
        _, path, data = subject
        changed = copy.deepcopy(data)
        terminal = definition(changed, "step")[9][2]
        assert terminal == ["return", [2, 0]], terminal
        terminal[1] = [0, 2]
        candidate = path.parent / "copied-digest-changed-body.json"
        write_json(candidate, changed)
        self.command("changed-body:admit", [self.tools["lean"], "check", candidate])
        values = [["vector", FIELD, ["2"]], ["field", FIELD, "7"], ["field", FIELD, "11"]]
        request = path.parent / "copied-digest.inputs.json"
        write_json(request, values)
        result = json.loads(self.command("changed-body:run", [self.tools["lean"], "run", candidate, request]))
        assert result == typed_result(definition(data, data[3])[5], returned("2", "11")), result
        assert changed[2] == data[2] and changed != data

    def native(self, subject, label, values, expected):
        for finite_bulk in (False, True):
            self.native_mode(subject, label, values, expected, finite_bulk)

    def native_mode(self, subject, label, values, expected, finite_bulk):
        if "runtime" not in self.tools:
            return
        original, snapshot, data = subject
        mode = "bulk" if finite_bulk else "loops"
        label += "-" + mode
        bundle = snapshot.parent / ("bundle-" + mode + ".json")
        if not bundle.exists():
            bundle.write_text(self.command(label + ":bundle",
                [self.tools["compiler"], "protocol-bundle", original, "--entry=" + data[3],
                 "--no-simplify"] + ([] if finite_bulk else ["--no-finite-bulk"])), encoding="utf-8")
        candidate = json.loads(json.loads(bundle.read_text(encoding="utf-8"))["candidate"])
        ports = candidate[3][0][4]
        entry = definition(data, data[3])
        roles = entry[6][1]
        if len(roles) != 1:
            raise ValueError("closed native comparison requires exactly one participant")
        encoded = [wire(ty, value) for ty, value in zip(entry[4], values, strict=True)]
        request = ["zkc.bundle-inputs/0", "structured-source",
                   [[roles[0], [[str(i), port[1], ["wire", value]]
                               for i, (port, value) in enumerate(zip(ports, encoded, strict=True))], []]], []]
        path = snapshot.parent / (label + ".native-inputs.json")
        write_json(path, request)
        report = json.loads(self.command(label + ":runtime",
                            [self.tools["runtime"], "--json", "run-bundle", bundle, digest(bundle), path],
                            success=expected[0] == "returned"))
        assert report.get("format") == "zkc.bundle-result/0", report
        endpoint = report["roles"][0]
        assert endpoint["active_frames"] == endpoint["live_resource_units"] == 0, report
        if expected[0] == "returned":
            assert report["outcome"] == ["completed"], report
            outputs = [wire(ty, value) for ty, value in zip(entry[5], expected[1], strict=True)]
            assert [item[2] for item in endpoint["outputs"]] == outputs, report
        else:
            assert report["outcome"] != ["completed"], report
            assert endpoint["after"][0] == "stopped", report
            assert endpoint["after"][1]["cause"] == ["explicit", {
                "omitted_bytes": 0, "text": expected[1]}], report

    def verify_sources(self):
        """Finish source evidence before selecting a terminal report status."""
        if "before" in self.archives:
            if getattr(self.args, "write_fixtures", False):
                self.archives["after"] = self.capture_sources("after")
            else:
                self.checks.append(check_sources(ROOT, self.archives["before"],
                                                 self.source_inventory()))

    def finish(self, status=None):
        if not self.checks:
            self.checks.append({"name": "suite", "passed": False, "error": "no checks executed"})
        try:
            self.verify_sources()
        except BaseException as error:
            failure = self.failure("source-stability", error)
            status = "interrupted" if "interrupted" in (status, failure) else "failed"
        failures = sum(not check["passed"] for check in self.checks)
        if status != "interrupted":
            status = "failed" if failures or status == "failed" else self.success_status()
        try:
            self.publish(status)
        except BaseException as error:
            failure = self.failure("report-publication", error)
            status = "interrupted" if "interrupted" in (status, failure) else "failed"
            # Attempt both destinations again with the failure recorded. A
            # permanently unwritable destination cannot be promised a report.
            try:
                self.publish(status)
            except BaseException as error:
                print(f"could not publish terminal report: {error}", file=sys.stderr)
        failures = sum(not check["passed"] for check in self.checks)
        print(f"{len(self.checks)} checks, {failures} failures; {self.args.report}")
        return int(status not in ("pass", "native-only"))


def wire(ty, value):
    if ty == ["bool"]:
        tag, payload = 5, bytes([value])
    elif ty == ["index"]:
        tag, payload = 31, int(value).to_bytes(8, "little")
    elif ty == ["field", FIELD]:
        tag, payload = 1, int(value).to_bytes(32, "little")
    elif ty == ["vector", FIELD]:
        tag = 66
        payload = len(value).to_bytes(4, "little") + b"".join(int(x).to_bytes(32, "little") for x in value)
    else:
        raise ValueError(f"unsupported wire type {ty}")
    return (b"ZKCV" + bytes([0, tag]) + payload).hex()


def provenance_cases(suite, fixtures):
    forwarded_text = (fixtures / "forwarded-bounds.mlir").read_text(encoding="utf-8")
    forwarded = suite.export("forwarded-bounds", forwarded_text)
    mixed_text = forwarded_text.replace(
        "func.func private @permute(%xs: !V, %ys: !V, %i: ui64) -> (!V, ui64, !V, !V)",
        "func.func private @permute(%xs: !V, %ys: !V, %i: ui64) -> (!F, !V, ui64, !F, !V, !V)").replace(
        "      func.return %ys, %i, %xs, %xs : !V, ui64, !V, !V",
        '      %one = "algebra.constant"() {value="1"} : () -> !F\n'
        '      %fresh = algebra.field_add %one, %one : (!F, !F) -> !F\n'
        '      func.return %fresh, %ys, %i, %fresh, %xs, %xs : !F, !V, ui64, !F, !V, !V').replace(
        "%p:4 = func.call @permute", "%p:6 = func.call @permute").replace(
        "-> (!V, ui64, !V, !V)\n      func.return %p#3, %p#1",
        "-> (!F, !V, ui64, !F, !V, !V)\n      func.return %p#5, %p#2")
    mixed = suite.export("mixed-result-identities", mixed_text)
    direct_text = forwarded_text.replace(
        "func.call @read(%forward#0, %forward#1)",
        '"data.bounded_at"(%forward#0, %forward#1)')
    direct = suite.export("forwarded-read", direct_text)
    aliased_text = (fixtures / "aliased-indices.mlir").read_text(encoding="utf-8")
    aliased = suite.export("aliased-indices", aliased_text)
    capture_text = aliased_text.replace(
        "^entry(%xs: !V, %ys: !V):", "^entry(%xs: !V):").replace(
        "function_type = (!V, !V) -> !data.domain<ui64>",
        "function_type = (!V) -> !data.domain<ui64>").replace(
        '"algebra.finite_fold"(%xs, %xs, %seed)',
        '"algebra.finite_fold"(%xs, %seed, %xs)').replace(
        ": (!V, !V, !F) -> !F\n      \"protocol.return\"",
        ": (!V, !F, !V) -> !F\n      \"protocol.return\"")
    captured = suite.export("aliased-capture", capture_text)
    returned_alias_text = aliased_text.replace("    func.func private @read(",
        "    func.func private @identity(%xs: !V) -> !V { func.return %xs : !V }\n"
        "    func.func private @read(").replace(
        '      %r = "algebra.finite_fold"(%xs, %xs, %seed)',
        '      %alias = func.call @identity(%xs) : (!V) -> !V\n'
        '      %r = "algebra.finite_fold"(%xs, %alias, %seed)')
    returned_alias = suite.export("aliased-helper-result", returned_alias_text)
    for label, subject in (("forwarded", forwarded), ("mixed", mixed), ("direct", direct),
                           ("aliased", aliased), ("captured", captured),
                           ("returned-alias", returned_alias)):
        for items in ([], [2, 3], [MODULUS - 1, 2, 2**180]):
            values = [fields(items), [], "7"]
            expected = returned(str((7 + sum(items)) % MODULUS))
            name = f"{label}-{len(items)}"
            suite.case(name, lambda s=subject, n=name, v=values, e=expected: suite.compare(s, n, v, e))
            if "runtime" in suite.tools:
                suite.case(name + "-runner", lambda s=subject, n=name, v=values, e=expected:
                           suite.native(s, n, v, e))
    bad = copy.deepcopy(forwarded[2])
    definition(bad, "forward")[9][2][1][0] = 0
    suite.case("refuse-forwarded-unrelated-result", lambda: suite.refuse_snapshot(
        "forwarded-unrelated-result", bad, "structured-call-premise"))
    suite.case("native-refuse-forwarded-unrelated-result", lambda: suite.refuse_native(
        "native-forwarded-unrelated-result",
        forwarded_text.replace("func.return %p#3, %p#1", "func.return %p#0, %p#1"),
        "finite-bound"))
    distinct = copy.deepcopy(aliased[2])
    definition(distinct, "main")[9][1][0][1][1] = 1
    suite.case("refuse-distinct-domain-actual", lambda: suite.refuse_snapshot(
        "distinct-domain-actual", distinct, "structured-fold-premise"))
    suite.case("native-refuse-distinct-domain-actual", lambda: suite.refuse_native(
        "native-distinct-domain-actual",
        aliased_text.replace('"algebra.finite_fold"(%xs, %xs, %seed)',
                             '"algebra.finite_fold"(%xs, %ys, %seed)'), "finite-bound"))


def boundary_cases(suite, unit_text):
    def simple(helpers="", body="", result="%flag"):
        return '''module { "protocol.module"() ({
''' + helpers + '''
"protocol.func"() ({ ^entry(%flag:i1):
''' + body + '\n"protocol.return"(' + result + ''') : (i1)->()
}) {sym_name="main",function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }'''

    def instruction_boundary():
        body = '\n'.join(f'%x{i} = arith.xori %flag,%flag : i1' for i in range(4096))
        subject = suite.export('maximum-instructions', simple(body=body))
        suite.compare(subject, 'maximum-instructions', [True], returned(True))
        suite.refuse_native('excess-instructions', simple(body=body + '\n%x4096 = arith.xori %flag,%flag : i1'),
                            'structured-source-limit')
    suite.case('exact-instruction-limit-has-independent-reference', instruction_boundary)

    def finite_instruction_boundary():
        def source(count):
            body = '\n'.join(f'%x{i} = arith.xori %flag,%flag : i1' for i in range(count))
            helper = 'func.func private @padding(%flag:i1) -> i1 {\n' + body + '\nreturn %flag : i1\n}'
            return unit_text.replace(' local.func private @step', helper + '\n local.func private @step', 1)
        # The fixture contributes one finite declaration and two call sites.
        subject = suite.export('maximum-finite-instructions', source(4093))
        suite.compare(subject, 'maximum-finite-instructions', [[], False], returned(False))
        excessive = source(4094)
        suite.refuse_native('excess-finite-instructions', excessive, 'structured-source-limit')
        original = suite.directory / 'excess-finite-instructions.mlir'
        request = subject[1].parent / 'maximum-finite-instructions.inputs.json'
        number = len(suite.commands)
        suite.command('reference-finite-instruction-limit',
                      [suite.tools['reference'], original, 'main', request], success=False)
        assert 'structured-reference-capacity' in (
            suite.directory / f'command-{number:04d}.stderr').read_text(encoding="utf-8")
    suite.case('finite-declaration-counts-domain-and-terminators-do-not', finite_instruction_boundary)

    def file_boundary():
        inputs = ','.join(f'%a{i}:i1' for i in range(512))
        outputs = ','.join(['i1'] * 512)
        values = ','.join(f'%a{i}' for i in range(512))
        names = [f'h{i}' for i in range(93)]
        def source():
            return simple('\n'.join(f'func.func private @{name}({inputs}) -> ({outputs}) '
                                    f'{{ return {values} : {outputs} }}' for name in names))
        baseline = suite.export('file-size-baseline', source())
        padding = 1024 * 1024 - len(baseline[1].read_bytes())
        assert 0 <= padding <= sum(512 - len(name) for name in names)
        for i, name in enumerate(names):
            size = min(padding, 512 - len(name))
            names[i] += 'x' * size
            padding -= size
        exact = suite.export('maximum-file-bytes', source())
        assert len(exact[1].read_bytes()) == 1024 * 1024
        suite.compare(exact, 'maximum-file-bytes', [True], returned(True))
        names[-1] += 'y'
        assert len(names[-1]) <= 512
        suite.refuse_native('excess-file-bytes', source(), 'structured-source-limit')
    suite.case('exact-file-limit-is-readable-in-lean', file_boundary)

    for name in ['증명_α_🙂', 'line\nfeed']:
        # MLIR byte escapes are independent of JSON and Lean escaping.
        symbol = '@"' + ''.join(f'\\{byte:02X}' for byte in name.encode()) + '"'
        def renamed(name=name, symbol=symbol):
            subject = suite.export('unicode-' + str(len(name)), simple(
                f'func.func private {symbol}(%x:i1) -> i1 {{ return %x : i1 }}',
                f'%r = func.call {symbol}(%flag) : (i1)->i1', '%r'))
            assert definition(subject[2], name)[1] == name
            suite.compare(subject, 'unicode-identity', [True], returned(True))
            rendered = constructors.render(subject[2], 'UnicodeData')
            (subject[1].parent / 'Data.lean').write_text(rendered, encoding="utf-8")
        suite.case('native-unicode-helper-' + str(len(name)), renamed)


def installed_rows_cases(suite):
    """Every installed field, group and random service exports native rows that
    Lean decodes and finds consistent. Lean then refuses them only because its
    environment does not list them, or does not admit the sort instance."""
    def unit(declarations="", inputs=""):
        return ('''module { "protocol.module"() ({
''' + declarations + '''
"protocol.func"() ({ ^entry(%flag:i1''' + (",%service:" + inputs if inputs else "") + '''):
"protocol.return"(%flag) : (i1)->()
}) {sym_name="main",function_type=(i1''' + ("," + inputs if inputs else "") + ''')->i1,roles=["P"],input_roles=[["P"]'''
                + (',["P"]' if inputs else "") + '''],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }''')

    def dead(kind, identity):
        value = f'!algebra.{kind}<"{identity}">'
        return unit(f"func.func private @dead(%x:{value}) -> {value} {{ return %x : {value} }}")

    unknown = "structured-catalogue-unknown"
    subjects = [(identity, dead("field", identity), unknown) for identity in [
        "ristretto255.scalar", "bn254.fr", "koala-bear", "koala-bear.ext8-binomial3",
        "koala-bear.ext4-binomial3", "gf2-64.pentanomial-4-3-1",
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1"]]
    subjects += [(identity, dead("group", identity), unknown) for identity in [
        "bn254.g1", "bn254.g2", "bn254.gt", "ristretto255.group", "edwards25519.prime"]]
    # Rows the environment lists, at sort instances it does not admit.
    subjects += [(identity, dead("group", identity), "structured-type-unadmitted")
                 for identity in ["bls12-381.g2", "bls12-381.gt"]]
    subjects += [(contract, unit(inputs=f'!protocol.service_ref<"{contract}">'), unknown) for contract in [
        "random.bn254.fr/0", "random.ristretto255.scalar/0", "random.koala-bear.ext8-binomial3/0"]]
    for name, source, code in subjects:
        label = "installed-rows-" + name.replace("/", "-")
        def refused(label=label, source=source, code=code):
            folder = suite.directory / label
            folder.mkdir(exist_ok=True)
            original = folder / "source.mlir"
            original.write_text(source, encoding="utf-8")
            snapshot = json.loads(suite.command(label + ":export", [
                suite.tools["compiler"], "protocol-structured", original, "--symbol=main"]))
            assert snapshot[9][0] or snapshot[9][1], snapshot[9]
            suite.refuse_snapshot(label, snapshot, code)
        suite.case(label, refused)


def run_cases(suite):
    finite = ROOT / "compiler/test/fixtures/finite"
    total_text = (finite / "total-state.mlir").read_text(encoding="utf-8")
    unit_text = (finite / "unit-state.mlir").read_text(encoding="utf-8")
    total = suite.export("total-state", total_text)
    unit = suite.export("unit-state", unit_text)
    suite.case("retained-total-source-export-constructors", lambda: suite.retained(total, "total-state", "TotalState"))
    suite.case("retained-unit-source-export-constructors", lambda: suite.retained(unit, "unit-state", "UnitState"))
    suite.case("copied-digest-does-not-establish-correspondence", lambda: suite.changed_body(total))
    for items in ([], [2], [2, 3], [2, 3, 5], [MODULUS - 1, 0, 2**180]):
        a, b = 7, 11
        for value in items:
            a, b = b, value
        values, expected = [fields(items), "7", "11"], returned(str(a), str(b))
        label = f"total-{len(items)}-{items[:1]}"
        suite.case(label, lambda v=values, e=expected, n=label: suite.compare(total, n, v, e))
        if "runtime" in suite.tools:
            suite.case(label + "-runner", lambda v=values, e=expected, n=label: suite.native(total, n, v, e))
    for items in ([], [2], [2, 3]):
        for enabled in (False, True):
            expected = ["stopped", "abort"] if enabled and items else returned(enabled)
            values, label = [fields(items), enabled], f"unit-{len(items)}-{enabled}"
            suite.case(label, lambda v=values, e=expected, n=label: suite.compare(unit, n, v, e))
            if "runtime" in suite.tools:
                suite.case(label + "-runner", lambda v=values, e=expected, n=label: suite.native(unit, n, v, e))

    reversed_text = total_text.replace("func.return %b,%v", "func.return %v,%b")
    assert reversed_text != total_text
    reversed_subject = suite.export("reversed-results", reversed_text)
    suite.case("same-typed-result-order-changes-meaning", lambda: suite.compare(
        reversed_subject, "reversed", [["2"], "7", "11"], returned("2", "11")))
    for stop in ("abort", "reject", "exhausted", "incomplete", "refused"):
        changed = suite.export("stop-" + stop, unit_text.replace('reason="abort"', f'reason="{stop}"'))
        suite.case("stop-class-" + stop, lambda s=changed, reason=stop: suite.compare(
            s, "active", [["2"], True], ["stopped", reason]))

    shared = suite.export("shared-math", (Path(__file__).parent / "fixtures/shared-math.mlir").read_text(encoding="utf-8"))
    assert sum(item[1] == "pair" for item in shared[2][7]) == 1
    structured = ROOT / "compiler/test/fixtures/structured-source"
    indexed = suite.export("indexed-helper", (structured / "indexed-helper.mlir").read_text(encoding="utf-8"))
    for entry in ("Run", "IndexedRun"):
        compiled = suite.frontend(entry)
        for items in ([], [2], [MODULUS - 1, 2, 2**180]):
            values = [fields(items), "7"]
            expected = returned(str((7 + sum(items)) % MODULUS))
            name = f"frontend-{entry}-{len(items)}"
            suite.case(name, lambda s=compiled, n=name, v=values, e=expected: suite.compare(s, n, v, e))
            if "runtime" in suite.tools:
                suite.case(name + "-runner", lambda s=compiled, n=name, v=values, e=expected: suite.native(s, n, v, e))
    provenance_cases(suite, structured)
    installed_rows_cases(suite)
    boundary_cases(suite, unit_text)
    guarded = suite.export("guarded", (structured / "guards.mlir").read_text(encoding="utf-8"))
    for enabled in (False, True):
        expected = returned(True) if enabled else ["stopped", "reject"]
        name = "guard-" + str(enabled)
        suite.case(name, lambda n=name, v=enabled, e=expected: suite.compare(guarded, n, [v], e))
        if "runtime" in suite.tools:
            suite.case(name + "-runner", lambda n=name, v=enabled, e=expected: suite.native(guarded, n, [v], e))
    dag = suite.export("shared-local-dag", (structured / "shared-local-dag.mlir").read_text(encoding="utf-8"))
    def shared_dag_capacity():
        suite.command("shared-dag:check", [suite.tools["lean"], "check", dag[1]])
        assert len(dag[2][7]) == 23, len(dag[2][7])
        request = dag[1].parent / "inputs.json"
        write_json(request, [["bool", True]])
        result = json.loads(suite.command("shared-dag:capacity",
            [suite.tools["lean"], "run", dag[1], request], success=False))
        assert result == {"code": "structured-bounds-analysis-limit", "status": "refused"}, result
    suite.case("shared-helper-admission-is-separate-from-analysis-capacity", shared_dag_capacity)
    nested = suite.export("nested-control", (structured / "nested-controls.mlir").read_text(encoding="utf-8"))
    loops = suite.export("loop-control", (structured / "loops-and-captures.mlir").read_text(encoding="utf-8"), "entry")
    completed = suite.export("conditional-completion",
        (Path(__file__).parent / "fixtures/conditional-completion.mlir").read_text(encoding="utf-8"))
    for lower, upper in ((0, 0), (3, 1), (0, 1), (0, 2), (0, 3)):
        values = [str(lower), str(upper), "7", "11"]
        expected = returned("11", "7") if lower < upper else returned("7", "11")
        name = f"completion-{lower}-{upper}"
        suite.case(name, lambda n=name, v=values, e=expected: suite.compare(completed, n, v, e))
        if "runtime" in suite.tools:
            suite.case(name + "-runner", lambda n=name, v=values, e=expected: suite.native(completed, n, v, e))
    for items in ([], [2], [2, 3, 5]):
        for enabled in (False, True):
            a, b = 7, 11
            for value in items:
                if enabled:
                    a, b = b, value
            expected = returned(str(a), str(b)) if enabled else ["stopped", "abort"]
            suite.case(f"nested-{len(items)}-{enabled}", lambda xs=items, flag=enabled, e=expected:
                       suite.compare(nested, f"nested-{len(xs)}-{flag}",
                                     [fields(xs), "7", "11", flag], e))
            if "runtime" in suite.tools:
                suite.case(f"nested-{len(items)}-{enabled}-runner", lambda xs=items, flag=enabled, e=expected:
                           suite.native(nested, f"nested-{len(xs)}-{flag}",
                                        [fields(xs), "7", "11", flag], e))
    for lower, upper in ((0, 0), (2, 1), (0, 1), (1, 3), (2, 5)):
        for enabled in (False, True):
            a, b, c, d = 7, 11, 13, 17
            count = max(upper - lower, 0)
            for _ in range(count):
                first, second = (c, b) if enabled else (a, d)
                a, b = second, first
            if count and enabled:
                for _ in range(count):
                    a, b = b, a
            expected = ["stopped", "reject"] if count and not enabled else returned(str(b), str(c))
            values = ["7", "11", "13", "17", str(lower), str(upper), enabled]
            name = f"loops-{lower}-{upper}-{enabled}"
            suite.case(name, lambda n=name, v=values, e=expected: suite.compare(loops, n, v, e))
            if "runtime" in suite.tools:
                suite.case(name + "-runner", lambda n=name, v=values, e=expected: suite.native(loops, n, v, e))
    for i in range(suite.args.cases):
        a, b = suite.rng.randrange(MODULUS), suite.rng.randrange(MODULUS)
        first, second = (a + b) % MODULUS, (a - b) % MODULUS
        third, fourth = (second + first) % MODULUS, (second - first) % MODULUS
        expected = ["returned", fields([first, second, third, fourth, third * fourth % MODULUS])]
        suite.case(f"shared-actuals-{i}", lambda n=i, x=a, y=b, e=expected: suite.compare(
            shared, f"shared-{n}", fields([x, y]), e))
        if "runtime" in suite.tools and i < 8:
            suite.case(f"shared-actuals-{i}-runner", lambda n=i, x=a, y=b, e=expected: suite.native(
                shared, f"shared-{n}", fields([x, y]), e))
        xs = [suite.rng.randrange(MODULUS) for _ in range(i % 7)]
        ys = [suite.rng.randrange(MODULUS) for _ in range((i + 2) % 5)]
        expected = returned(str((a + sum(xs)) % MODULUS))
        suite.case(f"index-provenance-{i}", lambda n=i, x=xs, y=ys, seed=a, e=expected: suite.compare(
            indexed, f"indexed-{n}", [fields(x), fields(y), str(seed)], e))
        if "runtime" in suite.tools and i < 8:
            suite.case(f"index-provenance-{i}-runner", lambda n=i, x=xs, y=ys, seed=a, e=expected: suite.native(
                indexed, f"indexed-{n}", [fields(x), fields(y), str(seed)], e))

    malformed = []
    for index, replacement, label in [(0, "unknown/0", "format"), (1, "prepared", "stage")]:
        bad = copy.deepcopy(total[2]); bad[index] = replacement
        malformed.append((label, bad))
    bad = copy.deepcopy(unit[2]); definition(bad, "main")[6][2][0] = ["other"]
    malformed.append(("wrong-role", bad))
    bad = copy.deepcopy(total[2]); bad[4].append(copy.deepcopy(bad[4][0]))
    malformed.append(("duplicate-domain", bad))
    bad = copy.deepcopy(unit[2]); definition(bad, "work")[9][1][0][0][1] = "missing"
    malformed.append(("missing-helper", bad))
    bad = copy.deepcopy(total[2]); definition(bad, "step")[7] = []
    malformed.append(("missing-index-premise", bad))
    bad = copy.deepcopy(indexed[2]); definition(bad, "step")[9][1][0][1][0] = 3
    malformed.append(("same-typed-wrong-container-at-call", bad))
    bad = copy.deepcopy(total[2]); definition(bad, "step")[9][1][0][1][1] = 4096
    malformed.append(("out-of-scope-index", bad))
    bad = copy.deepcopy(unit[2]); definition(bad, "step")[9][2].append("ignored")
    malformed.append(("malformed-dormant-stop", bad))
    bad = copy.deepcopy(total[2]); definition(bad, "main")[9][1][0][0][0] = "unknown"
    malformed.append(("unknown-operation", bad))
    bad = copy.deepcopy(total[2]); bad.append("ignored")
    malformed.append(("extra-envelope-field", bad))
    bad = copy.deepcopy(total[2]); definition(bad, "step")[7][0][3] = 1
    malformed.append(("wrong-bound-axis", bad))
    bad = copy.deepcopy(unit[2]); definition(bad, "work")[9][1][0][0][1] = "work"
    malformed.append(("helper-cycle", bad))
    bad = copy.deepcopy(total[2]); definition(bad, "step")[9] = ["block", [], ["stop", "abort", "math_stop"]]
    malformed.append(("math-stopping-body", bad))
    bad = copy.deepcopy(total[2]); bad[3] = "x" * 513
    malformed.append(("overlong-identity", bad))
    bad = copy.deepcopy(loops[2]); definition(bad, "control")[9][1][0][3][0][2][2][1][-3:-1] = [6, 5]
    malformed.append(("same-typed-capture-swap", bad))
    for label, bad in malformed:
        suite.case("refuse-" + label, lambda n=label, b=bad: suite.refuse_snapshot(n, b))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--reference", type=Path, default=ROOT / "build/compiler/test/zkc-structured_reference-test")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--runtime", type=Path, help="optional production zkc executable")
    parser.add_argument("--cases", type=int, default=32)
    parser.add_argument("--seed", type=int, default=73191)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    suite = Suite(args)
    return suite.run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
