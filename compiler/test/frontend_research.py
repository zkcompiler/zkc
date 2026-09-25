"""Durable frontend bundles and API measurement contracts; no timing thresholds."""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from commands import Commands
from tools import ROOT, compiler, optimizer, records, source_bench


SCRIPT = ROOT / "bench/protocol_experiment.py"
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("experiment", SCRIPT)
experiment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(experiment)


EVIDENCE = records()
commands = Commands(EVIDENCE)


class Research(unittest.TestCase):
    def setUp(self):
        # Each case works in a directory of its own, and the name carries a
        # space on purpose: a tool that split its arguments would fail here and
        # nowhere else.
        self.root = EVIDENCE / f"{self.id().rsplit('.', 1)[-1]} case"
        self.root.mkdir(parents=True)
        self.source = self.root / "source $(touch injected).pir"
        self.source.write_bytes(experiment.synthetic(3))

    def command(self, output, *extra, source=None, using=None):
        return [sys.executable, str(SCRIPT), "run", str(source or self.source),
                "--output", str(output), "--compiler", str(using or compiler),
                "--bench", str(source_bench), "--opt", str(optimizer),
                "--iterations", "2", "--warmup", "0", *map(str, extra)]

    def run_bundle(self, name="bundle with spaces", *extra, code=0, source=None, using=None):
        output = self.root / name
        proc = commands.attempt(self.command(output, *extra, source=source, using=using),
                                text=False, timeout=60)
        self.assertEqual(proc.returncode, code, (proc.stdout, proc.stderr))
        manifest = json.loads((output / "manifest.json").read_bytes())
        # Every referenced artifact must still exist and match the recorded bytes.
        for path, record in manifest["artifacts"].items():
            self.assertEqual(Path(path).name, path)
            raw = (output / path).read_bytes()
            self.assertEqual(record, {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)})
        self.assertTrue((output / "original.bin").exists())
        return output, manifest, {s["name"]: s for s in manifest["stages"]}

    def wrapper(self, body):
        wrapper = self.root / "compiler wrapper"
        wrapper.write_text(f"#!{sys.executable}\nimport os, sys, time\n" + body +
                           f"\nos.execv({str(compiler)!r}, [{str(compiler)!r}, *sys.argv[1:]])\n")
        wrapper.chmod(0o700)
        return wrapper

    def test_success_and_spaces(self):
        output, manifest, stages = self.run_bundle()
        self.assertEqual(manifest["status"], "success")
        for name in ("syntax", "admission", "inspection", "common", "logical", "project", "physical", "participants", "benchmark"):
            self.assertEqual(stages[name]["status"], "success")
        self.assertEqual((output / "original.bin").read_bytes(), self.source.read_bytes())
        self.assertFalse((output / "injected").exists())
        self.assertIn("module", (output / "source.pir").read_text())
        report = manifest["measurement"]
        # The build requires major 23 and only warns on the patch release,
        # which compiler/CMakeLists.txt says is "reported, not required", so
        # pinning the patch here would fail on the next distribution bump.
        self.assertRegex(report["versions"]["llvm_mlir"], r"^23\.")
        counts = report["counts"]
        self.assertEqual(counts["configurations"], 4)
        self.assertEqual(counts["demanded_configurations"], 3)
        self.assertEqual(counts["specializations"], 1)
        self.assertEqual(counts["closed_functions"], 1)
        for stage in report["stages"]:
            self.assertEqual(stage["status"], "success")
            self.assertEqual(len(stage["samples_us"]), 2)
            # Verify aggregation, never a wall-clock performance assertion.
            self.assertEqual(stage["min_us"], min(stage["samples_us"]))
        physical = json.loads((output / "participants.stdout").read_bytes())
        self.assertEqual(physical[0:1], ["zkc.participants/1"])
        self.assertEqual(physical[2], "physical")

    def test_portable_source_and_no_generic_elaboration(self):
        # Hand-curated common carrier, without a shared text parser as oracle.
        portable = ["zkc.protocol/1", [], [], [
            ["protocol", "Empty", ["Alice"], [], [], [], [], [["return", []]]]],
            [["instance", "empty", "Empty", [], [], [["Alice", "Alice"]]]],
            [["entry", "main", "empty"]]]
        source = self.root / "portable source.json"
        source.write_text(json.dumps(portable))
        output, manifest, stages = self.run_bundle(source=source)
        syntax = json.loads((output / "syntax.stdout").read_bytes())
        self.assertEqual(syntax["kind"], "syntax-inspection")
        self.assertEqual(syntax["format"], "common-source-json")
        self.assertEqual(syntax["content"], portable)
        self.assertEqual(json.loads((output / "admission.stdout").read_bytes()), portable)
        elaboration = next(s for s in manifest["measurement"]["stages"] if s["name"] == "elaborate")
        self.assertEqual(elaboration["status"], "not_applicable")
        self.assertEqual(elaboration["samples_us"], [])
        self.assertEqual(stages["format"]["status"], "success")
        # Portable input now retains original JSON array spans as well as text.
        self.assertGreater(manifest["measurement"]["counts"]["spans"], 0)

    def test_syntax_failure(self):
        self.source.write_bytes(b"module {\n  fn")
        output, manifest, stages = self.run_bundle(code=1)
        self.assertEqual(stages["syntax"]["status"], "refused")
        self.assertEqual(stages["admission"]["status"], "skipped")
        self.assertEqual(stages["common"]["status"], "skipped")
        self.assertEqual(manifest["measurement"]["stages"][0]["status"], "refused")
        self.assertEqual((output / "source.pir").read_bytes(), self.source.read_bytes())
        self.assertTrue((output / "syntax.stderr").read_bytes())

    def test_semantic_refusal_retains_syntax(self):
        self.source.write_bytes(self.source.read_bytes().replace(b"Choice0(x)", b"Missing(x)"))
        output, manifest, stages = self.run_bundle(code=1)
        self.assertEqual(stages["syntax"]["status"], "success")
        self.assertEqual(stages["format"]["status"], "success")
        self.assertEqual(stages["admission"]["status"], "refused")
        self.assertEqual(stages["inspection"]["status"], "refused")
        self.assertEqual(stages["common"]["status"], "skipped")
        self.assertIn(b"source-name-unresolved", (output / "admission.stderr").read_bytes())
        api = {s["name"]: s for s in manifest["measurement"]["stages"]}
        self.assertEqual(api["syntax"]["status"], "success")
        self.assertEqual(api["source"]["status"], "refused")
        self.assertEqual(api["check"]["status"], "skipped")
        self.assertEqual(api["import"]["status"], "skipped")

    def test_existing_data_and_symlinks_refused(self):
        existing = self.root / "existing"
        existing.mkdir()
        keep = existing / "manifest.json"
        keep.write_bytes(b"unrelated data")
        link = self.root / "symlink"
        link.symlink_to(existing, target_is_directory=True)
        dangling = self.root / "dangling"
        dangling.symlink_to(self.root / "missing")
        for output in (existing, link, dangling):
            proc = commands.attempt(self.command(output), text=False, timeout=10)
            self.assertEqual(proc.returncode, 2)
            self.assertEqual(keep.read_bytes(), b"unrelated data")
        self.assertEqual(list(existing.iterdir()), [keep])

    def test_artifact_names_cannot_escape_bundle(self):
        bundle = experiment.Bundle(self.root / "bounded names", [])
        for name in ("../escaped", str(self.root / "absolute"), ".", "nested/file"):
            with self.assertRaises(ValueError):
                bundle.write(name, b"must not escape")
        self.assertFalse((self.root / "escaped").exists())
        self.assertFalse((self.root / "absolute").exists())

    def test_suite_retains_every_run(self):
        output = self.root / "suite"
        proc = commands.attempt([sys.executable, SCRIPT, "suite", "--output", output,
                                 "--compiler", os.path.relpath(compiler),
                                 "--bench", os.path.relpath(source_bench),
                                 "--opt", os.path.relpath(optimizer),
                                 "--iterations", "1", "--warmup", "0",
                                 "--repeats", "1", "--scales", "1"],
                                text=False, timeout=60)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        results = json.loads((output / "results.json").read_bytes())
        self.assertEqual([c["case"] for c in results["cases"]],
                         ["generic-dleq", "generic-committed-two-factor", "sharing-1"])
        for case in results["cases"]:
            run = case["runs"][0]
            self.assertEqual(run["status"], "success")
            self.assertEqual(case["api"]["syntax"]["iterations"], 1)
            manifest = output / run["manifest"]
            self.assertEqual(hashlib.sha256(manifest.read_bytes()).hexdigest(), run["manifest_sha256"])
            self.assertTrue((manifest.parent / "source.pir").exists())

    def test_seed_reproduction_and_preserved_selectors(self):
        # Supplied context may refer to any existing label; no label is removed.
        config = self.root / "config with spaces.json"
        config.write_text('{"site": "call0"}')
        a, ma, _ = self.run_bundle("first", "--seed", "123", "--presentation", "--config", config)
        b, mb, _ = self.run_bundle("second", "--seed", "123", "--presentation", "--config", config)
        c, _, _ = self.run_bundle("third", "--seed", "456", "--presentation")
        self.assertEqual((a / "source.pir").read_bytes(), (b / "source.pir").read_bytes())
        self.assertNotEqual((a / "source.pir").read_bytes(), (c / "source.pir").read_bytes())
        self.assertEqual(ma["source"]["sha256"], mb["source"]["sha256"])
        self.assertIn(b"[call0]", (a / "source.pir").read_bytes())
        self.assertEqual((a / "config.bin").read_bytes(), config.read_bytes())
        # Syntax inspection now retains real spelling offsets. Presentation
        # changes may move those offsets, but not the elaborated common source.
        self.assertEqual((a / "admission.stdout").read_bytes(), (c / "admission.stdout").read_bytes())

    def test_original_changed_after_capture(self):
        original = self.source.read_bytes()
        real_snapshot = experiment.snapshot
        reads = []

        def change(path):
            captured = real_snapshot(path)
            reads.append(Path(path))
            Path(path).write_bytes(b"module { broken after capture")
            return captured

        output = self.root / "one snapshot"
        with patch.object(experiment, "snapshot", side_effect=change):
            code = experiment.main(self.command(output)[2:])
        self.assertEqual(code, 0)
        self.assertEqual(reads, [self.source])
        self.assertEqual((output / "original.bin").read_bytes(), original)
        self.assertEqual((output / "source.pir").read_bytes(), original)
        self.assertNotEqual(self.source.read_bytes(), original)

    def test_command_exit_and_partial_evidence(self):
        wrapper = self.wrapper("if len(sys.argv) > 1 and sys.argv[1] == 'protocol-physical-ir':\n"
                               "    print('partial physical output', flush=True)\n"
                               "    print('controlled failure', file=sys.stderr, flush=True)\n"
                               "    sys.exit(17)\n")
        output, _, stages = self.run_bundle(using=wrapper, code=1)
        self.assertEqual(stages["physical"]["exit_code"], 17)
        self.assertEqual(stages["physical"]["status"], "refused")
        self.assertEqual(stages["participants"]["status"], "success")
        self.assertIn(b"partial physical output", (output / "physical.stdout").read_bytes())
        self.assertIn(b"controlled failure", (output / "physical.stderr").read_bytes())

    def test_timeout_preserves_output(self):
        wrapper = self.wrapper("if len(sys.argv) > 1 and sys.argv[1] == 'protocol-physical-ir':\n"
                               "    print('before timeout', flush=True)\n"
                               "    time.sleep(10)\n")
        output, _, stages = self.run_bundle("timeout", "--timeout", "1", using=wrapper, code=1)
        self.assertEqual(stages["physical"]["status"], "timeout")
        self.assertIn(b"before timeout", (output / "physical.stdout").read_bytes())
        self.assertEqual(stages["participants"]["status"], "success")

    def test_missing_requested_tools(self):
        for option, stage in (("--lean", "lean-source"), ("--bench", "benchmark"), ("--opt", "project")):
            _, manifest, stages = self.run_bundle(stage, option, self.root / "not installed", code=1)
            self.assertEqual(stages[stage]["status"], "unavailable")
            self.assertEqual(manifest["status"], "incomplete")
            self.assertEqual(stages["participants"]["status"], "success")

    def test_lean_zero_exit_is_not_a_check_claim(self):
        fake = self.root / "fake lean"
        fake.write_text(f"#!{sys.executable}\nprint('not a checking result')\n")
        fake.chmod(0o700)
        _, _, stages = self.run_bundle("bad checker", "--lean", fake, code=1)
        self.assertEqual(stages["lean-source"]["status"], "failed")
        self.assertEqual(stages["lean-participants"]["status"], "failed")
        self.assertEqual(stages["lean-source"]["exit_code"], 0)

    def test_lean_pending_is_not_execution_success(self):
        fake = self.root / "controlled checker"
        fake.write_text(f"#!{sys.executable}\nimport json, sys\n" + """
if sys.argv[1] == '--generic-declarations':
    print(json.dumps(['checked', 'generic-local-formation', 'not-whole-source-admission']))
elif sys.argv[1] == '--check-generic':
    print(json.dumps(['checked', 'generic-structural-correspondence', [], [], 'no-elaboration-adequacy-proof']))
elif sys.argv[1] == '--generic-reference':
    print(json.dumps(['zkc.reference-observation/1', 'main', 'joint', ['pending', 'reply-missing'], [], ['scope', 'test-double']]))
else:
    sys.exit(1)
""")
        fake.chmod(0o700)
        inputs = self.root / "inputs"
        inputs.write_bytes(b"[]")
        _, _, stages = self.run_bundle("pending", "--lean", fake, "--lean-reference", "--inputs", inputs, code=1)
        self.assertEqual(stages["lean-source"]["status"], "success")
        self.assertEqual(stages["lean-reference"]["exit_code"], 0)
        self.assertEqual(stages["lean-reference"]["status"], "refused")
        self.assertEqual(stages["lean-reference"]["outcome"], ["pending", "reply-missing"])

    def test_source_byte_limit_is_an_explicit_partial_capture(self):
        self.source.write_bytes(b"// too large\n" + b" " * experiment.LIMIT)
        output, manifest, stages = self.run_bundle("large", code=1)
        self.assertEqual(stages["runner"]["status"], "refused")
        self.assertFalse(manifest["supplied"]["original"]["capture_complete"])
        self.assertEqual((output / "original.bin").stat().st_size, experiment.LIMIT + 1)
        self.assertTrue((output / "original.txt").read_text().startswith("// too large"))

    def test_supplied_inputs_descriptor_and_selections(self):
        for name, data in (("inputs", b"[]"), ("config", b"{}"), ("implementations", b"[]"),
                           ("descriptor", b"not a construction descriptor")):
            (self.root / name).write_bytes(data)
        output, _, stages = self.run_bundle("supplied", *[
            part for key in ("inputs", "config", "implementations", "descriptor")
            for part in ("--" + key, self.root / key)], code=1)
        self.assertEqual(stages["participants"]["status"], "success")
        self.assertEqual(stages["construction"]["status"], "refused")
        self.assertIn("--implementations=implementations.bin", stages["participants"]["argv"])
        self.assertEqual((output / "descriptor.bin").read_bytes(), (self.root / "descriptor").read_bytes())


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0]], verbosity=2)
