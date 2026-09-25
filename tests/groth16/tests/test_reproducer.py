"""Focused refusal tests for the maintained artifact/provenance boundary."""

import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE / "scripts"))
from common import check_files, sha256  # noqa: E402
from prepare_reference import prepare  # noqa: E402

spec = importlib.util.spec_from_file_location(
    "groth16_reproduce", PACKAGE / "reproduce.py"
)
reproduce = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reproduce)


class ReproducerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="groth16-test-")
        self.root = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def copy_evidence(self):
        shutil.copytree(PACKAGE / "evidence", self.root / "evidence")
        shutil.copy2(PACKAGE / "package-lock.json", self.root / "package-lock.json")

    def test_preserved_evidence_relocates(self):
        self.copy_evidence()
        reproduce.check_evidence(self.root)

    def test_changed_preserved_proof_refused(self):
        self.copy_evidence()
        path = self.root / "evidence/depth2/proof-r1-s2.json"
        path.write_text(path.read_text().replace('"groth16"', '"changed"'))
        with self.assertRaisesRegex(ValueError, "evidence hash mismatch"):
            reproduce.check_evidence(self.root)

    def test_changed_lock_refused(self):
        self.copy_evidence()
        with (self.root / "package-lock.json").open("a") as stream:
            stream.write("\n")
        with self.assertRaisesRegex(ValueError, "npm lock differs"):
            reproduce.check_evidence(self.root)

    def test_changed_artifact_refused_before_copy(self):
        path = self.root / "witness.wtns"
        path.write_bytes(b"original fixture witness")
        manifest = {path.name: {"sha256": sha256(path), "bytes": path.stat().st_size}}
        check_files(self.root, manifest)
        path.write_bytes(b"modified fixture witness")
        with self.assertRaisesRegex(ValueError, "Artifact hash mismatch"):
            check_files(self.root, manifest)

    def test_truncated_artifact_refused(self):
        path = self.root / "final.zkey"
        path.write_bytes(b"truncated")
        manifest = {path.name: {"sha256": sha256(path), "bytes": 100}}
        with self.assertRaisesRegex(ValueError, "Artifact length mismatch"):
            check_files(self.root, manifest)

    def test_modified_upstream_prover_refused(self):
        self.copy_evidence()
        upstream = self.root / "node_modules/snarkjs"
        (upstream / "src").mkdir(parents=True)
        (upstream / "package.json").write_text(json.dumps({"version": "0.7.5"}))
        (upstream / "src/groth16_prove.js").write_text("modified upstream prover")
        with self.assertRaisesRegex(ValueError, "Upstream source hash mismatch"):
            prepare(self.root)
        self.assertFalse((self.root / "reference/snarkjs-controlled").exists())

    def test_wrong_upstream_version_refused(self):
        self.copy_evidence()
        upstream = self.root / "node_modules/snarkjs"
        upstream.mkdir(parents=True)
        (upstream / "package.json").write_text(json.dumps({"version": "0.7.4"}))
        with self.assertRaisesRegex(ValueError, "Unexpected snarkjs version"):
            prepare(self.root)

    def test_source_directory_cannot_be_workdir(self):
        for path in (PACKAGE, PACKAGE.parent, PACKAGE / "scripts/output"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                reproduce.prepare_workdir(path)

    def test_nonempty_unmarked_workdir_refused(self):
        (self.root / "valuable.txt").write_text("preserve me")
        with self.assertRaisesRegex(ValueError, "nonempty, unmarked"):
            reproduce.prepare_workdir(self.root)
        self.assertEqual((self.root / "valuable.txt").read_text(), "preserve me")

    def test_wrong_workdir_marker_refused(self):
        (self.root / ".groth16-workdir.json").write_text('{"schema":"unrelated"}')
        with self.assertRaisesRegex(ValueError, "Unrecognized work-directory marker"):
            reproduce.prepare_workdir(self.root)

    def test_read_only_source_can_be_staged_twice(self):
        source = self.root / "readonly-source"
        work = self.root / "work"
        source.mkdir()
        work.mkdir()
        for name in ("scripts", "circuits", "evidence"):
            directory = source / name
            directory.mkdir()
            (directory / "fixture.txt").write_text("immutable source")
            (directory / "fixture.txt").chmod(0o444)
            directory.chmod(0o555)
        for name in ("package.json", "package-lock.json", "SOURCE_PINS.json"):
            (source / name).write_text("{}")
            (source / name).chmod(0o444)
        source.chmod(0o555)
        with patch.object(reproduce, "SOURCE", source):
            reproduce.stage_source(work)
            reproduce.stage_source(work)
        self.assertEqual((source / "scripts/fixture.txt").stat().st_mode & 0o777, 0o444)
        self.assertEqual((source / "scripts").stat().st_mode & 0o777, 0o555)
        self.assertEqual((work / "scripts/fixture.txt").read_text(), "immutable source")

    def test_failed_rerun_does_not_leave_stale_success(self):
        (self.root / ".groth16-workdir.json").write_text(
            '{"schema":"zkc.groth16-workdir/1"}'
        )
        (self.root / "RESULTS.json").write_text('{"status":"passed"}')
        arguments = ["reproduce.py", "validate", "--workdir", str(self.root)]
        with (
            patch.object(sys, "argv", arguments),
            patch.object(reproduce, "prepare_circomlib", return_value={}),
            patch.object(
                reproduce, "prepare_circom", side_effect=ValueError("wrong compiler")
            ),
        ):
            with self.assertRaisesRegex(ValueError, "wrong compiler"):
                reproduce.main()
        result = json.loads((self.root / "RESULTS.json").read_text())
        self.assertEqual(result["status"], "failed")
        self.assertIn("wrong compiler", result["error"])

    def test_wrong_circomlib_commit_refused(self):
        with patch.object(reproduce, "git_output", return_value="1" * 40):
            with self.assertRaisesRegex(ValueError, "not at pinned"):
                reproduce.check_checkout(self.root, {"commit": "0" * 40})

    def test_dirty_checkout_refused(self):
        commit = "1" * 40
        with patch.object(
            reproduce, "git_output", side_effect=[commit, " M poseidon.circom"]
        ):
            with self.assertRaisesRegex(ValueError, "must be clean"):
                reproduce.check_checkout(self.root, {"commit": commit})


if __name__ == "__main__":
    unittest.main()
