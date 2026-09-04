from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

from checks import run


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "checks" / "manifest.json"


def _synthetic_manifest(execution: dict[str, object]) -> dict[str, object]:
    return {
        "schema_version": 1,
        "tiers": {
            "developer": {
                "title": "Developer feedback",
                "purpose": "Synthetic control-plane test tier.",
            }
        },
        "checks": [
            {
                "id": "synthetic.pass",
                "title": "Synthetic passing check",
                "subject": "The control-plane test fixture.",
                "claim": "The synthetic command produces its declared artifact.",
                "classification": "control-plane",
                "methods": ["unit"],
                "source_paths": ["checks/run.py"],
                "tiers": ["developer"],
                "cost": "instant",
                "environment": "python-stdlib",
                "shardability": "none",
                "blocking": True,
                "nonclaims": [
                    "The synthetic command carries no project semantic claim."
                ],
                "execution": execution,
            }
        ],
    }


class ManifestTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest = run.load_manifest(MANIFEST)

    def test_committed_manifest_is_strictly_valid(self) -> None:
        self.assertEqual(1, self.manifest.raw["schema_version"])
        self.assertGreaterEqual(len(self.manifest.checks), 30)
        self.assertEqual(
            len(self.manifest.checks),
            len({item["id"] for item in self.manifest.checks}),
        )

    def test_every_declared_source_exists_and_committed_sources_are_tracked(
        self,
    ) -> None:
        paths = sorted(
            {
                source
                for check in self.manifest.checks
                for source in check["source_paths"]
            }
        )
        for path in paths:
            self.assertTrue((ROOT / path).is_file(), path)
        completed = subprocess.run(
            ["git", "ls-files"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        tracked = set(completed.stdout.splitlines())
        for path in paths:
            if not path.startswith("checks/"):
                self.assertIn(path, tracked)

    def test_every_tracked_research_runner_is_inventoried(self) -> None:
        completed = subprocess.run(
            ["git", "ls-files", "evaluation"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        tracked_runners = {
            line
            for line in completed.stdout.splitlines()
            if re.fullmatch(r"evaluation/[^/]+/run\.py", line)
        }
        declared_arguments = {
            argument
            for check in self.manifest.checks
            if check["execution"]["kind"] == "command"
            for argument in check["execution"]["argv"]
        }
        self.assertSetEqual(tracked_runners, tracked_runners & declared_arguments)

    def test_cross_cutting_probes_and_diagnostics_are_inventoried(self) -> None:
        all_arguments = "\n".join(
            argument
            for check in self.manifest.checks
            if check["execution"]["kind"] == "command"
            for argument in check["execution"]["argv"]
        )
        for required in (
            "evaluation/r2-probe-commitment/tests",
            "evaluation/r2-probe-guard-cost/tests",
            "evaluation/r2-probe-logup/tests",
            "evaluation/r2-probe-value-bridges/tests",
            "evaluation/coverage.py",
            "evaluation/reachability.py",
        ):
            self.assertIn(required, all_arguments)

    def test_public_labels_do_not_use_work_package_codes(self) -> None:
        internal_code = re.compile(r"\b(?:K|R|F|P)\d+(?:[-A-Z0-9]*)?\b")
        for check in self.manifest.checks:
            self.assertIsNone(internal_code.search(check["id"]), check["id"])
            self.assertIsNone(internal_code.search(check["title"]), check["title"])

    def test_release_freeze_has_one_canonical_analysis_check(self) -> None:
        selected = run.select_checks(self.manifest, ("release-freeze",), ())
        analysis = [
            check for check in selected if check["id"] == "research.property-analysis"
        ]
        self.assertEqual(1, len(analysis))
        self.assertIn("--jobs", analysis[0]["execution"]["argv"])
        self.assertIn("1", analysis[0]["execution"]["argv"])

    def test_selector_preserves_manifest_order_and_unions_inputs(self) -> None:
        selected = run.select_checks(
            self.manifest,
            ("developer",),
            ("research.property-analysis",),
        )
        selected_ids = [check["id"] for check in selected]
        expected_ids = [
            check["id"]
            for check in self.manifest.checks
            if "developer" in check["tiers"]
            or check["id"] == "research.property-analysis"
        ]
        self.assertEqual(expected_ids, selected_ids)

    def test_duplicate_json_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as raw_temp:
            path = Path(raw_temp) / "manifest.json"
            path.write_text(
                '{"schema_version": 1, "schema_version": 1}\n', encoding="utf-8"
            )
            with self.assertRaisesRegex(run.ManifestError, "duplicate JSON key"):
                run.load_manifest(path)

    def test_unknown_command_placeholder_is_rejected(self) -> None:
        manifest = _synthetic_manifest(
            {
                "kind": "command",
                "argv": ["{python}", "-c", "print('{unknown}')"],
                "cwd": "{repo}",
                "requires": ["{python}"],
                "artifacts": [],
            }
        )
        with tempfile.TemporaryDirectory() as raw_temp:
            path = Path(raw_temp) / "manifest.json"
            path.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaisesRegex(run.ManifestError, "unknown placeholders"):
                run.load_manifest(path)


class RunnerTests(unittest.TestCase):
    def test_command_result_records_provenance_logs_and_declared_artifact(self) -> None:
        execution = {
            "kind": "command",
            "argv": [
                "{python}",
                "-c",
                "from pathlib import Path; Path(r'{artifacts}/proof.txt').write_text('ok', encoding='utf-8')",
            ],
            "cwd": "{repo}",
            "requires": ["{python}"],
            "artifacts": ["proof.txt"],
        }
        manifest = _synthetic_manifest(execution)
        with tempfile.TemporaryDirectory() as raw_temp:
            temp = Path(raw_temp)
            manifest_path = temp / "manifest.json"
            artifacts = temp / "artifacts"
            result_path = temp / "result.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            completed = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(ROOT / "checks" / "run.py"),
                    "--manifest",
                    str(manifest_path),
                    "run",
                    "--check",
                    "synthetic.pass",
                    "--artifacts-dir",
                    str(artifacts),
                    "--result",
                    str(result_path),
                ],
                cwd=ROOT,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(0, completed.returncode, completed.stderr)
            report = json.loads(result_path.read_text(encoding="utf-8"))
            self.assertEqual("passed", report["outcome"])
            self.assertEqual("pass", report["results"][0]["status"])
            self.assertIn(report["provenance"]["worktree"], {"clean", "dirty"})
            self.assertTrue(Path(report["results"][0]["stdout_log"]).is_file())
            self.assertTrue((artifacts / "synthetic-pass" / "proof.txt").is_file())

    def test_external_workflow_is_incomplete_not_passed(self) -> None:
        with tempfile.TemporaryDirectory() as raw_temp:
            result_path = Path(raw_temp) / "result.json"
            completed = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(ROOT / "checks" / "run.py"),
                    "run",
                    "--check",
                    "formal.receipt-reading",
                    "--result",
                    str(result_path),
                    "--artifacts-dir",
                    str(Path(raw_temp) / "artifacts"),
                ],
                cwd=ROOT,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(2, completed.returncode, completed.stderr)
            report = json.loads(result_path.read_text(encoding="utf-8"))
            self.assertEqual("incomplete", report["outcome"])
            self.assertEqual("external", report["results"][0]["status"])


if __name__ == "__main__":
    unittest.main()
