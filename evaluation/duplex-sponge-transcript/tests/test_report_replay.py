from __future__ import annotations

from contextlib import contextmanager
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from typing import Iterator


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

from duplexmodel.provenance import source_manifest  # noqa: E402
from duplexmodel.report import (  # noqa: E402
    CONSTRUCTION_PATH,
    EXPECTED_PATH,
    PUBLIC_INPUT_PATH,
    PUBLIC_PROOF_PATH,
    SOURCE_LEDGER_PATH,
    build_report,
    expected_projection,
    verify_report,
)
from duplexmodel.terms import canonical_json_bytes, canonical_json_text  # noqa: E402


RUNNER_PATH = "evaluation/duplex-sponge-transcript/run.py"


@contextmanager
def copied_checkout() -> Iterator[tuple[Path, Path]]:
    with tempfile.TemporaryDirectory(prefix="duplex-public-replay-") as temporary:
        temporary_root = Path(temporary)
        copied_root = temporary_root / "checkout"
        isolated = temporary_root / "isolated"
        isolated.mkdir()
        paths = {
            CONSTRUCTION_PATH,
            PUBLIC_INPUT_PATH,
            PUBLIC_PROOF_PATH,
            SOURCE_LEDGER_PATH,
            EXPECTED_PATH,
            RUNNER_PATH,
            *(entry["path"] for entry in source_manifest(REPO_ROOT)),
        }
        for relative in sorted(paths):
            source = REPO_ROOT / relative
            destination = copied_root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        yield copied_root, isolated


def run_copied(
    copied_root: Path,
    isolated: Path,
    *,
    requested_root: Path | None = None,
    check_projection: bool = True,
) -> subprocess.CompletedProcess[str]:
    environment = {
        "PATH": os.environ.get("PATH", ""),
        "PYTHONPATH": "",
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    arguments = [
        sys.executable,
        "-S",
        "-B",
        str(copied_root / RUNNER_PATH),
        "--repo-root",
        str(copied_root if requested_root is None else requested_root),
    ]
    if check_projection:
        arguments.append("--check")
    return subprocess.run(
        arguments,
        cwd=isolated,
        env=environment,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )


class ReportReplayTest(unittest.TestCase):
    def test_build_strict_verify_and_canonical_round_trip(self) -> None:
        report = build_report(REPO_ROOT)
        self.assertEqual(verify_report(report, REPO_ROOT), [])
        encoded = canonical_json_bytes(report)
        self.assertEqual(json.loads(encoded), report)

    def test_frozen_expected_projection_matches_only_after_build(self) -> None:
        report = build_report(REPO_ROOT)
        expected = json.loads((REPO_ROOT / EXPECTED_PATH).read_text(encoding="utf-8"))
        self.assertEqual(expected, expected_projection(report))

    def test_copied_public_replay_succeeds_without_private_sidecar(self) -> None:
        with copied_checkout() as (copied_root, isolated):
            self.assertFalse(
                (
                    copied_root
                    / "evaluation/duplex-sponge-transcript/cases/private-generation.json"
                ).exists()
            )
            result = run_copied(copied_root, isolated)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                json.loads(result.stdout)["report_id"],
                build_report(REPO_ROOT)["report_id"],
            )

    def test_expected_oracle_mutation_is_detected_post_build(self) -> None:
        with copied_checkout() as (copied_root, isolated):
            path = copied_root / EXPECTED_PATH
            value = json.loads(path.read_text(encoding="utf-8"))
            value["execution_permutation_calls"] += 1
            path.write_text(canonical_json_text(value, pretty=True), encoding="utf-8")
            plain = run_copied(
                copied_root, isolated, check_projection=False
            )
            checked = run_copied(copied_root, isolated)
            self.assertEqual(plain.returncode, 0, plain.stderr)
            self.assertEqual(checked.returncode, 1)
            self.assertIn("expected projection differs", checked.stderr)

    def test_public_proof_mutation_changes_report_and_misses_frozen_projection(self) -> None:
        with copied_checkout() as (copied_root, isolated):
            path = copied_root / PUBLIC_PROOF_PATH
            value = json.loads(path.read_text(encoding="utf-8"))
            value["salt"] = [1, 4]
            path.write_text(canonical_json_text(value, pretty=True), encoding="utf-8")
            result = run_copied(copied_root, isolated)
            self.assertEqual(result.returncode, 1)
            self.assertIn("expected projection differs", result.stderr)

    def test_mixed_loaded_and_requested_roots_are_rejected(self) -> None:
        with copied_checkout() as (copied_root, isolated):
            result = run_copied(
                copied_root, isolated, requested_root=REPO_ROOT
            )
            self.assertEqual(result.returncode, 1)
            self.assertIn("differs from the loaded source root", result.stderr)
