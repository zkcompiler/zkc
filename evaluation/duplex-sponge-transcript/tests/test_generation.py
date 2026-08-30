from __future__ import annotations

import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(PACKAGE_ROOT))

from generate import proof_from_generation_support  # noqa: E402
from duplexmodel.diagnostics import MalformedInput  # noqa: E402


CASES = PACKAGE_ROOT / "cases"


class GenerationTest(unittest.TestCase):
    def test_private_support_reconstructs_the_frozen_public_proof_bytes(self) -> None:
        private = json.loads((CASES / "private-generation.json").read_text())
        public = json.loads((CASES / "public-proof.json").read_text())
        self.assertEqual(proof_from_generation_support(private).to_term(), public)

    def test_support_policy_cannot_claim_uniformity_or_portability(self) -> None:
        private = json.loads((CASES / "private-generation.json").read_text())
        for key in ("uniformity_evidence", "portable_identity", "public_report_digest"):
            with self.subTest(key=key):
                changed = copy.deepcopy(private)
                changed["policy"][key] = True
                with self.assertRaisesRegex(MalformedInput, "policy differs"):
                    proof_from_generation_support(changed)

    def test_support_check_is_nonmutating_and_only_simulates_prefix(self) -> None:
        before = {
            path.name: path.read_bytes() for path in sorted(CASES.glob("*.json"))
        }
        result = subprocess.run(
            (
                sys.executable,
                str(PACKAGE_ROOT / "generate.py"),
                "--check-fixtures",
            ),
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        summary = json.loads(result.stdout)
        self.assertEqual(summary["simulated_prefix_challenges"], [[1, 0], 2])
        self.assertEqual(
            summary["simulated_challenge_occurrences"],
            ["challenge-1", "challenge-2"],
        )
        self.assertFalse(summary["final_verifier_squeeze_simulated"])
        self.assertEqual(
            summary["claim_boundaries"],
            {
                "entropy_uniformity": False,
                "portable_identity": False,
                "proof_generation": False,
                "prover_necessity": False,
            },
        )
        after = {
            path.name: path.read_bytes() for path in sorted(CASES.glob("*.json"))
        }
        self.assertEqual(after, before)
