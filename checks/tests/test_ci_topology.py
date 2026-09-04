from __future__ import annotations

from pathlib import Path
import re
import unittest

from checks import run


ROOT = Path(__file__).resolve().parents[2]
CI = ROOT / ".github" / "workflows" / "ci.yml"


class ContinuousIntegrationTopologyTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = CI.read_text(encoding="utf-8")
        cls.manifest = run.load_manifest()

    def test_workflow_invokes_exactly_the_pull_request_check_ids(self) -> None:
        expected = {
            check["id"] for check in self.manifest.checks if "pr" in check["tiers"]
        }
        invoked = set(re.findall(r"--check\s+([a-z][a-z0-9.-]+)", self.text))
        self.assertSetEqual(expected, invoked)

    def test_expensive_jobs_depend_on_the_source_only_control(self) -> None:
        self.assertEqual(2, self.text.count("needs: public-tree"))
        self.assertNotIn("research.property-analysis", self.text)
        self.assertNotIn("--tier release-freeze", self.text)

    def test_workflow_does_not_duplicate_underlying_gate_commands(self) -> None:
        for command in (
            "tools/public-tree-guard.sh",
            "cmake --build --preset ci --target check-zkc",
            "uvx ruff check .",
            "cargo test --locked",
            "cargo clippy --locked",
            "python -m oracle.model",
        ):
            with self.subTest(command=command):
                self.assertNotIn(command, self.text)

    def test_each_lane_retains_nonhidden_structured_results(self) -> None:
        self.assertEqual(3, self.text.count("uses: actions/upload-artifact@v7"))
        self.assertEqual(3, self.text.count("retention-days: 14"))
        self.assertNotIn("include-hidden-files:", self.text)


if __name__ == "__main__":
    unittest.main()
