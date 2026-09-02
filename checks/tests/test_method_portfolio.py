from __future__ import annotations

from pathlib import Path
import unittest

from checks import method_portfolio, run


ROOT = Path(__file__).resolve().parents[2]


class MethodPortfolioTest(unittest.TestCase):
    def test_method_and_classification_vocabularies_are_total(self) -> None:
        self.assertSetEqual(set(run.METHODS), set(method_portfolio.METHOD_LENSES))
        self.assertSetEqual(
            set(run.CLASSIFICATIONS),
            set(method_portfolio.CLASSIFICATION_FLOORS),
        )

    def test_committed_portfolio_meets_its_declared_floors(self) -> None:
        report = method_portfolio.audit(run.load_manifest())
        self.assertEqual("pass", report["outcome"], report["findings"])
        self.assertEqual([], report["findings"])

    def test_one_method_implementation_gate_is_refused(self) -> None:
        raw = {
            "schema_version": 1,
            "tiers": {
                "pr": {"title": "PR", "purpose": "Synthetic test tier."}
            },
            "checks": [
                {
                    "id": "synthetic.one-method",
                    "title": "Synthetic one-method check",
                    "subject": "A synthetic implementation surface.",
                    "claim": "One example passes.",
                    "classification": "implementation-regression",
                    "methods": ["unit"],
                    "source_paths": ["checks/run.py"],
                    "tiers": ["pr"],
                    "cost": "instant",
                    "environment": "python-stdlib",
                    "shardability": "none",
                    "blocking": True,
                    "nonclaims": ["This synthetic check carries no project claim."],
                    "execution": {
                        "kind": "command",
                        "argv": ["{python}", "-c", "print('ok')"],
                        "cwd": "{repo}",
                        "requires": ["{python}"],
                        "artifacts": [],
                    },
                }
            ],
        }
        manifest = run.Manifest(raw=raw, digest="synthetic", path=ROOT / "synthetic")
        report = method_portfolio.audit(manifest)
        self.assertEqual("fail", report["outcome"])
        self.assertEqual("insufficient-method-diversity", report["findings"][0]["kind"])
        self.assertEqual(
            [["adversarial"]],
            report["findings"][0]["missing_lens_alternatives"],
        )


if __name__ == "__main__":
    unittest.main()
