from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from checks import evaluation_lifecycle, run


class EvaluationLifecycleTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest = run.load_manifest()
        cls.catalog = evaluation_lifecycle.load_catalog()
        cls.report = evaluation_lifecycle.audit(cls.manifest, cls.catalog)

    def test_every_research_check_and_tracked_package_has_one_disposition(self) -> None:
        self.assertEqual("pass", self.report["outcome"], self.report["findings"])
        self.assertEqual([], self.report["findings"])
        self.assertEqual(47, self.report["summary"]["research_checks"])
        self.assertEqual(49, self.report["summary"]["packages"])

    def test_current_dispositions_make_no_bulk_retirement_claim(self) -> None:
        dispositions = self.report["summary"]["dispositions"]
        self.assertEqual(
            {
                "active-sequence": 25,
                "promote-then-retire": 10,
                "retain": 14,
            },
            dispositions,
        )

    def test_report_carries_review_metrics_not_only_labels(self) -> None:
        summary = self.report["summary"]
        self.assertGreater(summary["tracked_files"], 200)
        self.assertGreater(summary["tracked_lines"], 100_000)
        self.assertEqual(10, len(self.report["largest_packages"]))
        for package in self.report["packages"]:
            self.assertGreater(package["tracked_files"], 0, package["package"])
            self.assertGreater(package["tracked_bytes"], 0, package["package"])

    def test_duplicate_check_assignment_is_refused(self) -> None:
        duplicate = deepcopy(self.catalog)
        check_id = duplicate["groups"][0]["checks"][0]
        duplicate["groups"][1]["checks"].append(check_id)
        with tempfile.TemporaryDirectory() as raw_temp:
            path = Path(raw_temp) / "lifecycle.json"
            path.write_text(json.dumps(duplicate), encoding="utf-8")
            with self.assertRaisesRegex(
                evaluation_lifecycle.LifecycleError,
                "assigned more than once",
            ):
                evaluation_lifecycle.load_catalog(path)


if __name__ == "__main__":
    unittest.main()
