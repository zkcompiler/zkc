"""Tests for the generated open-items index."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from checks import open_items


class RealTreeTest(unittest.TestCase):
    def test_real_tree_is_coherent_and_nonempty(self) -> None:
        report = open_items.build_report()
        blocking = [f for f in report["findings"] if f["blocking"]]
        self.assertEqual([], blocking, blocking)
        self.assertEqual("pass", report["outcome"])
        self.assertGreater(report["summary"]["cannot_answer_items"], 0)
        self.assertGreater(report["summary"]["reopening_records"], 0)
        rendered = open_items.render_markdown(report)
        self.assertIn("# Open items (generated)", rendered)
        self.assertIn("## Reopening records", rendered)


class SyntheticSourcesTest(unittest.TestCase):
    def _write(self, root: Path, package: str, payload: object) -> None:
        directory = root / package
        directory.mkdir(parents=True)
        (directory / open_items.FINDINGS_FILE).write_text(json.dumps(payload))

    def test_both_findings_shapes_are_read(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write(
                root,
                "pkg-a",
                {"finding_codes": [["one", "CannotAnswer", "A-C-ONE"], ["two", "Affirmative", "A-A-TWO"]]},
            )
            self._write(
                root,
                "pkg-b",
                {"findings": [{"name": "three", "outcome": "CannotAnswer", "code": "B-C-THREE"}]},
            )
            items = open_items.collect_cannot_answer(root)
        self.assertEqual(
            [("pkg-a", "A-C-ONE"), ("pkg-b", "B-C-THREE")],
            [(item["package"], item["code"]) for item in items],
        )

    def test_duplicate_and_malformed_codes_are_findings(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write(
                root,
                "pkg",
                {
                    "finding_codes": [
                        ["one", "CannotAnswer", "P-C-SAME"],
                        ["two", "CannotAnswer", "P-C-SAME"],
                        ["three", "CannotAnswer", "lowercase"],
                    ]
                },
            )
            items = open_items.collect_cannot_answer(root)
        findings = open_items.audit(items, [])
        self.assertEqual(
            {("malformed-code", True), ("duplicate-code", False)},
            {(f["kind"], f["blocking"]) for f in findings},
        )

    def test_malformed_json_is_an_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = root / "pkg"
            directory.mkdir()
            (directory / open_items.FINDINGS_FILE).write_text("{not json")
            with self.assertRaises(open_items.OpenItemsError):
                open_items.collect_cannot_answer(root)

    def test_gap_ledger_rows_are_read_and_malformed_rows_refuse(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp) / "gap-ledger.md"
            ledger.write_text(
                "# Gap Ledger\n\n| Specification | Current behaviour | Measured by | Closes with |\n"
                "|---|---|---|---|\n| spec/x.md 3 | refuses | `research.x` | change y |\n\nNo more.\n"
            )
            rows = open_items.collect_gap_ledger(ledger)
            self.assertEqual([("spec/x.md 3", "change y")], [(r["specification"], r["closes_with"]) for r in rows])
            ledger.write_text("| Specification | Current behaviour | Measured by | Closes with |\n|---|---|---|---|\n| a | b |\n")
            with self.assertRaises(open_items.OpenItemsError):
                open_items.collect_gap_ledger(ledger)

    def test_reopening_record_without_state_is_a_finding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            notes = Path(tmp)
            (notes / "x-reopening-2026-01-01.md").write_text("# Some record\n\nbody\n")
            (notes / "y-reopening-2026-01-02.md").write_text(
                "# Other record\n\n> **Kind:** k\n> **State:** Opened; pending\n> more\n> **Authority:** none\n"
            )
            records = open_items.collect_reopening_records(notes)
        self.assertEqual(["", "Opened; pending more"], [r["state"] for r in records])
        findings = open_items.audit([], records)
        self.assertEqual(["missing-state"], [f["kind"] for f in findings])


if __name__ == "__main__":
    unittest.main()
