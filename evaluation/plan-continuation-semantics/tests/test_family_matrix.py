from __future__ import annotations

from dataclasses import replace
import json
from pathlib import Path
import sys
from types import MappingProxyType
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import fixtures  # noqa: E402
import reference_model as m  # noqa: E402


class FamilyMatrixTests(unittest.TestCase):
    def test_public_and_private_fixture_files_are_role_separated(self) -> None:
        public = json.loads((ROOT / "cases" / "public-inputs.json").read_text(encoding="utf-8"))
        private = json.loads((ROOT / "cases" / "private-generation.json").read_text(encoding="utf-8"))
        for key in ("nova", "hypernova", "cyclefold", "protostar", "latticefold_plus"):
            with self.subTest(case=key):
                self.assertEqual(set(public[key]), {"statement", "session", "fresh"})
                self.assertIn("private", private[key])
                self.assertNotIn("private", public[key])
                self.assertNotIn("statement", private[key])

    def test_declared_matrix_matches_executable_results(self) -> None:
        declared = json.loads((ROOT / "cases" / "family-shapes.json").read_text(encoding="utf-8"))
        cases = fixtures.family_cases()
        for case, row in zip(cases, declared["families"], strict=True):
            with self.subTest(case=case.name):
                generated, completed = m.execute_case(case)
                self.assertEqual(row["name"], case.name)
                self.assertEqual(row["depth"], case.evidence_depth)
                self.assertEqual(tuple(row["arm"]), tuple(completed.outputs))
                self.assertEqual(row["source_requirement"], case.expected_requirement.value)
                self.assertIs(generated.record.entries[-1].value, True)

    def test_source_ledger_is_inert_and_complete_for_selected_families(self) -> None:
        loaded: list[str] = []
        original_load = fixtures._load

        def observed_load(name: str) -> object:
            loaded.append(name)
            return original_load(name)

        with patch.object(fixtures, "_load", side_effect=observed_load):
            cases = fixtures.family_cases()
        self.assertEqual(
            loaded,
            [
                "family-shapes.json",
                "private-generation.json",
                "public-inputs.json",
            ],
        )
        self.assertNotIn("source-ledger.json", loaded)
        ledger = json.loads((ROOT / "cases" / "source-ledger.json").read_text(encoding="utf-8"))
        names = {item["case"] for item in ledger["sources"]}
        self.assertEqual(names, {case.name for case in cases})
        for item in ledger["sources"]:
            digest = bytes.fromhex(item["pdf_sha256"])
            self.assertEqual(len(digest), 32)

    def test_case_output_values_are_not_semantic_identity(self) -> None:
        case = fixtures.family_cases()[0]
        changed_private = dict(case.private_values)
        changed_private["w1"] += 100
        changed_case = replace(
            case,
            private_values=MappingProxyType(changed_private),
        )
        _, baseline = m.execute_case(case)
        _, changed = m.execute_case(changed_case)
        baseline_oir = m.derive_endpoint_graph(
            case.core, case.plan, m.EndpointPurpose.PLAN_CONTINUATION
        )
        changed_oir = m.derive_endpoint_graph(
            changed_case.core,
            changed_case.plan,
            m.EndpointPurpose.PLAN_CONTINUATION,
        )
        self.assertNotEqual(
            baseline.outputs["folded"].value,
            changed.outputs["folded"].value,
        )
        self.assertEqual(case.plan.identity, changed_case.plan.identity)
        self.assertEqual(baseline_oir.identity, changed_oir.identity)


if __name__ == "__main__":
    unittest.main()
