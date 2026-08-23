from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = MODEL_ROOT.parents[1]
sys.path.insert(0, str(MODEL_ROOT))

import r2model.report as report_module
from r2model.report import (
    EXECUTION_ROLES,
    MAX_REPORT_CASES,
    MAX_REPORT_OPERANDS,
    RELATION_NAMES,
    REPORT_SOURCE_PATHS,
    SCHEMA,
    build_report,
    verify_report,
)
from r2model.terms import semantic_id
import run as runner


REPORT_KEYS = {
    "schema",
    "semantic_regime_id",
    "replay_basis",
    "semantic_roots",
    "executions",
    "relations",
    "cases",
    "evidence",
    "scope",
    "root_ids",
    "report_id",
}

CASE_KEYS = {
    "outcome",
    "boundary",
    "code",
    "subject_id",
    "evidence_id",
}

EXPECTED_KEYS = {
    "schema",
    "semantic_regime_id",
    "replay_basis",
    "semantic_roots",
    "executions",
    "relations",
    "cases",
    "root_ids",
    "report_id",
}


class ReportV3Test(unittest.TestCase):
    """Identity-graph and exact-replay checks for the compact v3 report."""

    @classmethod
    def setUpClass(cls) -> None:
        # Building the finite witness dominates this suite. Keep one canonical
        # object and make malformed reports fail before the replay step.
        cls.report = build_report(REPO_ROOT)

    def assert_structural_error(self, report: object, fragment: str) -> None:
        """Assert rejection without allowing a malformed term to escape."""

        try:
            errors = verify_report(report, REPO_ROOT)
        except Exception as error:  # pragma: no cover - this is the property
            self.fail(f"malformed report raised {type(error).__name__}: {error}")
        self.assertTrue(errors)
        self.assertTrue(
            any(fragment in error for error in errors),
            f"expected {fragment!r} in {errors!r}",
        )

    def test_canonical_build_has_exact_v3_envelope_and_replays(self) -> None:
        self.assertEqual(set(self.report), REPORT_KEYS)
        self.assertEqual(self.report["schema"], SCHEMA)
        self.assertEqual(SCHEMA, "zkc.r2.protocol-model-report.v3")
        self.assertEqual(tuple(self.report["executions"]), EXECUTION_ROLES)
        self.assertEqual(
            tuple(self.report["relations"]["definitions"]),
            RELATION_NAMES,
        )
        self.assertEqual(tuple(self.report["relations"]["runs"]), RELATION_NAMES)
        self.assertEqual(len(self.report["cases"]), 41)
        self.assertEqual(len(self.report["evidence"]), 41)
        self.assertTrue(
            all(set(case) == CASE_KEYS for case in self.report["cases"].values())
        )

        # This is the suite's one real exact canonical replay. Other tests
        # either fail structurally or inject the already-built canonical graph.
        self.assertEqual(verify_report(self.report, REPO_ROOT), [])

    def test_expected_projection_has_exact_v4_identity_graph_shape(self) -> None:
        projection = runner.expected_projection(self.report)
        self.assertEqual(set(projection), EXPECTED_KEYS)
        self.assertEqual(projection["schema"], "zkc.r2.expected-results.v4")
        self.assertEqual(projection["semantic_regime_id"], self.report["semantic_regime_id"])
        self.assertEqual(projection["replay_basis"], self.report["replay_basis"])
        self.assertEqual(projection["semantic_roots"], self.report["semantic_roots"])
        self.assertEqual(projection["root_ids"], self.report["root_ids"])
        self.assertEqual(projection["report_id"], self.report["report_id"])

        self.assertEqual(tuple(projection["executions"]), EXECUTION_ROLES)
        for role in EXECUTION_ROLES:
            self.assertEqual(
                set(projection["executions"][role]),
                {"manifest_id", "request_id", "record_id", "qualification_id"},
            )
        self.assertEqual(tuple(projection["relations"]), RELATION_NAMES)
        for name in RELATION_NAMES:
            self.assertEqual(
                set(projection["relations"][name]),
                {
                    "shape_id",
                    "validation_profile_id",
                    "run_evidence_id",
                    "hybrid_factorization_id",
                },
            )
        self.assertEqual(len(projection["cases"]), 41)
        self.assertTrue(
            all(set(case) == CASE_KEYS for case in projection["cases"].values())
        )
        self.assertNotIn("evidence", projection)
        self.assertNotIn("scope", projection)

    def test_relation_runs_exclude_the_external_fresh_support_point(self) -> None:
        external_qualification_id = self.report["executions"][
            "external_fresh_support_point"
        ]["qualification_id"]
        expected_fresh_roles = {
            "shared": "coupled_fresh_grinding",
            "distinct": "coupled_fresh_no_grinding",
        }
        for relation_name, execution_role in expected_fresh_roles.items():
            with self.subTest(relation=relation_name):
                term = self.report["relations"]["runs"][relation_name][
                    "run_evidence"
                ]["term"]
                self.assertEqual(
                    term["fresh_qualification_id"],
                    self.report["executions"][execution_role]["qualification_id"],
                )
                self.assertNotIn(
                    external_qualification_id,
                    json.dumps(term, sort_keys=True),
                )

    def test_fully_readdressed_case_tamper_fails_exact_canonical_replay(self) -> None:
        tampered = deepcopy(self.report)
        case_name = "base/fs-admission.v1"
        case = tampered["cases"][case_name]
        old_evidence_id = case["evidence_id"]
        body = tampered["evidence"].pop(old_evidence_id)

        # Change a semantic classification, then consistently recompute every
        # report identity that commits to it. Local hash consistency therefore
        # cannot be the reason for rejection.
        body["classification"]["code"] = "R2-TEST-RECLASSIFIED"
        case["code"] = body["classification"]["code"]
        new_evidence_id = semantic_id("r2.report-case-evidence.v1", body)
        case["evidence_id"] = new_evidence_id
        tampered["evidence"][new_evidence_id] = body
        tampered["root_ids"]["case_index_id"] = semantic_id(
            "r2.report-case-index.v3",
            {
                name: tampered["cases"][name]["evidence_id"]
                for name in sorted(tampered["cases"])
            },
        )
        tampered["report_id"] = semantic_id(
            "r2.protocol-model-report.v3",
            {
                "schema": tampered["schema"],
                "semantic_regime_id": tampered["semantic_regime_id"],
                "root_ids": tampered["root_ids"],
            },
        )

        # Avoid a second expensive execution of build_report while still
        # exercising verify_report's final exact-replay comparison.
        with mock.patch.object(
            report_module,
            "build_report",
            return_value=self.report,
        ):
            errors = verify_report(tampered, REPO_ROOT)
        self.assertEqual(errors, ["report differs from canonical replay"])

    def test_missing_orphan_and_duplicate_evidence_are_rejected(self) -> None:
        names = list(self.report["cases"])
        first_name, second_name = names[:2]
        first_id = self.report["cases"][first_name]["evidence_id"]
        second_id = self.report["cases"][second_name]["evidence_id"]

        missing = deepcopy(self.report)
        del missing["evidence"][first_id]
        self.assert_structural_error(missing, "case or evidence aggregate bound differs")

        orphan = deepcopy(self.report)
        orphan_body = orphan["evidence"].pop(first_id)
        orphan_body["law"] = "r2.test-orphan-evidence.v1"
        orphan_id = semantic_id("r2.report-case-evidence.v1", orphan_body)
        orphan["evidence"][orphan_id] = orphan_body
        self.assert_structural_error(orphan, "missing or orphaned entry")

        duplicate = deepcopy(self.report)
        duplicate["cases"][second_name]["evidence_id"] = first_id
        self.assertNotEqual(first_id, second_id)
        self.assert_structural_error(duplicate, "case evidence is not one-to-one")

    def test_malformed_id_and_aggregate_bounds_are_rejected(self) -> None:
        malformed = deepcopy(self.report)
        first_case = next(iter(malformed["cases"].values()))
        first_case["subject_id"] = "not-a-content-id"
        self.assert_structural_error(malformed, "case vocabulary differs")

        too_many_cases = deepcopy(self.report)
        template = deepcopy(next(iter(too_many_cases["cases"].values())))
        for index in range(MAX_REPORT_CASES - len(too_many_cases["cases"]) + 1):
            too_many_cases["cases"][f"test/over-bound-{index}.v1"] = deepcopy(
                template
            )
        self.assertGreater(len(too_many_cases["cases"]), MAX_REPORT_CASES)
        self.assert_structural_error(
            too_many_cases,
            "case or evidence aggregate bound differs",
        )

        too_many_operands = deepcopy(self.report)
        case = next(iter(too_many_operands["cases"].values()))
        body = too_many_operands["evidence"][case["evidence_id"]]
        exemplar_id = case["subject_id"]
        body["operand_ids"] = {
            f"operand-{index}": exemplar_id
            for index in range(MAX_REPORT_OPERANDS + 1)
        }
        self.assert_structural_error(too_many_operands, "evidence body differs")

    def test_replay_basis_rejects_path_and_digest_drift(self) -> None:
        path_drift = deepcopy(self.report)
        path_drift["replay_basis"]["source_digests"][0]["path"] = (
            "evaluation/r2-protocol-model/r2model/not-relations.py"
        )
        self.assertNotEqual(
            tuple(item["path"] for item in path_drift["replay_basis"]["source_digests"]),
            REPORT_SOURCE_PATHS,
        )
        self.assert_structural_error(path_drift, "source set")

        digest_drift = deepcopy(self.report)
        digest_drift["replay_basis"]["source_digests"][0]["sha256"] = "0" * 64
        self.assert_structural_error(digest_drift, "digest differs")

    def test_alternate_repo_root_cannot_name_the_loaded_evaluator(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            alternate_root = Path(directory)
            with self.assertRaisesRegex(
                ValueError,
                "repository root differs from the checkout that loaded the evaluator",
            ):
                build_report(alternate_root)
            self.assertEqual(
                verify_report(self.report, alternate_root),
                [
                    "repository root differs from the checkout that loaded "
                    "the evaluator"
                ],
            )

    def test_malformed_nested_terms_return_errors_without_raising(self) -> None:
        malformed_profile = deepcopy(self.report)
        malformed_profile["relations"]["definitions"]["shared"][
            "validation_profile"
        ]["term"] = ["not", "a", "profile", "term"]
        self.assert_structural_error(
            malformed_profile,
            "relation definition vocabulary differs",
        )

        malformed_run = deepcopy(self.report)
        malformed_run["relations"]["runs"]["shared"]["run_evidence"][
            "term"
        ] = {"unexpected": "shape"}
        self.assert_structural_error(
            malformed_run,
            "relation run evidence shape differs",
        )

        malformed_evidence = deepcopy(self.report)
        case = next(iter(malformed_evidence["cases"].values()))
        malformed_evidence["evidence"][case["evidence_id"]]["operand_ids"] = [
            "not",
            "an",
            "operand-map",
        ]
        self.assert_structural_error(malformed_evidence, "evidence body differs")

    def test_runner_json_loader_rejects_duplicate_keys(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_text(
                json.dumps({"schema": "first"})[:-1]
                + ', "schema": "second"}',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "duplicate JSON key: schema"):
                runner._load(path)


if __name__ == "__main__":
    unittest.main()
